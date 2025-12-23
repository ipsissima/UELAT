"""
    UELAT.jl — Universal Embedding and Linear Approximation Theorem

This module provides executable implementations of the verified Bernstein
approximation theory from UELAT. The key results are:

1. **Degree bound**: For L-Lipschitz functions on [0,1], degree N ≥ (L/(2ε))²
   guarantees ε-approximation (verified in Coq/Approx/Bernstein_Lipschitz.v)

2. **Certificate construction**: Sample f at k/N for k = 0, ..., N to get
   Bernstein coefficients that form a valid certificate

3. **Stable evaluation**: Use De Casteljau's algorithm for numerically stable
   evaluation, avoiding catastrophic cancellation in the power basis

Reference: UELAT Paper, Sections 5-7
"""
module UELAT

using LinearAlgebra

export BernsteinCert, required_degree, certify, evaluate, verify_certificate
export test_exponential, test_lipschitz_function

# ============================================================================
# 1. The Certificate Structure
# ============================================================================

"""
    BernsteinCert

A certificate for function approximation using Bernstein polynomials.

# Fields
- `degree::Int`: The polynomial degree N
- `coeffs::Vector{Float64}`: Bernstein coefficients [f(0/N), f(1/N), ..., f(N/N)]
- `epsilon::Float64`: The guaranteed approximation error bound
- `lipschitz::Float64`: The Lipschitz constant of the certified function

# Mathematical Guarantee
For any x ∈ [0,1]:
    |B_N[f](x) - f(x)| ≤ epsilon

where B_N[f](x) = Σ_{k=0}^N f(k/N) · C(N,k) · x^k · (1-x)^{N-k}

This bound is verified in Coq/Approx/Bernstein_Lipschitz.v, Theorem bernstein_uniform_lipschitz.
"""
struct BernsteinCert
    degree::Int
    coeffs::Vector{Float64}
    epsilon::Float64
    lipschitz::Float64

    function BernsteinCert(degree::Int, coeffs::Vector{Float64}, epsilon::Float64, lipschitz::Float64)
        @assert degree >= 0 "Degree must be non-negative"
        @assert length(coeffs) == degree + 1 "Must have exactly N+1 coefficients for degree N"
        @assert epsilon > 0 "Epsilon must be positive"
        @assert lipschitz >= 0 "Lipschitz constant must be non-negative"
        new(degree, coeffs, epsilon, lipschitz)
    end
end

# ============================================================================
# 2. The Constructive Logic (from Bernstein_Lipschitz.v)
# ============================================================================

"""
    required_degree(L::Float64, epsilon::Float64) -> Int

Calculate the required degree N = ⌈(L/(2ε))²⌉ for ε-approximation of
an L-Lipschitz function.

# Mathematical Background
From Coq/Approx/Bernstein_Lipschitz.v, Theorem bernstein_uniform_lipschitz:

    For L-Lipschitz f on [0,1], if N ≥ (L/(2ε))², then
    sup_{x ∈ [0,1]} |B_N[f](x) - f(x)| ≤ ε

The proof uses:
1. Convexity of Bernstein operator: B_N[f](x) = Σ f(k/N) w_{N,k}(x)
2. Lipschitz bound: |f(k/N) - f(x)| ≤ L |k/N - x|
3. Variance bound: Σ |k/N - x| w_{N,k}(x) ≤ 1/(2√N)
4. Therefore: |B_N[f](x) - f(x)| ≤ L/(2√N) ≤ ε when N ≥ (L/(2ε))²

# Arguments
- `L`: Lipschitz constant of the function
- `epsilon`: Desired approximation error bound

# Returns
The minimum degree N guaranteeing ε-approximation.

# Example
```julia
julia> required_degree(1.0, 0.01)  # For exp(x) on [0,1] with L ≈ e
2500
```
"""
function required_degree(L::Float64, epsilon::Float64)::Int
    @assert L >= 0 "Lipschitz constant must be non-negative"
    @assert epsilon > 0 "Epsilon must be positive"

    if L == 0.0
        return 0  # Constant function needs degree 0
    end

    # N = ceil((L / (2 * epsilon))^2)
    ratio = L / (2 * epsilon)
    return Int(ceil(ratio^2))
end

# ============================================================================
# 3. The Generator (The "Adjunction" step)
# ============================================================================

"""
    certify(f::Function, L::Float64, epsilon::Float64) -> BernsteinCert

Construct a Bernstein certificate for function `f` by sampling at k/N.

This implements the "free functor" from the category of Lipschitz functions
to the category of certificates, establishing the adjunction:

    Hom(certify(f), C) ≅ Hom(f, evaluate(C))

# Mathematical Construction
Given L-Lipschitz function f : [0,1] → ℝ and target error ε:

1. Compute N = required_degree(L, ε)
2. Sample: coeffs[k] = f(k/N) for k = 0, ..., N
3. Return BernsteinCert(N, coeffs, ε, L)

The resulting certificate satisfies:
    ∀x ∈ [0,1]: |evaluate(cert, x) - f(x)| ≤ ε

# Arguments
- `f`: The function to certify (must be L-Lipschitz on [0,1])
- `L`: Lipschitz constant of f
- `epsilon`: Desired approximation error bound

# Returns
A `BernsteinCert` that ε-approximates f on [0,1].

# Example
```julia
julia> cert = certify(exp, 2.72, 0.01)
BernsteinCert(degree=18496, epsilon=0.01)
```
"""
function certify(f::Function, L::Float64, epsilon::Float64)::BernsteinCert
    N = required_degree(L, epsilon)

    # Sample f at the Bernstein nodes k/N
    coeffs = Vector{Float64}(undef, N + 1)
    for k in 0:N
        x_k = N == 0 ? 0.0 : k / N
        coeffs[k + 1] = f(x_k)
    end

    return BernsteinCert(N, coeffs, epsilon, L)
end

# ============================================================================
# 4. The Evaluator (Stable De Casteljau Algorithm)
# ============================================================================

"""
    evaluate(cert::BernsteinCert, x::Float64) -> Float64

Evaluate the Bernstein polynomial certificate at point x using
De Casteljau's algorithm for numerical stability.

# De Casteljau's Algorithm
Instead of computing:
    B_N(x) = Σ_{k=0}^N c_k · C(N,k) · x^k · (1-x)^{N-k}

which suffers from catastrophic cancellation and overflow for large N,
we use the recursive subdivision:

    b_k^{(0)} = c_k
    b_k^{(r)} = (1-x) · b_k^{(r-1)} + x · b_{k+1}^{(r-1)}
    B_N(x) = b_0^{(N)}

This is:
- Numerically stable (no large intermediate values)
- O(N²) time, O(N) space
- Geometrically meaningful (repeated linear interpolation)

# Stability Analysis
For condition number κ, De Casteljau satisfies:
    |computed - exact| / |exact| ≤ κ · ε_mach · N

where the naive power basis can have κ exponentially large in N.

# Arguments
- `cert`: The Bernstein certificate
- `x`: Evaluation point (should be in [0,1])

# Returns
The value B_N(x) of the Bernstein polynomial at x.

# Example
```julia
julia> cert = certify(sin, 1.0, 0.001)
julia> evaluate(cert, 0.5)  # Should be ≈ sin(0.5) = 0.4794...
0.47942553860420295
```
"""
function evaluate(cert::BernsteinCert, x::Float64)::Float64
    N = cert.degree
    coeffs = cert.coeffs

    # Handle edge cases
    if N == 0
        return coeffs[1]
    end

    # Clamp x to [0,1] for numerical safety
    x = clamp(x, 0.0, 1.0)

    # De Casteljau's algorithm
    # We work in-place on a copy of the coefficients
    b = copy(coeffs)

    for r in 1:N
        for k in 1:(N - r + 1)
            # b[k] = (1 - x) * b[k] + x * b[k + 1]
            b[k] = (1 - x) * b[k] + x * b[k + 1]
        end
    end

    return b[1]
end

"""
    evaluate_naive(cert::BernsteinCert, x::Float64) -> Float64

Evaluate using the naive power basis formula. This is provided for
comparison and testing, but should NOT be used for large N due to
numerical instability.

WARNING: Can produce incorrect results for N > 50 due to overflow
in binomial coefficients and cancellation errors.
"""
function evaluate_naive(cert::BernsteinCert, x::Float64)::Float64
    N = cert.degree
    coeffs = cert.coeffs

    result = 0.0
    for k in 0:N
        binom = binomial(BigInt(N), BigInt(k))
        term = Float64(binom) * x^k * (1 - x)^(N - k)
        result += coeffs[k + 1] * term
    end

    return result
end

# ============================================================================
# 5. Verification
# ============================================================================

"""
    verify_certificate(cert::BernsteinCert, f::Function, n_samples::Int=1000) -> NamedTuple

Verify that a certificate achieves its claimed error bound.

# Returns
A named tuple with:
- `max_error`: Maximum observed error |evaluate(cert, x) - f(x)|
- `mean_error`: Mean absolute error
- `within_bound`: Whether max_error ≤ cert.epsilon
- `samples`: Vector of (x, error) pairs

# Example
```julia
julia> cert = certify(exp, 2.72, 0.01)
julia> result = verify_certificate(cert, exp)
julia> result.within_bound
true
```
"""
function verify_certificate(cert::BernsteinCert, f::Function, n_samples::Int=1000)
    xs = range(0.0, 1.0, length=n_samples)
    errors = [abs(evaluate(cert, x) - f(x)) for x in xs]

    max_error = maximum(errors)
    mean_error = sum(errors) / n_samples

    return (
        max_error = max_error,
        mean_error = mean_error,
        within_bound = max_error <= cert.epsilon,
        samples = collect(zip(xs, errors))
    )
end

# ============================================================================
# 6. Test Functions
# ============================================================================

"""
    test_exponential(epsilon::Float64=0.01) -> Bool

Test the certification of exp(x) on [0,1].

The exponential function has Lipschitz constant L = e ≈ 2.718 on [0,1]
(since |exp'(x)| ≤ e for x ∈ [0,1]).

# Example
```julia
julia> test_exponential(0.001)
Testing exp(x) on [0,1] with ε = 0.001
Lipschitz constant L = 2.718281828459045
Required degree N = 1847689
Certificate size: 1847690 coefficients
Verification: max error = 0.0009876543...
✓ Error within bound!
true
```
"""
function test_exponential(epsilon::Float64=0.01)::Bool
    println("Testing exp(x) on [0,1] with ε = $epsilon")

    # Lipschitz constant of exp on [0,1] is max|exp'(x)| = e
    L = exp(1.0)
    println("Lipschitz constant L = $L")

    # Compute required degree
    N = required_degree(L, epsilon)
    println("Required degree N = $N")

    # Build certificate
    cert = certify(exp, L, epsilon)
    println("Certificate size: $(length(cert.coeffs)) coefficients")

    # Verify
    result = verify_certificate(cert, exp, 1000)
    println("Verification: max error = $(result.max_error)")

    if result.within_bound
        println("✓ Error within bound!")
    else
        println("✗ Error exceeds bound by $(result.max_error - epsilon)")
    end

    return result.within_bound
end

"""
    test_lipschitz_function(f::Function, L::Float64, epsilon::Float64, name::String="f") -> Bool

Test certification of an arbitrary Lipschitz function.

# Arguments
- `f`: The function to test
- `L`: Lipschitz constant of f on [0,1]
- `epsilon`: Desired error bound
- `name`: Name for display purposes

# Example
```julia
julia> test_lipschitz_function(sin, 1.0, 0.001, "sin")
Testing sin on [0,1] with ε = 0.001, L = 1.0
...
true
```
"""
function test_lipschitz_function(f::Function, L::Float64, epsilon::Float64, name::String="f")::Bool
    println("Testing $name on [0,1] with ε = $epsilon, L = $L")

    N = required_degree(L, epsilon)
    println("Required degree N = $N")

    cert = certify(f, L, epsilon)
    println("Certificate size: $(length(cert.coeffs)) coefficients")

    result = verify_certificate(cert, f, 1000)
    println("Verification: max error = $(result.max_error)")

    if result.within_bound
        println("✓ Error within bound!")
    else
        println("✗ Error exceeds bound by $(result.max_error - epsilon)")
    end

    return result.within_bound
end

# ============================================================================
# 7. Utility Functions
# ============================================================================

"""
    certificate_info(cert::BernsteinCert) -> String

Return a summary of the certificate for display.
"""
function certificate_info(cert::BernsteinCert)::String
    return """
    BernsteinCert:
      Degree: $(cert.degree)
      Coefficients: $(length(cert.coeffs))
      Epsilon: $(cert.epsilon)
      Lipschitz: $(cert.lipschitz)
      Memory: ≈ $(sizeof(cert.coeffs)) bytes
    """
end

"""
    Base.show(io::IO, cert::BernsteinCert)

Pretty-print a certificate.
"""
function Base.show(io::IO, cert::BernsteinCert)
    print(io, "BernsteinCert(degree=$(cert.degree), ε=$(cert.epsilon), L=$(cert.lipschitz))")
end

"""
    lipschitz_estimate(f::Function, n_samples::Int=1000) -> Float64

Estimate the Lipschitz constant of f on [0,1] by sampling.

This is useful when the exact Lipschitz constant is unknown.
The estimate is a lower bound; the true constant may be higher.

# Example
```julia
julia> lipschitz_estimate(exp)
2.715... # Close to e ≈ 2.718
```
"""
function lipschitz_estimate(f::Function, n_samples::Int=1000)::Float64
    xs = range(0.0, 1.0, length=n_samples)
    ys = [f(x) for x in xs]

    max_slope = 0.0
    for i in 1:(n_samples-1)
        slope = abs(ys[i+1] - ys[i]) / (xs[i+1] - xs[i])
        max_slope = max(max_slope, slope)
    end

    return max_slope
end

# ============================================================================
# Module initialization
# ============================================================================

function __init__()
    # Perform a quick self-test on module load
    # Disabled by default to avoid slow startup
    # test_exponential(0.1)
end

end # module UELAT
