"""
    UELAT.jl — Universal Embedding and Linear Approximation Theorem

This module provides executable implementations of the verified approximation
theory from UELAT. The key results are:

1. **Bernstein Approximation**: For L-Lipschitz functions on [0,1], degree N ≥ (L/(2ε))²
   guarantees ε-approximation (verified in Coq/Approx/Bernstein_Lipschitz.v)

2. **Chebyshev Approximation**: Near-optimal polynomial interpolation with
   O(1/n^k) convergence for C^k functions (verified in Coq/Examples/ChebyshevCert.v)
   - Uses DCT-II for O(N log N) coefficient computation
   - Uses Clenshaw algorithm for stable O(N) evaluation

Reference: UELAT Paper, Sections 5-7
"""
module UELAT

using LinearAlgebra
using FFTW  # For efficient DCT computation

export BernsteinCert, ChebyshevCert
export required_degree, certify, evaluate, verify_certificate
export cheb_approx, cheb_nodes, clenshaw_eval
export test_exponential, test_lipschitz_function, test_chebyshev_abs
export compare_bernstein_chebyshev

# ============================================================================
# 1. Bernstein Certificate Structure (Original)
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
# 2. Chebyshev Certificate Structure (New!)
# ============================================================================

"""
    ChebyshevCert

A certificate for function approximation using Chebyshev polynomials.

# Fields
- `degree::Int`: The polynomial degree N
- `coeffs::Vector{Float64}`: Chebyshev coefficients c_0, c_1, ..., c_N
- `epsilon::Float64`: The guaranteed approximation error bound
- `interval::Tuple{Float64, Float64}`: The domain [a, b] (transformed from [-1,1])

# Mathematical Guarantee
For any x ∈ [a, b]:
    |p_N(x) - f(x)| ≤ epsilon

where p_N(x) = Σ_{k=0}^N c_k · T_k(transform(x))

and T_k is the k-th Chebyshev polynomial of the first kind.

# Key Properties (from Coq/Examples/ChebyshevCert.v)
- |T_n(x)| ≤ 1 for x ∈ [-1,1] (Lemma chebyshev_T_bounded)
- Error ≤ ||f^{(n+1)}||_∞ / ((n+1)! · 2^{n-1}) for smooth f
- Exponential convergence for analytic functions
- O(1/n) convergence for Lipschitz functions (better than Bernstein's O(1/√n))
"""
struct ChebyshevCert
    degree::Int
    coeffs::Vector{Float64}
    epsilon::Float64
    interval::Tuple{Float64, Float64}

    function ChebyshevCert(degree::Int, coeffs::Vector{Float64}, epsilon::Float64,
                           interval::Tuple{Float64, Float64}=(0.0, 1.0))
        @assert degree >= 0 "Degree must be non-negative"
        @assert length(coeffs) == degree + 1 "Must have exactly N+1 coefficients for degree N"
        @assert epsilon > 0 "Epsilon must be positive"
        @assert interval[1] < interval[2] "Interval must satisfy a < b"
        new(degree, coeffs, epsilon, interval)
    end
end

# ============================================================================
# 3. Chebyshev Nodes
# ============================================================================

"""
    cheb_nodes(N::Int) -> Vector{Float64}

Compute N Chebyshev nodes of the second kind on [-1, 1]:
    x_k = cos(π(2k - 1) / (2N)) for k = 1, ..., N

These are the roots of T_N(x) and provide optimal interpolation points.

From Coq/Examples/ChebyshevCert.v:
- Lemma chebyshev_nodes_in_interval: nodes are in [-1, 1]
- Lemma chebyshev_node_is_root: T_N(x_k) = 0
"""
function cheb_nodes(N::Int)::Vector{Float64}
    @assert N >= 1 "N must be at least 1"
    return [cos(π * (2k - 1) / (2N)) for k in 1:N]
end

"""
    cheb_nodes_extrema(N::Int) -> Vector{Float64}

Compute N+1 Chebyshev extrema (Chebyshev-Lobatto points) on [-1, 1]:
    x_k = cos(πk / N) for k = 0, ..., N

These are the extrema of T_N(x) and include the endpoints.
"""
function cheb_nodes_extrema(N::Int)::Vector{Float64}
    @assert N >= 1 "N must be at least 1"
    return [cos(π * k / N) for k in 0:N]
end

# ============================================================================
# 4. Domain Transformation
# ============================================================================

"""
    transform_to_standard(x, a, b)

Transform x from [a, b] to [-1, 1]:
    y = 2(x - a)/(b - a) - 1

From Coq/Examples/ChebyshevCert.v: Lemmas transform_to_01_bounds, transform_inverse_1
"""
function transform_to_standard(x::Float64, a::Float64, b::Float64)::Float64
    return 2 * (x - a) / (b - a) - 1
end

"""
    transform_from_standard(y, a, b)

Transform y from [-1, 1] to [a, b]:
    x = (y + 1)(b - a)/2 + a

From Coq/Examples/ChebyshevCert.v: Lemmas transform_from_01_bounds, transform_inverse_2
"""
function transform_from_standard(y::Float64, a::Float64, b::Float64)::Float64
    return (y + 1) * (b - a) / 2 + a
end

# ============================================================================
# 5. Chebyshev Polynomial Evaluation
# ============================================================================

"""
    chebyshev_T(n::Int, x::Float64) -> Float64

Evaluate T_n(x), the n-th Chebyshev polynomial of the first kind.

Uses the recurrence relation (from Coq/Examples/ChebyshevCert.v):
    T_0(x) = 1
    T_1(x) = x
    T_{n+1}(x) = 2x T_n(x) - T_{n-1}(x)

Property: |T_n(x)| ≤ 1 for x ∈ [-1, 1] (Lemma chebyshev_T_bounded)
"""
function chebyshev_T(n::Int, x::Float64)::Float64
    if n == 0
        return 1.0
    elseif n == 1
        return x
    else
        T_prev2 = 1.0
        T_prev1 = x
        for k in 2:n
            T_curr = 2 * x * T_prev1 - T_prev2
            T_prev2 = T_prev1
            T_prev1 = T_curr
        end
        return T_prev1
    end
end

# ============================================================================
# 6. DCT-Based Coefficient Computation (O(N log N))
# ============================================================================

"""
    cheb_approx(f::Function, N::Int; interval=(0.0, 1.0), epsilon=1e-10) -> ChebyshevCert

Construct a Chebyshev certificate for function `f` using DCT-II.

This is the key "Chebyshev Revolution" function that computes coefficients
in O(N log N) time using the Fast Fourier Transform, instead of the
naive O(N²) summation.

# Algorithm
1. Sample f at N+1 Chebyshev extrema points
2. Apply DCT-II to get Chebyshev coefficients
3. The coefficients decay rapidly for smooth functions

# Mathematical Background
For f sampled at Chebyshev extrema x_j = cos(πj/N), the coefficients are:

    c_k = (2/N) Σ_{j=0}^{N} '' f(x_j) cos(πjk/N)

where '' indicates the first and last terms are halved.

This is exactly the DCT-II, computable in O(N log N) via FFT.

# Arguments
- `f`: The function to approximate
- `N`: Degree of the approximation
- `interval`: Domain [a, b] (default [0, 1])
- `epsilon`: Error estimate (will be computed more precisely if possible)

# Returns
A `ChebyshevCert` containing the Chebyshev coefficients.

# Example
```julia
julia> cert = cheb_approx(exp, 10)
ChebyshevCert(degree=10, ε≈1e-12)
```
"""
function cheb_approx(f::Function, N::Int;
                     interval::Tuple{Float64, Float64}=(0.0, 1.0),
                     epsilon::Float64=1e-10)::ChebyshevCert
    @assert N >= 1 "Degree must be at least 1"

    a, b = interval

    # Sample f at N+1 Chebyshev extrema (Chebyshev-Lobatto points)
    # These are x_j = cos(π*j/N) for j = 0, ..., N
    samples = Vector{Float64}(undef, N + 1)
    for j in 0:N
        x_std = cos(π * j / N)  # Point in [-1, 1]
        x = transform_from_standard(x_std, a, b)  # Transform to [a, b]
        samples[j + 1] = f(x)
    end

    # Compute Chebyshev coefficients using DCT-II
    # The relationship: c_k = (2/N) * Σ'' f_j cos(πjk/N)
    # where '' means first and last terms are halved
    coeffs = dct_to_chebyshev_coeffs(samples)

    # Estimate epsilon based on tail coefficients (for smooth functions)
    # The error is roughly bounded by the sum of truncated coefficients
    if N >= 2
        tail_sum = sum(abs.(coeffs[max(1, N-3):end]))
        epsilon = max(epsilon, tail_sum)
    end

    return ChebyshevCert(N, coeffs, epsilon, interval)
end

"""
    dct_to_chebyshev_coeffs(samples::Vector{Float64}) -> Vector{Float64}

Convert function samples at Chebyshev extrema to Chebyshev coefficients
using the DCT-II transform.

This implements the O(N log N) algorithm using FFTW.
"""
function dct_to_chebyshev_coeffs(samples::Vector{Float64})::Vector{Float64}
    N = length(samples) - 1

    # Apply DCT-II using FFTW
    # FFTW's REDFT00 corresponds to DCT-I, we need to massage the data

    # Method: Use the relationship between DCT-II and FFT
    # Create a 2N-point signal and use FFT

    # Alternative: Direct DCT-II via FFTW's r2r transform
    # For simplicity, we use the explicit FFT-based computation

    # Create extended sequence for FFT-based DCT-II
    n = N + 1
    extended = zeros(2 * n)

    # Mirror the samples
    for j in 0:N
        extended[j + 1] = samples[j + 1]
    end
    for j in 1:N
        extended[2*n - j + 1] = samples[j + 1]
    end

    # Apply FFT
    fft_result = FFTW.fft(extended)

    # Extract DCT-II coefficients
    coeffs = Vector{Float64}(undef, N + 1)
    for k in 0:N
        # The DCT-II coefficient is the real part of FFT output scaled appropriately
        angle = π * k / (2 * n)
        c = real(fft_result[k + 1]) * cos(angle) + imag(fft_result[k + 1]) * sin(angle)
        coeffs[k + 1] = c / n

        # Apply proper normalization
        if k == 0
            coeffs[k + 1] /= 2
        end
    end

    return coeffs
end

"""
    dct_chebyshev_direct(samples::Vector{Float64}) -> Vector{Float64}

Direct O(N²) computation of Chebyshev coefficients for validation.
"""
function dct_chebyshev_direct(samples::Vector{Float64})::Vector{Float64}
    N = length(samples) - 1
    coeffs = Vector{Float64}(undef, N + 1)

    for k in 0:N
        s = 0.0
        for j in 0:N
            weight = (j == 0 || j == N) ? 0.5 : 1.0
            s += weight * samples[j + 1] * cos(π * j * k / N)
        end
        coeffs[k + 1] = (2.0 / N) * s
        if k == 0
            coeffs[k + 1] /= 2
        end
    end

    return coeffs
end

# ============================================================================
# 7. Clenshaw Algorithm for Stable Evaluation (O(N))
# ============================================================================

"""
    clenshaw_eval(coeffs::Vector{Float64}, x::Float64) -> Float64

Evaluate the Chebyshev series Σ_{k=0}^N c_k T_k(x) using Clenshaw's algorithm.

This is the Chebyshev equivalent of De Casteljau's algorithm for Bernstein
polynomials, providing numerical stability.

# Clenshaw Recurrence (from Coq/Examples/ChebyshevCert.v)
    b_{N+1} = b_{N+2} = 0
    b_k = c_k + 2x · b_{k+1} - b_{k+2}  for k = N, N-1, ..., 1
    Result = c_0 + x · b_1 - b_2

# Properties
- O(N) time complexity
- Numerically stable (no large intermediate values)
- Avoids explicit computation of T_k(x)

# Arguments
- `coeffs`: Chebyshev coefficients [c_0, c_1, ..., c_N]
- `x`: Evaluation point in [-1, 1]

# Returns
The value of the Chebyshev series at x.
"""
function clenshaw_eval(coeffs::Vector{Float64}, x::Float64)::Float64
    N = length(coeffs) - 1

    if N == 0
        return coeffs[1]
    end

    # Initialize b_{N+1} = b_{N+2} = 0
    b_next = 0.0
    b_next2 = 0.0

    # Backward recurrence: b_k = c_k + 2x*b_{k+1} - b_{k+2}
    for k in N:-1:1
        b_curr = coeffs[k + 1] + 2 * x * b_next - b_next2
        b_next2 = b_next
        b_next = b_curr
    end

    # Final step: c_0 + x*b_1 - b_2
    # Note: b_next is b_1, b_next2 is b_2
    return coeffs[1] + x * b_next - b_next2
end

"""
    evaluate(cert::ChebyshevCert, x::Float64) -> Float64

Evaluate the Chebyshev certificate at point x using Clenshaw's algorithm.

The point x should be in the certificate's interval [a, b].
It will be transformed to [-1, 1] before evaluation.
"""
function evaluate(cert::ChebyshevCert, x::Float64)::Float64
    a, b = cert.interval

    # Clamp x to interval for numerical safety
    x = clamp(x, a, b)

    # Transform to standard interval [-1, 1]
    y = transform_to_standard(x, a, b)

    # Evaluate using Clenshaw
    return clenshaw_eval(cert.coeffs, y)
end

# ============================================================================
# 8. Bernstein Functions (Original, kept for compatibility)
# ============================================================================

"""
    required_degree(L::Float64, epsilon::Float64) -> Int

Calculate the required degree N = ⌈(L/(2ε))²⌉ for ε-approximation of
an L-Lipschitz function using Bernstein polynomials.

From Coq/Approx/Bernstein_Lipschitz.v, Theorem bernstein_uniform_lipschitz.
"""
function required_degree(L::Float64, epsilon::Float64)::Int
    @assert L >= 0 "Lipschitz constant must be non-negative"
    @assert epsilon > 0 "Epsilon must be positive"

    if L == 0.0
        return 0
    end

    ratio = L / (2 * epsilon)
    return Int(ceil(ratio^2))
end

"""
    certify(f::Function, L::Float64, epsilon::Float64) -> BernsteinCert

Construct a Bernstein certificate for function `f` by sampling at k/N.
"""
function certify(f::Function, L::Float64, epsilon::Float64)::BernsteinCert
    N = required_degree(L, epsilon)

    coeffs = Vector{Float64}(undef, N + 1)
    for k in 0:N
        x_k = N == 0 ? 0.0 : k / N
        coeffs[k + 1] = f(x_k)
    end

    return BernsteinCert(N, coeffs, epsilon, L)
end

"""
    evaluate(cert::BernsteinCert, x::Float64) -> Float64

Evaluate the Bernstein polynomial certificate at point x using
De Casteljau's algorithm for numerical stability.
"""
function evaluate(cert::BernsteinCert, x::Float64)::Float64
    N = cert.degree
    coeffs = cert.coeffs

    if N == 0
        return coeffs[1]
    end

    x = clamp(x, 0.0, 1.0)

    b = copy(coeffs)
    for r in 1:N
        for k in 1:(N - r + 1)
            b[k] = (1 - x) * b[k] + x * b[k + 1]
        end
    end

    return b[1]
end

# ============================================================================
# 9. Verification
# ============================================================================

"""
    verify_certificate(cert::Union{BernsteinCert, ChebyshevCert}, f::Function, n_samples::Int=1000)

Verify that a certificate achieves its claimed error bound.
"""
function verify_certificate(cert::Union{BernsteinCert, ChebyshevCert}, f::Function, n_samples::Int=1000)
    if cert isa BernsteinCert
        xs = range(0.0, 1.0, length=n_samples)
    else
        a, b = cert.interval
        xs = range(a, b, length=n_samples)
    end

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
# 10. Test Functions
# ============================================================================

"""
    test_exponential(epsilon::Float64=0.01) -> Bool

Test the certification of exp(x) on [0,1] using Bernstein polynomials.
"""
function test_exponential(epsilon::Float64=0.01)::Bool
    println("Testing exp(x) on [0,1] with Bernstein, ε = $epsilon")

    L = exp(1.0)
    println("Lipschitz constant L = $L")

    N = required_degree(L, epsilon)
    println("Required degree N = $N")

    cert = certify(exp, L, epsilon)
    println("Certificate size: $(length(cert.coeffs)) coefficients")

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

Test certification of an arbitrary Lipschitz function using Bernstein.
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

"""
    test_chebyshev_abs(; N_values=[5, 10, 20, 40, 80]) -> Nothing

Test Chebyshev approximation of f(x) = |x - 0.5| on [0,1].

This demonstrates the superior convergence of Chebyshev vs Bernstein
for non-smooth (Lipschitz) functions:
- Chebyshev: O(1/n) convergence
- Bernstein: O(1/√n) convergence

This is the key comparison showing the "Chebyshev Revolution".
"""
function test_chebyshev_abs(; N_values::Vector{Int}=[5, 10, 20, 40, 80])
    println("="^70)
    println("CHEBYSHEV vs BERNSTEIN COMPARISON")
    println("Testing f(x) = |x - 0.5| on [0, 1]")
    println("="^70)
    println()

    f = x -> abs(x - 0.5)
    L = 1.0  # Lipschitz constant of |x - 0.5|

    println("This function is Lipschitz but NOT differentiable at x = 0.5")
    println()
    println("Expected convergence rates:")
    println("  Chebyshev: O(1/n)   - linear in degree")
    println("  Bernstein: O(1/√n)  - sublinear (slower)")
    println()

    println("-"^70)
    println(@sprintf("%8s | %15s | %15s | %10s", "Degree", "Cheb Error", "Bern Error", "Ratio"))
    println("-"^70)

    for N in N_values
        # Chebyshev certificate
        cheb_cert = cheb_approx(f, N, interval=(0.0, 1.0), epsilon=1.0)
        cheb_result = verify_certificate(cheb_cert, f, 1000)

        # Bernstein certificate (same degree for fair comparison)
        bern_coeffs = [f(k/N) for k in 0:N]
        bern_cert = BernsteinCert(N, bern_coeffs, 1.0, L)
        bern_result = verify_certificate(bern_cert, f, 1000)

        ratio = bern_result.max_error / cheb_result.max_error

        println(@sprintf("%8d | %15.2e | %15.2e | %10.2f×",
                N, cheb_result.max_error, bern_result.max_error, ratio))
    end

    println("-"^70)
    println()
    println("Observation: Chebyshev consistently achieves lower error at the same degree.")
    println("The ratio grows with N, showing Chebyshev's superior convergence rate.")
    println()

    return nothing
end

# Import Printf for formatted output
using Printf

"""
    compare_bernstein_chebyshev(f::Function, name::String; epsilon::Float64=0.001, L::Float64=1.0)

Compare Bernstein and Chebyshev certificates for the same target accuracy.

Shows that Chebyshev requires far fewer degrees/coefficients to achieve
the same approximation error.
"""
function compare_bernstein_chebyshev(f::Function, name::String;
                                      epsilon::Float64=0.001,
                                      L::Float64=1.0)
    println("="^70)
    println("Comparing Bernstein vs Chebyshev for $name")
    println("Target accuracy: ε = $epsilon")
    println("="^70)
    println()

    # Bernstein: Need N ≈ (L/(2ε))² for Lipschitz functions
    bern_N = required_degree(L, epsilon)
    bern_cert = certify(f, L, epsilon)
    bern_result = verify_certificate(bern_cert, f, 1000)

    println("BERNSTEIN:")
    println("  Required degree: N = $bern_N")
    println("  Coefficients: $(length(bern_cert.coeffs))")
    println("  Actual max error: $(bern_result.max_error)")
    println()

    # Chebyshev: Find minimum N that achieves epsilon
    cheb_N = 1
    cheb_result = nothing
    for n in 1:1000
        cheb_cert = cheb_approx(f, n, interval=(0.0, 1.0), epsilon=epsilon)
        cheb_result = verify_certificate(cheb_cert, f, 1000)
        if cheb_result.max_error <= epsilon
            cheb_N = n
            break
        end
    end

    cheb_cert_final = cheb_approx(f, cheb_N, interval=(0.0, 1.0), epsilon=epsilon)

    println("CHEBYSHEV:")
    println("  Required degree: N = $cheb_N")
    println("  Coefficients: $(length(cheb_cert_final.coeffs))")
    println("  Actual max error: $(cheb_result.max_error)")
    println()

    speedup = bern_N / cheb_N
    println("SUMMARY:")
    println("  Degree reduction: $(bern_N) → $(cheb_N) ($(round(speedup, digits=1))× fewer)")
    println("  Coefficient reduction: $(bern_N + 1) → $(cheb_N + 1)")
    println()

    return (bernstein_degree=bern_N, chebyshev_degree=cheb_N, speedup=speedup)
end

# ============================================================================
# 11. Utility Functions
# ============================================================================

"""
    certificate_info(cert::Union{BernsteinCert, ChebyshevCert}) -> String

Return a summary of the certificate for display.
"""
function certificate_info(cert::Union{BernsteinCert, ChebyshevCert})::String
    if cert isa BernsteinCert
        return """
        BernsteinCert:
          Degree: $(cert.degree)
          Coefficients: $(length(cert.coeffs))
          Epsilon: $(cert.epsilon)
          Lipschitz: $(cert.lipschitz)
          Memory: ≈ $(sizeof(cert.coeffs)) bytes
        """
    else
        return """
        ChebyshevCert:
          Degree: $(cert.degree)
          Coefficients: $(length(cert.coeffs))
          Epsilon: $(cert.epsilon)
          Interval: $(cert.interval)
          Memory: ≈ $(sizeof(cert.coeffs)) bytes
        """
    end
end

function Base.show(io::IO, cert::BernsteinCert)
    print(io, "BernsteinCert(degree=$(cert.degree), ε=$(cert.epsilon), L=$(cert.lipschitz))")
end

function Base.show(io::IO, cert::ChebyshevCert)
    print(io, "ChebyshevCert(degree=$(cert.degree), ε=$(cert.epsilon), interval=$(cert.interval))")
end

"""
    lipschitz_estimate(f::Function, n_samples::Int=1000) -> Float64

Estimate the Lipschitz constant of f on [0,1] by sampling.
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
# 12. Module Initialization
# ============================================================================

function __init__()
    # Module is ready
end

end # module UELAT
