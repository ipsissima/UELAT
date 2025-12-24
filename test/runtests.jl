using Test
using UELAT

@testset "UELAT Tests" begin

    @testset "Bernstein Certificate" begin
        @testset "required_degree" begin
            # For L=1, epsilon=0.1: N = ceil((1/(2*0.1))^2) = ceil(25) = 25
            @test required_degree(1.0, 0.1) == 25
            # For L=0, any epsilon: N = 0 (constant function)
            @test required_degree(0.0, 0.01) == 0
        end

        @testset "certify and evaluate" begin
            # Test with a simple linear function f(x) = x
            cert = certify(identity, 1.0, 0.1)
            @test cert.degree >= 1
            @test length(cert.coeffs) == cert.degree + 1

            # Evaluation should match f(x) closely
            for x in [0.0, 0.25, 0.5, 0.75, 1.0]
                @test abs(evaluate(cert, x) - x) < 0.1
            end
        end

        @testset "De Casteljau stability" begin
            # High degree should still work
            f = x -> sin(2π * x)
            cert = certify(f, 2π, 0.01)
            # Evaluate at several points
            for x in 0:0.1:1
                val = evaluate(cert, x)
                @test isfinite(val)
            end
        end
    end

    @testset "Chebyshev Certificate" begin
        @testset "cheb_nodes" begin
            nodes = cheb_nodes(5)
            @test length(nodes) == 5
            # All nodes should be in [-1, 1]
            @test all(-1 .<= nodes .<= 1)
            # Nodes should be symmetric around 0
            @test nodes ≈ -reverse(nodes) atol=1e-10
        end

        @testset "chebyshev_T" begin
            # T_0(x) = 1
            @test UELAT.chebyshev_T(0, 0.5) == 1.0
            # T_1(x) = x
            @test UELAT.chebyshev_T(1, 0.5) == 0.5
            # T_2(x) = 2x^2 - 1
            @test UELAT.chebyshev_T(2, 0.5) ≈ 2*0.5^2 - 1 atol=1e-10
            # T_n(1) = 1 for all n
            for n in 0:10
                @test UELAT.chebyshev_T(n, 1.0) ≈ 1.0 atol=1e-10
            end
            # T_n(-1) = (-1)^n for all n
            for n in 0:10
                @test UELAT.chebyshev_T(n, -1.0) ≈ (-1.0)^n atol=1e-10
            end
            # |T_n(x)| <= 1 for x in [-1, 1] (key property from Coq proof)
            for n in 1:20
                for x in -1:0.1:1
                    @test abs(UELAT.chebyshev_T(n, x)) <= 1.0 + 1e-10
                end
            end
        end

        @testset "clenshaw_eval" begin
            # Test with simple cases
            # c = [1] -> 1*T_0(x) = 1
            @test clenshaw_eval([1.0], 0.5) == 1.0
            # c = [0, 1] -> 0*T_0(x) + 1*T_1(x) = x
            @test clenshaw_eval([0.0, 1.0], 0.5) ≈ 0.5 atol=1e-10
            # c = [0, 0, 1] -> T_2(x) = 2x^2 - 1
            @test clenshaw_eval([0.0, 0.0, 1.0], 0.5) ≈ 2*0.5^2 - 1 atol=1e-10
        end

        @testset "cheb_approx exponential" begin
            # Exponential should converge very fast (analytic function)
            cert = cheb_approx(exp, 10, interval=(0.0, 1.0))
            @test cert.degree == 10
            @test length(cert.coeffs) == 11

            # Check accuracy at several points
            for x in 0:0.1:1
                @test abs(evaluate(cert, x) - exp(x)) < 1e-6
            end
        end

        @testset "cheb_approx polynomial" begin
            # Polynomial of degree n should be exact with degree >= n
            f = x -> x^3 - 2x^2 + x - 1
            cert = cheb_approx(f, 5, interval=(-1.0, 1.0))

            for x in -1:0.2:1
                @test abs(evaluate(cert, x) - f(x)) < 1e-10
            end
        end

        @testset "domain transformation" begin
            # Test on [0, 1] interval
            cert = cheb_approx(sin, 20, interval=(0.0, 1.0))
            for x in 0:0.1:1
                @test abs(evaluate(cert, x) - sin(x)) < 1e-8
            end

            # Test on [-2, 2] interval
            cert2 = cheb_approx(cos, 20, interval=(-2.0, 2.0))
            for x in -2:0.4:2
                @test abs(evaluate(cert2, x) - cos(x)) < 1e-8
            end
        end
    end

    @testset "Chebyshev vs Bernstein Comparison" begin
        # For Lipschitz functions, Chebyshev should achieve lower error at same degree
        f = x -> abs(x - 0.5)

        for N in [10, 20, 40]
            cheb_cert = cheb_approx(f, N, interval=(0.0, 1.0), epsilon=1.0)
            bern_coeffs = [f(k/N) for k in 0:N]
            bern_cert = BernsteinCert(N, bern_coeffs, 1.0, 1.0)

            cheb_err = maximum(abs(evaluate(cheb_cert, x) - f(x)) for x in 0:0.01:1)
            bern_err = maximum(abs(evaluate(bern_cert, x) - f(x)) for x in 0:0.01:1)

            # Chebyshev should be better (or at least comparable)
            @test cheb_err <= bern_err * 1.1  # Allow 10% margin for numerical issues
        end
    end

    @testset "verify_certificate" begin
        # Test verification for Bernstein
        bern_cert = certify(exp, exp(1.0), 0.01)
        bern_result = verify_certificate(bern_cert, exp, 100)
        @test bern_result.max_error >= 0
        @test bern_result.mean_error >= 0

        # Test verification for Chebyshev
        cheb_cert = cheb_approx(exp, 15, interval=(0.0, 1.0))
        cheb_result = verify_certificate(cheb_cert, exp, 100)
        @test cheb_result.max_error >= 0
        @test cheb_result.max_error < 1e-10  # exp is analytic, should be very accurate
    end
end

println("All UELAT tests passed!")
