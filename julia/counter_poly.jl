import AutoGrad
using LinearAlgebra
using SumOfSquares
using DynamicPolynomials
using MultivariatePolynomials
using ProgressBars
MP = MultivariatePolynomials
using Combinatorics
using JuMP
import MathOptInterface
using MosekTools
using CSDP
using SCS

const MOI = MathOptInterface

dotp(p1, p2) = reduce(+, [MP.coefficient(p1, m)*MP.coefficient(p2, m) for m in monomials(p1)], init=0)

round_poly(p; digits=6) = reduce(+, [round(MP.coefficient(p, m), digits=digits) * m for m in monomials(p)], init=zero(p))

function rand_poly(vars, d)
    m = monomials(vars,0:d)
    m'*randn(length(m))
end

rand_u(vars, d, r) = [rand_poly(vars, d) for i in 1:r]

function feasiblep(model, vars, u; hess=true, hom=false)
    # vars: Polynomial variables
    # hess: Whether to include Hessian

    n = length(vars)
    r = length(u) # Number of squares
    d = maximum(map(maxdegree, u)) # 2d is the degree of p
    X = monomials(vars, 0:2*d)
    @variable(model, p, Poly(X))

    smp = u'*u - p

    basis = [col * m for col in eachcol(Matrix{Float64}(I,r,r))
                     for m in monomials(vars, 0:d)]
    l = length(basis)

    # Gradient constraint
    for bi in basis
        @constraint(model, dotp(bi'*u, smp) == 0)
    end

    # Hessian constraint
    if hess
        h(vi, vj) = dotp(vi'*vj, smp) + 2 * dotp(u'*vi, u'*vj)

        H = reshape(AffExpr[h(vi, vj) for vi in basis for vj in basis], l, l)

        @variable(model, Hm[1:l, 1:l], PSD)
        @constraint(model, H .== Hm)
    end

    @constraint(model, p in SOSCone())
    return p
end


function find_counter(vars, u; ntrials=10, hess=true, verbose=true)
    res = Float64[]
    for i in 1:ntrials
        #solver = optimizer_with_attributes(Mosek.Optimizer, MOI.Silent() => !verbose)
        solver = optimizer_with_attributes(CSDP.Optimizer, MOI.Silent() => !verbose)
        model = SOSModel(solver)
        p = feasiblep(model, vars, u, hess=hess)
        c = coefficients(p)
        @objective(model, Max, randn(length(c))'*c)
        optimize!(model)
        err = norm(coefficients(value(p - u'*u)))
        append!(res, err)
        if verbose
            @show termination_status(model)
            @show round_poly(value(p))
            @show round_poly(value(p - u'*u))
            @show err
        end
    end
    maximum(res)
end

# Example 1: Univariate polynomials
function test_univariate(;d=5, ntrials=10, verbose=false, tol=1e-2)
    # X is a binary form (i.e. univariate polynomial)
    @polyvar x[1:1]

    # r=1 should find counterexample
    counter_value = find_counter(x, rand_u(x, d, 1); ntrials, verbose)
    @assert counter_value > 0.1

    # r=2 should not find counterexample
    for _ in 1:10
        counter_value = find_counter(x, rand_u(x, d, 2); ntrials, verbose)
        @assert isapprox(counter_value, 0.; atol=tol)
    end
end

function get_basis(x, r, d)
    basis = [col * m for col in eachcol(Matrix{Float64}(I,r,r))
                     for m in monomials(x, 0:d)]
    basis_2d = monomials(x, 0:2d)
    basis, basis_2d
end

function counter_homogeneous(x, d, u, a; verbose=true)
    model = SOSModel(CSDP.Optimizer) #SOSModel(Mosek.Optimizer) #
    if ! verbose
        set_silent(model)
    end
    basis, basis_2d = get_basis(x, length(u), d)

    @variable(model, p, Poly(basis_2d))
    @variable(model, gamma >= 0)
    smp = u'*u*gamma - p
    grad_c = [@constraint(model, dotp(bi'*u, smp) == 0) for bi in basis]

    # Hessian constraint
    h(vi, vj) = dotp(vi'*vj, smp) + 2 * gamma * dotp(u'*vi, u'*vj)

    l = length(basis)
    H = reshape(AffExpr[h(vi, vj) for vi in basis for vj in basis], l, l)
    psd_c = @constraint(model, H in PSDCone())
    sos_c = @constraint(model, p in SOSCone())

    # We want to check if the only solution is when the homogeneous variable c
    # == 0, to do that we pick a at random and check if a'*c == 1. This should
    # almost surely avoid cases where c != 0 but a'*c is identically 0.
    nonzero_c = @constraint(model, a'*coefficients(smp) == 1)
    optimize!(model)

    if verbose
        @show solution_summary(model)
        @show round_poly(value(smp); digits=3)
    end

    model, smp, grad_c, psd_c, sos_c, nonzero_c
end

function psub(p, basis)
    [MP.coefficient(p, b) for b in basis]
end

function psuba(p, basis, a)
    [MP.coefficient(p, b) for b in basis]' * a
end

function get_Au(u, basis, basis_2d)
    hcat([psub(u' * bi, basis_2d) for bi in basis]...)
end

function search_basis(n, d, r)
    @polyvar x[1:n]
    basis, basis_2d = get_basis(x, r, d)
    found_counter = "unknown"
    us = [ui for ui in combinations(monomials(x, 0:d), r)]
    # @show length(us)
    for u in ProgressBar(us)
        while true
            a = randn(length(basis_2d))
            model, smp, grad_c, psd_c, sos_c, nonzero_c = counter_homogeneous(x, d, u, a; verbose=false)
            if termination_status(model) == INFEASIBLE
                found_counter = "NO "
                break
            elseif termination_status(model) in [OPTIMAL, ALMOST_OPTIMAL]
                found_counter = "YES"
                break
            else
                @show termination_status(model)
            end
        end
        if found_counter == "YES"
            println(found_counter, "---", u)
            println()
        end
    end
end
