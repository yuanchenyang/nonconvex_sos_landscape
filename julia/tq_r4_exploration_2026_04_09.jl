include("counter_poly.jl")

using Combinatorics
using DynamicPolynomials
using JuMP
using Random
import MathOptInterface

const MOI = MathOptInterface

Random.seed!(20260409)

@polyvar x[1:2]

function random_rank4_sweep()
    errs = [find_counter(x, rand_u(x, 2, 4); ntrials=1, verbose=false) for _ in 1:5]
    println("random_rank4_errs = ", errs)
    errs
end

function basis_sweep(; max_retries=5)
    _, basis_2d = get_basis(x, 4, 2)
    us = [collect(ui) for ui in combinations(monomials(x, 0:2), 4)]
    results = NamedTuple[]
    for u in us
        verdict = "unknown"
        status = MOI.OTHER_ERROR
        for _ in 1:max_retries
            a = randn(length(basis_2d))
            model, _, _, _, _, _ = counter_homogeneous(x, 2, u, a; verbose=false)
            status = termination_status(model)
            if status == MOI.INFEASIBLE
                verdict = "no_counter"
                break
            elseif status == MOI.OPTIMAL || status == MOI.ALMOST_OPTIMAL
                verdict = "counter"
                break
            end
        end
        result = (u=u, verdict=verdict, status=status)
        push!(results, result)
        println(result)
    end
    counters = count(r -> r.verdict == "counter", results)
    unknowns = count(r -> r.verdict == "unknown", results)
    println("basis_sweep_summary = (cases = ", length(results),
        ", counters = ", counters, ", unknowns = ", unknowns, ")")
    results
end

random_rank4_sweep()
basis_sweep()
