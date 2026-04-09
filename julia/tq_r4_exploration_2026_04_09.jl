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

function image_rank(u)
    basis, basis_2d = get_basis(x, length(u), 2)
    Au = get_Au(u, basis, basis_2d)
    rank(Au)
end

function basis_image_ranks()
    us = [collect(ui) for ui in combinations(monomials(x, 0:2), 4)]
    for u in us
        println("basis_image_rank = (u = ", u, ", rank = ", image_rank(u), ")")
    end
end

function missing_monomials(u)
    _, basis_2d = get_basis(x, length(u), 2)
    Au = get_Au(u, get_basis(x, length(u), 2)...)
    r = rank(Au)
    missing = Any[]
    for (idx, m) in enumerate(basis_2d)
        e = zeros(Float64, length(basis_2d))
        e[idx] = 1.0
        if rank(hcat(Au, e)) == r + 1
            push!(missing, m)
        end
    end
    missing
end

function dual_probe()
    u = [one(x[1]), x[2], x[1], x[2]^2]
    a = randn(length(monomials(x, 0:4)))
    model, _, grad_c, psd_c, sos_c, nonzero_c = counter_homogeneous(x, 2, u, a; verbose=false)
    println("dual_probe_status = (termination = ", termination_status(model),
        ", dual = ", dual_status(model), ", grad_constraints = ", length(grad_c), ")")
    println("dual_probe_types = (psd = ", typeof(dual(psd_c)),
        ", sos = ", typeof(dual(sos_c)), ", nonzero_dual = ", dual(nonzero_c),
        ", first_grad_dual = ", dual(grad_c[1]), ")")
end

function normal_form_probe()
    cands = [
        [one(x[1]), x[1], x[2], x[1]^2 + x[2]^2],
        [one(x[1]), x[1], x[2], x[1]^2 - x[2]^2],
        [one(x[1]), x[1], x[2], x[1] * x[2] + x[1]^2],
        [one(x[1]), x[1], x[2], x[1] * x[2] + x[2]^2],
        [x[1], x[2], x[1]^2 + x[2]^2, x[1] * x[2]],
        [x[1], x[2], x[1]^2 - x[2]^2, x[1] * x[2]],
    ]
    for u in cands
        err = find_counter(x, u; ntrials=1, verbose=false)
        println("normal_form_probe = (u = ", u, ", rank = ", image_rank(u), ", err = ", err, ")")
    end
end

function kernel_family_probe()
    u = [one(x[1]), x[2], x[1], x[2]^2]
    w = [-x[1]^2, zero(x[1]), x[1], zero(x[1])]
    println("kernel_family_probe = (Auw = ", u' * w, ", sigmaw = ", sum(wi^2 for wi in w), ")")
end

function low_affine_probe()
    cands = [
        [one(x[1]), x[1]^2, x[1] * x[2], x[2]^2],
        [x[1], x[1]^2, x[1] * x[2], x[2]^2],
        [x[1], x[2], x[1]^2, x[1] * x[2]],
        [x[1], x[2], x[1]^2 + x[2]^2, x[1] * x[2]],
    ]
    for u in cands
        err = find_counter(x, u; ntrials=1, verbose=false)
        println("low_affine_probe = (u = ", u, ", rank = ", image_rank(u), ", err = ", err, ")")
    end
end

function mixed_affine_probe()
    cands = [
        [one(x[1]), x[1], x[1]^2, x[1] * x[2]],
        [one(x[1]), x[1], x[1] * x[2], x[2]^2],
        [one(x[1]), x[1], x[1]^2, x[2]^2],
    ]
    for u in cands
        err = find_counter(x, u; ntrials=1, verbose=false)
        println("mixed_affine_probe = (u = ", u, ", rank = ", image_rank(u),
            ", missing = ", missing_monomials(u), ", err = ", err, ")")
    end
end

function mixed_affine_kernel_probe()
    u13 = [one(x[1]), x[1], x[1]^2, x[1] * x[2]]
    w13 = [zero(x[1]), zero(x[1]), -x[2]^2, x[1] * x[2]]
    println("mixed_affine_kernel_probe = (u = ", u13,
        ", w = ", w13, ", Auw = ", u13' * w13,
        ", sigmaw = ", sum(wi^2 for wi in w13), ")")

    u14 = [one(x[1]), x[1], x[1] * x[2], x[2]^2]
    w14 = [zero(x[1]), zero(x[1]), -x[1] * x[2], x[1]^2]
    println("mixed_affine_kernel_probe = (u = ", u14,
        ", w = ", w14, ", Auw = ", u14' * w14,
        ", sigmaw = ", sum(wi^2 for wi in w14), ")")
end

random_rank4_sweep()
basis_image_ranks()
basis_sweep()
dual_probe()
normal_form_probe()
kernel_family_probe()
low_affine_probe()
mixed_affine_probe()
mixed_affine_kernel_probe()
