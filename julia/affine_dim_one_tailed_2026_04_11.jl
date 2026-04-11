using LinearAlgebra
using Random

Random.seed!(20260411)

const QUAD_BASIS = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
const QUARTIC_BASIS = [
    (0, 0),
    (1, 0), (0, 1),
    (2, 0), (1, 1), (0, 2),
    (3, 0), (2, 1), (1, 2), (0, 3),
    (4, 0), (3, 1), (2, 2), (1, 3), (0, 4),
]

function basis_index(basis, key)
    for (i, x) in enumerate(basis)
        if x == key
            return i
        end
    end
    error("missing basis element $(key)")
end

function poly_mul_to_quartic(a::Vector{Float64}, b::Vector{Float64})
    out = zeros(Float64, length(QUARTIC_BASIS))
    for (i, ei) in enumerate(QUAD_BASIS), (j, ej) in enumerate(QUAD_BASIS)
        idx = basis_index(QUARTIC_BASIS, (ei[1] + ej[1], ej[2] + ei[2]))
        out[idx] += a[i] * b[j]
    end
    out
end

function get_Au(u::Vector{Vector{Float64}})
    cols = Vector{Vector{Float64}}()
    for i in 1:length(u), j in 1:length(QUAD_BASIS)
        basis_poly = zeros(Float64, length(QUAD_BASIS))
        basis_poly[j] = 1.0
        push!(cols, poly_mul_to_quartic(u[i], basis_poly))
    end
    reduce(hcat, cols)
end

function image_rank_missing(u::Vector{Vector{Float64}})
    A = get_Au(u)
    F = svd(A)
    r = sum(F.S .> 1e-9)
    U = F.U[:, 1:r]
    missing = Tuple{Int, Int}[]
    for (i, m) in enumerate(QUARTIC_BASIS)
        e = zeros(Float64, length(QUARTIC_BASIS))
        e[i] = 1.0
        if norm(e - U * (transpose(U) * e)) > 1e-8
            push!(missing, m)
        end
    end
    (rank = r, missing = missing)
end

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

function affine_dim_one_tailed_probe()
    lambdas = [-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0]
    x0 = quad_coeffs(a10 = 1.0)
    x1sq = quad_coeffs(a02 = 1.0)
    x0sq = quad_coeffs(a20 = 1.0)
    x0x1 = quad_coeffs(a11 = 1.0)

    cross_tail = NamedTuple[]
    common_factor_tail = NamedTuple[]
    x0sq_tail = NamedTuple[]

    for λ in lambdas
        qtail_cross = quad_coeffs(a01 = 1.0, a11 = λ)
        qtail_x0sq = quad_coeffs(a01 = 1.0, a20 = λ)
        push!(cross_tail, (; λ, image_rank_missing([x0, qtail_cross, x0sq, x1sq])...))
        push!(common_factor_tail, (; λ, image_rank_missing([x0, qtail_cross, x0sq, x0x1])...))
        push!(x0sq_tail, (; λ, image_rank_missing([x0, qtail_x0sq, x0sq, x1sq])...))
    end

    result = (
        lambdas = lambdas,
        cross_tail = cross_tail,
        common_factor_tail = common_factor_tail,
        x0sq_tail = x0sq_tail,
        cross_tail_ranks = sort(unique(x.rank for x in cross_tail)),
        common_factor_tail_ranks = sort(unique(x.rank for x in common_factor_tail)),
        x0sq_tail_ranks = sort(unique(x.rank for x in x0sq_tail)),
        cross_tail_missing = sort(unique(x.missing for x in cross_tail)),
        common_factor_tail_missing = sort(unique(x.missing for x in common_factor_tail)),
        x0sq_tail_missing = sort(unique(x.missing for x in x0sq_tail)),
    )
    println("affine_dim_one_tailed_probe = ", result)
    result
end

affine_dim_one_tailed_probe()
