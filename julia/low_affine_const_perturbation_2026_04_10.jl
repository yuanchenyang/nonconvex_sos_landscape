using LinearAlgebra
using Random

Random.seed!(20260410)

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
        idx = basis_index(QUARTIC_BASIS, (ei[1] + ej[1], ei[2] + ej[2]))
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

function affine_pair_const_plane_probe(samples::Int = 20)
    x0 = quad_coeffs(a10 = 1.0)
    x1 = quad_coeffs(a01 = 1.0)

    generic_ranks = Int[]
    generic_missing = nothing

    for _ in 1:samples
        C = randn(2, 3)
        rank(C) < 2 && continue
        a, b = randn(), randn()
        q2 = quad_coeffs(a00 = a, a20 = C[1, 1], a11 = C[1, 2], a02 = C[1, 3])
        q3 = quad_coeffs(a00 = b, a20 = C[2, 1], a11 = C[2, 2], a02 = C[2, 3])
        data = image_rank_missing([x0, x1, q2, q3])
        push!(generic_ranks, data.rank)
        if generic_missing === nothing
            generic_missing = data.missing
        end
    end

    controls = (
        coprime_const =
            image_rank_missing([x0, x1, quad_coeffs(a00 = 1.0, a20 = 1.0), quad_coeffs(a02 = 1.0)]),
        common_factor_const =
            image_rank_missing([x0, x1, quad_coeffs(a00 = 1.0, a20 = 1.0), quad_coeffs(a11 = 1.0)]),
        diagonal_const =
            image_rank_missing([x0, x1, quad_coeffs(a00 = 1.0, a20 = 1.0), quad_coeffs(a02 = 1.0)]),
        split_const =
            image_rank_missing([x0, x1, quad_coeffs(a00 = 1.0, a11 = 1.0), quad_coeffs(a20 = 1.0, a02 = -1.0)]),
    )

    result = (
        samples = samples,
        generic_ranks = sort(unique(generic_ranks)),
        generic_missing = generic_missing,
        controls = controls,
    )
    println("low_affine_const_perturbation_probe = ", result)
    result
end

affine_pair_const_plane_probe()
