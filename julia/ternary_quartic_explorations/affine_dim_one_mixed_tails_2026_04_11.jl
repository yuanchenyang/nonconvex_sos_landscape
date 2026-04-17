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

function exact_affine_dim(u::Vector{Vector{Float64}})
    H = reduce(hcat, [ui[4:6] for ui in u])
    F = svd(H)
    r = sum(F.S .> 1e-9)
    4 - r
end

function matrix_rank(M::Matrix{Float64})
    F = svd(M)
    sum(F.S .> 1e-9)
end

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

function affine_dim_one_mixed_tail_probe(; samples = 20)
    x0 = quad_coeffs(a10 = 1.0)
    data = NamedTuple[]

    while length(data) < samples
        α = randn(3)
        β = randn(3)
        T = [α[1] α[2] α[3]; β[1] β[2] β[3]]
        trank = matrix_rank(T)
        if trank < 2
            continue
        end

        u = [
            x0,
            quad_coeffs(a00 = α[1], a01 = β[1], a20 = 1.0),
            quad_coeffs(a00 = α[2], a01 = β[2], a11 = 1.0),
            quad_coeffs(a00 = α[3], a01 = β[3], a02 = 1.0),
        ]

        push!(data, (;
            α20 = α[1], β20 = β[1],
            α11 = α[2], β11 = β[2],
            α02 = α[3], β02 = β[3],
            tail_rank = trank,
            exact_affine_dim = exact_affine_dim(u),
            image_rank_missing(u)...,
        ))
    end

    result = (
        samples = samples,
        mixed_tail = data,
        tail_ranks = sort(unique(x.tail_rank for x in data)),
        exact_affine_dims = sort(unique(x.exact_affine_dim for x in data)),
        image_ranks = sort(unique(x.rank for x in data)),
        missing = sort(unique(x.missing for x in data)),
    )
    println("affine_dim_one_mixed_tail_probe = ", result)
    result
end

affine_dim_one_mixed_tail_probe()
