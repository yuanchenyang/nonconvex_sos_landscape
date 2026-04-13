using LinearAlgebra
using Random

Random.seed!(20260412)

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

function quad_coeffs(; a00 = 0.0, a10 = 0.0, a01 = 0.0, a20 = 0.0, a11 = 0.0, a02 = 0.0)
    [a00, a10, a01, a20, a11, a02]
end

function summarize(records)
    (
        count = length(records),
        ranks = sort(unique(x.rank for x in records)),
        missing = sort(unique(x.missing for x in records)),
        exact_affine_dims = sort(unique(x.exact_affine_dim for x in records)),
    )
end

function affine_dim_one_range_two_det_zero_probe(; samples = 200)
    vals = [-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0]

    x0 = quad_coeffs(a10 = 1.0)
    neg_disc = NamedTuple[]
    zero_disc = NamedTuple[]
    pos_disc = NamedTuple[]

    for _ in 1:samples
        a = rand(vals)
        b = rand(vals)
        if iszero(a) && iszero(b)
            continue
        end
        λ = rand(vals)
        e = rand(vals)
        f = rand(vals)

        c = λ * a
        d = λ * b

        # Keep only the determinant-zero / tail-rank-two slice.
        if abs(a * f - b * e) < 1e-9
            continue
        end

        u = [
            x0,
            quad_coeffs(a00 = a, a01 = b, a20 = 1.0),
            quad_coeffs(a00 = c, a01 = d, a11 = 1.0),
            quad_coeffs(a00 = e, a01 = f, a02 = 1.0),
        ]

        exact_dim = exact_affine_dim(u)
        exact_dim == 1 || continue

        disc = a^2 - a * b * f + b^2 * e
        record = (; a, b, c, d, e, f, disc, exact_affine_dim = exact_dim, image_rank_missing(u)...)

        if disc < -1e-8
            push!(neg_disc, record)
        elseif disc > 1e-8
            push!(pos_disc, record)
        else
            push!(zero_disc, record)
        end
    end

    result = (
        samples = samples,
        vals = vals,
        neg_disc = summarize(neg_disc),
        zero_disc = summarize(zero_disc),
        pos_disc = summarize(pos_disc),
    )
    println("affine_dim_one_range_two_det_zero_probe = ", result)
    result
end

function affine_dim_one_range_two_x0sq_probe()
    vals = [-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0]

    x0 = quad_coeffs(a10 = 1.0)
    x0sq = quad_coeffs(a20 = 1.0)
    nonzero_disc = NamedTuple[]
    zero_disc = NamedTuple[]

    for c in vals, d in vals, e in vals, f in vals
        u = [
            x0,
            x0sq,
            quad_coeffs(a00 = c, a01 = d, a11 = 1.0),
            quad_coeffs(a00 = e, a01 = f, a02 = 1.0),
        ]

        exact_dim = exact_affine_dim(u)
        exact_dim == 1 || continue

        disc = c^2 - c * d * f + d^2 * e
        record = (; c, d, e, f, disc, exact_affine_dim = exact_dim, image_rank_missing(u)...)

        if abs(disc) < 1e-8
            push!(zero_disc, record)
        else
            push!(nonzero_disc, record)
        end
    end

    result = (
        vals = vals,
        nonzero_disc = summarize(nonzero_disc),
        zero_disc = summarize(zero_disc),
    )
    println("affine_dim_one_range_two_x0sq_probe = ", result)
    result
end

affine_dim_one_range_two_det_zero_probe()
affine_dim_one_range_two_x0sq_probe()
