function x1_shear(q::Vector{Float64}, t::Float64)
    a00, a10, a01, a20, a11, a02 = q
    [
        a00,
        a10 + a01 * t,
        a01,
        a20 + a11 * t + a02 * t^2,
        a11 + 2 * a02 * t,
        a02,
    ]
end

function plane_chart_data(q2::Vector{Float64}, q3::Vector{Float64})
    a20_2, a11_2, a02_2 = q2[4], q2[5], q2[6]
    a20_3, a11_3, a02_3 = q3[4], q3[5], q3[6]
    A = a11_2 * a02_3 - a02_2 * a11_3
    B = (a20_2 * a02_3 - a02_2 * a20_3) / 2
    C = a20_2 * a11_3 - a11_2 * a20_3
    d = C - B^2 / A
    (
        A = A,
        B = B,
        C = C,
        d = d,
        cross = abs(A) < 1e-9,
        common_factor = abs(d) < 1e-9,
        diagonal = abs(A) ≥ 1e-9 && abs(d) ≥ 1e-9,
    )
end

function summarize(samples)
    (
        A_values = sort(unique(round(x.A; digits = 8) for x in samples)),
        d_signs = sort(unique(sign(x.d) for x in samples)),
        all_cross_false = all(!x.cross for x in samples),
        all_common_factor_false = all(!x.common_factor for x in samples),
        all_diagonal_true = all(x.diagonal for x in samples),
    )
end

function affine_dim_one_mixed_diagonal_shear_probe(;
    t_values = [-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0],
)
    x0x1 = [0.0, 0.0, 0.0, 0.0, 1.0, 0.0]
    diffsq = [0.0, 0.0, 0.0, 1.0, 0.0, -1.0]
    sumsq = [0.0, 0.0, 0.0, 1.0, 0.0, 1.0]

    diff_samples = [
        plane_chart_data(x1_shear(x0x1, t), x1_shear(diffsq, t))
        for t in t_values
    ]
    sum_samples = [
        plane_chart_data(x1_shear(x0x1, t), x1_shear(sumsq, t))
        for t in t_values
    ]

    result = (
        t_values = t_values,
        diff = summarize(diff_samples),
        sum = summarize(sum_samples),
    )
    println("affine_dim_one_mixed_diagonal_shear_probe = ", result)
    result
end

affine_dim_one_mixed_diagonal_shear_probe()
