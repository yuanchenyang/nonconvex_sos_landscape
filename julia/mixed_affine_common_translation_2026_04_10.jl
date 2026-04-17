using Random

Random.seed!(20260410)

"""
Probe the common-translation idea for mixed-affine pairs.

For random quadratic pairs
  q_i = a_i*x0^2 + b_i*x0*x1 + c_i*x1^2 + e_i*x1
with determinant A = b2*c3 - c2*b3 nonzero, solve
  e_i + b_i*u + 2*c_i*v = 0
for a common translation (x0,x1) -> (x0+u, x1+v), and report the residual tail
error.
"""

function tail_kill_probe(samples::Int = 20)
    max_tail_error = 0.0
    min_abs_det = Inf
    values = NamedTuple[]
    for _ in 1:samples
        local a2, b2, c2, e2, a3, b3, c3, e3, det
        while true
            a2, b2, c2, e2 = randn(), randn(), randn(), randn()
            a3, b3, c3, e3 = randn(), randn(), randn(), randn()
            det = b2 * c3 - c2 * b3
            if abs(det) > 1e-6
                break
            end
        end
        u = (c2 * e3 - c3 * e2) / det
        v = (b3 * e2 - b2 * e3) / (2 * det)
        tail2 = e2 + b2 * u + 2 * c2 * v
        tail3 = e3 + b3 * u + 2 * c3 * v
        err = max(abs(tail2), abs(tail3))
        max_tail_error = max(max_tail_error, err)
        min_abs_det = min(min_abs_det, abs(det))
        push!(values, (det = det, u = u, v = v, tail2 = tail2, tail3 = tail3, err = err))
    end
    println(
        "mixed_affine_common_translation_probe = ",
        "(samples = ", samples,
        ", max_tail_error = ", max_tail_error,
        ", min_abs_det = ", min_abs_det,
        ", values = ", values, ")",
    )
end

tail_kill_probe()
