// Exact CFL observable for a physical, component-major velocity field.
// Positive finite f32 values preserve order when bitcast to u32, allowing a
// portable atomic maximum without requiring optional shader-f32 atomics.

struct Params {
    n: u32,
    len: u32,
    axis: u32,
    inverse: u32,
    dt: f32,
    viscosity: f32,
    coefficient: f32,
    _pad: f32,
};

struct Reduction {
    max_speed_squared_bits: atomic<u32>,
    nonfinite: atomic<u32>,
};

@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> velocity: array<vec2<f32>>;
@group(0) @binding(2) var<storage, read_write> reduction: Reduction;

fn nonfinite(value: f32) -> bool {
    // Infinity and NaN both have an all-ones exponent in IEEE-754 binary32.
    return (bitcast<u32>(value) & 0x7f800000u) == 0x7f800000u;
}

@compute @workgroup_size(64)
fn reduce_max_speed(@builtin(global_invocation_id) gid: vec3<u32>) {
    let q = gid.x;
    if (q >= params.len) { return; }
    let u = vec3<f32>(
        velocity[q].x,
        velocity[params.len + q].x,
        velocity[2u * params.len + q].x,
    );
    let speed_squared = dot(u, u);
    if (nonfinite(u.x) || nonfinite(u.y) || nonfinite(u.z) || nonfinite(speed_squared)) {
        atomicStore(&reduction.nonfinite, 1u);
        return;
    }
    atomicMax(&reduction.max_speed_squared_bits, bitcast<u32>(speed_squared));
}
