// Direct, portable WebGPU implementation of the solver's Fourier operations.
// Complex vectors are component-major: [ux_hat, uy_hat, uz_hat].

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

@group(0) @binding(0) var<uniform> params: Params;
@group(0) @binding(1) var<storage, read> source: array<vec2<f32>>;
@group(0) @binding(2) var<storage, read> auxiliary: array<vec2<f32>>;
@group(0) @binding(3) var<storage, read_write> destination: array<vec2<f32>>;

fn complex_mul(a: vec2<f32>, b: vec2<f32>) -> vec2<f32> {
    return vec2<f32>(a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x);
}

fn point_coordinates(q: u32) -> vec3<u32> {
    let plane = params.n * params.n;
    return vec3<u32>(q / plane, (q / params.n) % params.n, q % params.n);
}

fn point_index(coordinates: vec3<u32>) -> u32 {
    return (coordinates.x * params.n + coordinates.y) * params.n + coordinates.z;
}

fn signed_frequency(index: u32) -> f32 {
    return select(f32(index) - f32(params.n), f32(index), index < params.n / 2u);
}

fn wave(q: u32) -> vec3<f32> {
    let c = point_coordinates(q);
    return vec3<f32>(signed_frequency(c.x), signed_frequency(c.y), signed_frequency(c.z));
}

fn kept(q: u32) -> bool {
    let k = abs(wave(q));
    let cutoff = f32(params.n) / 3.0;
    return all(k < vec3<f32>(cutoff));
}

fn total_values() -> u32 {
    return 3u * params.len;
}

@compute @workgroup_size(64)
fn copy_filtered(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let q = index % params.len;
    destination[index] = select(vec2<f32>(0.0), source[index], kept(q));
}

// One output Fourier coefficient per invocation. This O(N) separable DFT is
// deliberately used instead of a radix-specific kernel: it supports every
// even grid exposed by the UI and exactly matches the three-axis transform
// convention of the reference implementation. At the interactive N<=64
// grids, thousands of independent coefficient sums keep the GPU occupied.
@compute @workgroup_size(64)
fn dft_axis(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let component = index / params.len;
    let q = index % params.len;
    let output_coordinates = point_coordinates(q);
    var input_coordinates = output_coordinates;
    var output_axis = output_coordinates.x;
    if (params.axis == 1u) { output_axis = output_coordinates.y; }
    if (params.axis == 2u) { output_axis = output_coordinates.z; }
    var sum = vec2<f32>(0.0);
    for (var sample = 0u; sample < params.n; sample += 1u) {
        if (params.axis == 0u) { input_coordinates.x = sample; }
        if (params.axis == 1u) { input_coordinates.y = sample; }
        if (params.axis == 2u) { input_coordinates.z = sample; }
        let forward_twiddle = auxiliary[output_axis * params.n + sample];
        let twiddle = select(
            forward_twiddle,
            vec2<f32>(forward_twiddle.x, -forward_twiddle.y),
            params.inverse != 0u,
        );
        let input_index = component * params.len + point_index(input_coordinates);
        sum += complex_mul(source[input_index], twiddle);
    }
    if (params.inverse != 0u) { sum /= f32(params.n); }
    destination[index] = sum;
}

@compute @workgroup_size(64)
fn curl_filtered(@builtin(global_invocation_id) gid: vec3<u32>) {
    let q = gid.x;
    if (q >= params.len) { return; }
    if (!kept(q)) {
        destination[q] = vec2<f32>(0.0);
        destination[params.len + q] = vec2<f32>(0.0);
        destination[2u * params.len + q] = vec2<f32>(0.0);
        return;
    }
    let k = wave(q);
    let ux = source[q];
    let uy = source[params.len + q];
    let uz = source[2u * params.len + q];
    // i * z = (-Im z, Re z)
    let cx = k.y * uz - k.z * uy;
    let cy = k.z * ux - k.x * uz;
    let cz = k.x * uy - k.y * ux;
    destination[q] = vec2<f32>(-cx.y, cx.x);
    destination[params.len + q] = vec2<f32>(-cy.y, cy.x);
    destination[2u * params.len + q] = vec2<f32>(-cz.y, cz.x);
}

@compute @workgroup_size(64)
fn rotational_cross(@builtin(global_invocation_id) gid: vec3<u32>) {
    let q = gid.x;
    if (q >= params.len) { return; }
    let u = vec3<f32>(source[q].x, source[params.len + q].x, source[2u * params.len + q].x);
    let omega = vec3<f32>(auxiliary[q].x, auxiliary[params.len + q].x, auxiliary[2u * params.len + q].x);
    let value = cross(omega, u);
    destination[q] = vec2<f32>(value.x, 0.0);
    destination[params.len + q] = vec2<f32>(value.y, 0.0);
    destination[2u * params.len + q] = vec2<f32>(value.z, 0.0);
}

fn leray_component(q: u32, component: u32) -> vec2<f32> {
    if (!kept(q)) { return vec2<f32>(0.0); }
    let k = wave(q);
    let norm2 = dot(k, k);
    let vx = source[q];
    let vy = source[params.len + q];
    let vz = source[2u * params.len + q];
    var value = vx;
    if (component == 1u) { value = vy; }
    if (component == 2u) { value = vz; }
    if (norm2 == 0.0) { return value; }
    let pressure = (k.x * vx + k.y * vy + k.z * vz) / norm2;
    return value - k[component] * pressure;
}

@compute @workgroup_size(64)
fn project_scaled(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    destination[index] = -params.dt * leray_component(index % params.len, index / params.len);
}

@compute @workgroup_size(64)
fn project_only(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    destination[index] = leray_component(index % params.len, index / params.len);
}

fn decay(q: u32, fraction: f32) -> f32 {
    let k = wave(q);
    return exp(-fraction * params.viscosity * dot(k, k) * params.dt);
}

@compute @workgroup_size(64)
fn stage_half(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let e = decay(index % params.len, 0.5);
    destination[index] = e * (source[index] + 0.5 * auxiliary[index]);
}

@compute @workgroup_size(64)
fn stage_half_increment_outside(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let e = decay(index % params.len, 0.5);
    destination[index] = e * source[index] + 0.5 * auxiliary[index];
}

@compute @workgroup_size(64)
fn stage_full(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let q = index % params.len;
    destination[index] = decay(q, 1.0) * source[index] + decay(q, 0.5) * auxiliary[index];
}

@compute @workgroup_size(64)
fn combine_initial_a(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    let q = index % params.len;
    let e = decay(q, 1.0);
    destination[index] = e * source[index] + (e / 6.0) * auxiliary[index];
}

@compute @workgroup_size(64)
fn accumulate(@builtin(global_invocation_id) gid: vec3<u32>) {
    let index = gid.x;
    if (index >= total_values()) { return; }
    destination[index] += params.coefficient * source[index];
}
