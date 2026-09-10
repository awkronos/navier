# Blender caustic reference renderer

This tool turns a browser-exported Navier velocity snapshot into a reproducible
Cycles render. Its glass tubes encode advected material paths and cast physical
refractive caustics onto matte receivers. They are an optical presentation of
the evolving velocity field, **not** a computed water surface.

## Snapshot schema

```json
{
  "schema": 1,
  "time": 1.25,
  "source": "rust-spectral-advected-material-paths",
  "coordinates": "display x,z,y; periodic box normalized to [-1,1]",
  "ior": 1.333,
  "radiusScale": 0.52,
  "receiverY": -1.22,
  "lines": [
    {
      "id": "seed-001",
      "points": [0.0, 0.0, 0.0, 0.1, 0.03, 0.02],
      "colors": [0.2, 0.7, 0.8, 0.4, 0.8, 0.7],
      "width": 0.018,
      "opacity": 0.78
    }
  ]
}
```

`points`, per-point `colors`, and optional `velocities` accept either flat
triples or arrays of three-element arrays. Optional `speeds` may replace
`velocities`; if both are present, the renderer verifies that
`speeds = |velocities|` within tolerance. Non-finite values and malformed
snapshots fail closed.

The current export explicitly supplies browser display coordinates as solver
`x,z,y`. The render applies the orientation-preserving display-to-Blender map
`(X,Y,Z) = (x,-z,y)`. One uniform normalization scale fits the field into the
portrait; the manifest records that transform.

The browser's per-point speed palette controls tube color. Tube radius is
exactly `line.width × radiusScale`, carried through the same uniform scene
scale as positions. When only velocities are present, speed supplies color;
without either colors or velocity magnitude, color stays neutral cyan. Point
spacing is never misrepresented as speed.

## Render

In the live Navier page, let the solver accumulate paths and export the exact
visible optical state from the browser console:

```js
copy(JSON.stringify(window.NavierVisuals.exportOptics()))
```

Paste that clipboard payload into a `.json` file, then render it:

```bash
/Applications/Blender.app/Contents/MacOS/Blender --background \
  --python tools/blender/render_caustics.py -- \
  --input /absolute/path/to/browser-snapshot.json \
  --output-dir /Users/schizodactyl/reports/navier-caustics-20260910
```

The default is a 1920×1080, 384-sample, denoised CPU Cycles render. The output
directory receives a 16-bit PNG, editable `.blend`, and a provenance manifest
with exact input and artifact SHA-256 hashes. `--gpu` opts into Metal after a
local smoke test; Blender 5.2's current Metal path can spend minutes compiling
this transmission-heavy scene while CPU rendering starts immediately.

The browser renderer updates its optical pass at roughly 8 Hz over paths that
continue to advect in real time. Its photon pass uses two-interface local
cylinder Snell/Fresnel transmission and HDR splatting. It does not model mutual
occlusion, endcaps, multiple bounces, or a free surface; exposure is a visual
mapping. The Blender reference replaces that local photon approximation with
closed tube meshes rendered by Cycles. It enables the native caustics caster,
receiver, and caustics-light flags for manifold next-event estimation, while
preserving the same exported paths, radius scale, IOR, receiver height, speed
colors, and light direction.

At the exported glyph radius, Cycles' MNEE contribution is physically small and
is not described as a cinematic caustic effect. `--disable-mnee` exists for a
paired validation render: with the same input, camera, sample count, and seed,
it disables only the caster/receiver/light flags. The browser's brighter HDR
photon splats intentionally expose the local-cylinder approximation to the
reader rather than claiming the same radiometric result as Cycles.
