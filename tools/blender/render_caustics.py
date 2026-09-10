#!/usr/bin/env python3
"""Render a browser-exported velocity-field snapshot as refractive stream tubes.

Run through Blender, not the system Python:

  blender --background --python tools/blender/render_caustics.py -- \
    --input snapshot.json --output-dir /absolute/output/directory

The input geometry is scientific data.  The glass material and receiver are an
optical presentation of that data; they are not a reconstructed free surface.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any, Sequence

import bpy
from mathutils import Vector


BLENDER_SCRIPT_VERSION = 1
DEFAULT_IOR = 1.333


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--png", default="caustic-material-paths.png")
    parser.add_argument("--blend", default="caustic-material-paths.blend")
    parser.add_argument("--manifest", default="caustic-material-paths.manifest.json")
    parser.add_argument("--resolution-x", type=int, default=1920)
    parser.add_argument("--resolution-y", type=int, default=1080)
    parser.add_argument("--samples", type=int, default=384)
    parser.add_argument("--max-lines", type=int, default=180)
    parser.add_argument("--gpu", action="store_true", help="Opt into Metal GPU rendering")
    parser.add_argument("--cpu", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--disable-mnee", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args(sys.argv[sys.argv.index("--") + 1 :] if "--" in sys.argv else [])
    if args.resolution_x < 320 or args.resolution_y < 240:
        parser.error("render resolution is too small")
    if args.samples < 1:
        parser.error("samples must be positive")
    return args


def triples(raw: Sequence[Any], label: str) -> list[tuple[float, float, float]]:
    if not isinstance(raw, list):
        raise ValueError(f"{label} must be an array")
    if not raw:
        return []
    if isinstance(raw[0], (list, tuple)):
        if any(not isinstance(p, (list, tuple)) or len(p) != 3 for p in raw):
            raise ValueError(f"{label} nested points must all have length 3")
        values = [(float(p[0]), float(p[1]), float(p[2])) for p in raw]
    else:
        if len(raw) % 3:
            raise ValueError(f"{label} flat array length must be divisible by 3")
        values = [tuple(float(v) for v in raw[i : i + 3]) for i in range(0, len(raw), 3)]
    if any(not all(math.isfinite(x) for x in p) for p in values):
        raise ValueError(f"{label} contains a non-finite coordinate")
    return values


def scalars(raw: Any, count: int, label: str) -> list[float] | None:
    if raw is None:
        return None
    if not isinstance(raw, list) or len(raw) != count:
        raise ValueError(f"{label} must contain one finite value per point")
    values = [float(x) for x in raw]
    if any(not math.isfinite(x) or x < 0 for x in values):
        raise ValueError(f"{label} values must be finite and nonnegative")
    return values


def colors(raw: Any, count: int, label: str) -> list[tuple[float, float, float, float]] | None:
    if raw is None:
        return None
    parsed = triples(raw, label)
    if len(parsed) != count:
        raise ValueError(f"{label} must contain one RGB triple per point")
    if any(any(channel < 0.0 or channel > 1.0 for channel in rgb) for rgb in parsed):
        raise ValueError(f"{label} channels must be in [0,1]")
    return [(r, g, b, 1.0) for r, g, b in parsed]


def load_snapshot(path: Path, max_lines: int) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError("snapshot root must be an object")
    lines = payload.get("lines")
    if not isinstance(lines, list) or not lines:
        raise ValueError("snapshot.lines must be a nonempty array")
    parsed: list[dict[str, Any]] = []
    for index, item in enumerate(lines):
        if not isinstance(item, dict):
            raise ValueError(f"lines[{index}] must be an object")
        points = triples(item.get("points"), f"lines[{index}].points")
        if len(points) < 2:
            continue
        speeds = scalars(item.get("speeds"), len(points), f"lines[{index}].speeds")
        velocities_raw = item.get("velocities")
        if velocities_raw is not None:
            velocities = triples(velocities_raw, f"lines[{index}].velocities")
            if len(velocities) != len(points):
                raise ValueError(f"lines[{index}].velocities must contain one vector per point")
            derived = [math.sqrt(vx * vx + vy * vy + vz * vz) for vx, vy, vz in velocities]
            if speeds is not None and any(
                not math.isclose(a, b, rel_tol=2e-4, abs_tol=1e-8)
                for a, b in zip(speeds, derived)
            ):
                raise ValueError(f"lines[{index}] speeds disagree with velocity magnitudes")
            speeds = derived
        line_colors = colors(item.get("colors"), len(points), f"lines[{index}].colors")
        width = float(item.get("width", 0.018))
        opacity = float(item.get("opacity", 1.0))
        if not math.isfinite(width) or width <= 0:
            raise ValueError(f"lines[{index}].width must be finite and positive")
        if not math.isfinite(opacity) or not 0 <= opacity <= 1:
            raise ValueError(f"lines[{index}].opacity must be in [0,1]")
        parsed.append(
            {
                "points": points,
                "speeds": speeds,
                "colors": line_colors,
                "width": width,
                "opacity": opacity,
                "id": item.get("id", index),
            }
        )
    if not parsed:
        raise ValueError("snapshot has no lines with at least two points")
    if len(parsed) > max_lines:
        # Evenly retain coverage; this is deterministic and recorded in the manifest.
        picked = [round(i * (len(parsed) - 1) / (max_lines - 1)) for i in range(max_lines)]
        parsed = [parsed[i] for i in picked]
    time = float(payload.get("time", 0.0))
    if not math.isfinite(time):
        raise ValueError("snapshot.time must be finite")
    source = payload.get("source")
    if not isinstance(source, str) or not source.strip():
        raise ValueError("snapshot.source must be a nonempty provenance string")
    ior = float(payload.get("ior", DEFAULT_IOR))
    radius_scale = float(payload.get("radiusScale", 0.52))
    receiver_y = float(payload.get("receiverY", -1.22))
    if not math.isfinite(ior) or ior <= 1:
        raise ValueError("snapshot.ior must be finite and greater than 1")
    if not math.isfinite(radius_scale) or radius_scale <= 0:
        raise ValueError("snapshot.radiusScale must be finite and positive")
    if not math.isfinite(receiver_y):
        raise ValueError("snapshot.receiverY must be finite")
    return {
        "schema": payload.get("schema", 1),
        "time": time,
        "source": source.strip(),
        "coordinates": payload.get("coordinates", "browser x,y,z"),
        "camera": payload.get("camera"),
        "ior": ior,
        "radius_scale": radius_scale,
        "receiver_y": receiver_y,
        "lines": parsed,
        "input_lines": len(lines),
    }


def clean_scene() -> None:
    bpy.ops.object.select_all(action="SELECT")
    bpy.ops.object.delete(use_global=False)
    for datablocks in (bpy.data.curves, bpy.data.meshes, bpy.data.materials, bpy.data.cameras, bpy.data.lights):
        for block in list(datablocks):
            if block.users == 0:
                datablocks.remove(block)


def transformed_bounds(lines: list[dict[str, Any]]) -> tuple[Vector, Vector, float]:
    # Snapshot triples are browser display (x,y,z); Blender Z is vertical.
    # The +90-degree rotation about X is orientation-preserving: (X,Y,Z)=(x,-z,y).
    points = [Vector((x, -z, y)) for line in lines for x, y, z in line["points"]]
    low = Vector(tuple(min(p[i] for p in points) for i in range(3)))
    high = Vector(tuple(max(p[i] for p in points) for i in range(3)))
    extent = max(high[i] - low[i] for i in range(3))
    if extent <= 1e-12:
        raise ValueError("snapshot has zero spatial extent")
    return low, high, extent


def scene_point(point: Sequence[float], center: Vector, scale: float) -> Vector:
    x, y, z = point
    return (Vector((x, -z, y)) - center) * scale


def shader_material(
    name: str,
    color: tuple[float, float, float, float],
    *,
    transmission: float = 0.0,
    roughness: float = 0.25,
    ior: float = DEFAULT_IOR,
    emission_strength: float = 0.0,
) -> bpy.types.Material:
    material = bpy.data.materials.new(name)
    material.use_nodes = True
    material.diffuse_color = color
    nodes = material.node_tree.nodes
    principled = nodes.get("Principled BSDF")
    principled.inputs["Base Color"].default_value = color
    principled.inputs["Roughness"].default_value = roughness
    principled.inputs["IOR"].default_value = ior
    if "Transmission Weight" in principled.inputs:
        principled.inputs["Transmission Weight"].default_value = transmission
    if "Coat Weight" in principled.inputs:
        principled.inputs["Coat Weight"].default_value = 0.28 if transmission else 0.05
    if emission_strength:
        principled.inputs["Emission Color"].default_value = color
        principled.inputs["Emission Strength"].default_value = emission_strength
    return material


def velocity_glass_material(ior: float) -> bpy.types.Material:
    material = bpy.data.materials.new("Data-driven velocity glass")
    material.use_nodes = True
    nodes = material.node_tree.nodes
    links = material.node_tree.links
    nodes.clear()
    output = nodes.new("ShaderNodeOutputMaterial")
    glass = nodes.new("ShaderNodeBsdfGlass")
    color = nodes.new("ShaderNodeVertexColor")
    color.name = "Exported speed palette"
    color.layer_name = "flow_color"
    tint = nodes.new("ShaderNodeMixRGB")
    tint.name = "Optically light speed tint"
    tint.blend_type = "MIX"
    tint.inputs["Fac"].default_value = 0.34
    tint.inputs[1].default_value = (0.84, 0.97, 0.95, 1.0)
    links.new(color.outputs["Color"], tint.inputs[2])
    links.new(tint.outputs["Color"], glass.inputs["Color"])
    links.new(glass.outputs["BSDF"], output.inputs["Surface"])
    glass.distribution = "BECKMANN"
    glass.inputs["Roughness"].default_value = 0.006
    glass.inputs["IOR"].default_value = ior
    return material


def spectrum(value: float) -> tuple[float, float, float, float]:
    value = min(1.0, max(0.0, value))
    # Deep cyan -> warm gold.  Endpoints stay luminous without clipping to white.
    cold = (0.012, 0.30, 0.38)
    middle = (0.04, 0.75, 0.73)
    hot = (1.0, 0.41, 0.075)
    if value < 0.62:
        u = value / 0.62
        rgb = tuple((1.0 - u) * cold[i] + u * middle[i] for i in range(3))
    else:
        u = (value - 0.62) / 0.38
        rgb = tuple((1.0 - u) * middle[i] + u * hot[i] for i in range(3))
    return (*rgb, 1.0)


def percentile(values: list[float], fraction: float) -> float:
    values = sorted(values)
    if not values:
        return 0.0
    index = fraction * (len(values) - 1)
    lo = math.floor(index)
    hi = math.ceil(index)
    if lo == hi:
        return values[lo]
    return values[lo] * (hi - index) + values[hi] * (index - lo)


def transported_frames(points: list[Vector]) -> list[tuple[Vector, Vector]]:
    tangents: list[Vector] = []
    for index, point in enumerate(points):
        if index == 0:
            tangent = points[1] - point
        elif index == len(points) - 1:
            tangent = point - points[index - 1]
        else:
            tangent = points[index + 1] - points[index - 1]
        tangents.append(tangent.normalized())
    reference = Vector((0.0, 0.0, 1.0))
    if abs(tangents[0].dot(reference)) > 0.88:
        reference = Vector((0.0, 1.0, 0.0))
    normal = tangents[0].cross(reference).normalized()
    frames: list[tuple[Vector, Vector]] = []
    for tangent in tangents:
        projected = normal - tangent * normal.dot(tangent)
        if projected.length_squared < 1e-12:
            projected = tangent.cross(reference)
        normal = projected.normalized()
        binormal = tangent.cross(normal).normalized()
        frames.append((normal, binormal))
    return frames


def add_stream_tube(
    line: dict[str, Any],
    index: int,
    center: Vector,
    scale: float,
    radius_scale: float,
    speed_low: float,
    speed_high: float,
    material: bpy.types.Material,
    mnee: bool,
) -> None:
    speeds = line["speeds"]
    exported_colors = line["colors"]
    if exported_colors is None:
        if speeds:
            exported_colors = [
                spectrum(min(1.0, max(0.0, (value - speed_low) / max(1e-12, speed_high - speed_low))))
                for value in speeds
            ]
        else:
            exported_colors = [(0.16, 0.70, 0.72, 1.0)] * len(line["points"])

    centerline = [scene_point(point, center, scale) for point in line["points"]]
    frames = transported_frames(centerline)
    sides = 12
    # Width is the browser glyph diameter; radiusScale is its exported optical scale.
    radius = line["width"] * radius_scale * scale
    vertices: list[tuple[float, float, float]] = []
    vertex_colors: list[tuple[float, float, float, float]] = []
    for point, (normal, binormal), color in zip(centerline, frames, exported_colors):
        for side in range(sides):
            angle = math.tau * side / sides
            vertex = point + radius * (math.cos(angle) * normal + math.sin(angle) * binormal)
            vertices.append(tuple(vertex))
            vertex_colors.append(color)
    faces: list[tuple[int, ...]] = []
    for ring in range(len(centerline) - 1):
        for side in range(sides):
            nxt = (side + 1) % sides
            a = ring * sides + side
            b = ring * sides + nxt
            c = (ring + 1) * sides + nxt
            d = (ring + 1) * sides + side
            faces.append((a, b, c, d))
    faces.append(tuple(reversed(range(sides))))
    end = (len(centerline) - 1) * sides
    faces.append(tuple(end + side for side in range(sides)))

    mesh = bpy.data.meshes.new(f"Material path {index:03d}")
    mesh.from_pydata(vertices, [], faces)
    mesh.update()
    for polygon in mesh.polygons:
        polygon.use_smooth = True
    color_attribute = mesh.color_attributes.new(name="flow_color", type="FLOAT_COLOR", domain="CORNER")
    for polygon in mesh.polygons:
        for loop_index in polygon.loop_indices:
            vertex_index = mesh.loops[loop_index].vertex_index
            color_attribute.data[loop_index].color = vertex_colors[vertex_index]
    tube = bpy.data.objects.new(f"Refractive material path {index:03d}", mesh)
    bpy.context.collection.objects.link(tube)
    tube.data.materials.append(material)
    tube.cycles.is_caustics_caster = mnee
    tube["source_width"] = line["width"]
    tube["radius_scale"] = radius_scale
    tube["source_opacity"] = line["opacity"]


def add_receiver(scene_extent: float, receiver_height: float, mnee: bool) -> None:
    bpy.ops.mesh.primitive_plane_add(size=scene_extent * 8.0, location=(0.0, 0.0, receiver_height))
    receiver = bpy.context.object
    receiver.name = "Matte caustic receiver"
    receiver.cycles.is_caustics_receiver = mnee
    receiver.data.materials.append(
        shader_material("Receiver mineral black", (0.012, 0.036, 0.032, 1.0), roughness=0.22)
    )
    bevel = receiver.modifiers.new("Soft receiver edge", "BEVEL")
    bevel.width = scene_extent * 0.015
    bevel.segments = 4

def add_lighting(scene_extent: float, mnee: bool) -> None:
    # Browser optical model defines the direction from the field toward the light.
    toward_light = Vector((-0.35, -0.48, 0.82)).normalized()
    lights = [
        (
            "Caustic projector",
            "AREA",
            tuple(toward_light * 5.1),
            4200.0,
            (0.63, 0.96, 1.0),
            0.07,
        ),
        ("Warm edge", "AREA", (-2.8, 0.8, 1.65), 1050.0, (1.0, 0.29, 0.09), 0.55),
        ("Cool volume key", "POINT", (0.35, -0.45, 2.4), 460.0, (0.06, 0.55, 1.0), 0.12),
    ]
    for name, kind, loc, energy, color, size in lights:
        light_data = bpy.data.lights.new(name, type=kind)
        light_data.energy = energy
        light_data.color = color
        if kind == "AREA":
            light_data.shape = "DISK"
            light_data.size = size * scene_extent / 4.0
        else:
            light_data.shadow_soft_size = size * scene_extent / 4.0
        light_data.use_shadow = True
        light_data.cycles.is_caustics_light = mnee and name == "Caustic projector"
        obj = bpy.data.objects.new(name, light_data)
        obj.location = Vector(loc) * (scene_extent / 4.0)
        bpy.context.collection.objects.link(obj)
        if kind == "AREA":
            direction = Vector((0.0, 0.0, 0.0)) - obj.location
            obj.rotation_euler = direction.to_track_quat("-Z", "Y").to_euler()


def add_camera(
    scene_extent: float,
    data_center: Vector,
    exported_camera: dict[str, Any] | None,
) -> bpy.types.Object:
    camera_data = bpy.data.cameras.new("Data portrait camera")
    camera = bpy.data.objects.new("Data portrait camera", camera_data)
    bpy.context.collection.objects.link(camera)
    if isinstance(exported_camera, dict):
        azimuth = float(exported_camera.get("azimuth", -0.8))
        elevation = float(exported_camera.get("elevation", 0.52))
        distance = float(exported_camera.get("distance", 5.3)) * (scene_extent / 4.0) * 1.16
        # Preserve the exported orbit while reframing the data itself as a
        # standalone reference portrait rather than reproducing page margins.
        target = data_center + Vector((0.0, 0.0, scene_extent * 0.11))
        offset = Vector(
            (
                math.sin(azimuth) * math.cos(elevation),
                -math.cos(azimuth) * math.cos(elevation),
                math.sin(elevation),
            )
        ) * distance
        camera.location = target + offset
    else:
        camera.location = Vector((5.5, -7.7, 4.0)) * (scene_extent / 4.0)
        target = Vector((0.0, 0.0, -scene_extent * 0.02))
    camera.rotation_euler = (target - camera.location).to_track_quat("-Z", "Y").to_euler()
    camera_data.lens = 35
    camera_data.sensor_width = 36
    camera_data.dof.use_dof = True
    camera_data.dof.focus_object = None
    camera_data.dof.focus_distance = (camera.location - target).length
    camera_data.dof.aperture_fstop = 5.0
    return camera


def configure_render(scene: bpy.types.Scene, args: argparse.Namespace) -> dict[str, Any]:
    scene.render.resolution_x = args.resolution_x
    scene.render.resolution_y = args.resolution_y
    scene.render.resolution_percentage = 100
    scene.render.image_settings.file_format = "PNG"
    scene.render.image_settings.color_mode = "RGBA"
    scene.render.film_transparent = False
    scene.render.image_settings.color_depth = "16"

    gpu_status = "cpu"
    scene.render.engine = "CYCLES"
    scene.cycles.samples = args.samples
    scene.cycles.use_denoising = True
    scene.cycles.max_bounces = 14
    scene.cycles.diffuse_bounces = 4
    scene.cycles.glossy_bounces = 8
    scene.cycles.transmission_bounces = 12
    scene.cycles.volume_bounces = 2
    scene.cycles.transparent_max_bounces = 10
    scene.cycles.use_light_tree = True
    # Path guiding currently stalls Metal initialization in Blender 5.2; the
    # direct caustic projector is deterministic without it.
    scene.cycles.use_guiding = False
    scene.cycles.use_fast_gi = False
    scene.cycles.caustics_reflective = True
    scene.cycles.caustics_refractive = True
    scene.cycles.seed = 1701
    if args.gpu and not args.cpu:
        try:
            prefs = bpy.context.preferences.addons["cycles"].preferences
            prefs.compute_device_type = "METAL"
            prefs.get_devices()
            enabled = []
            for device in prefs.devices:
                device.use = device.type != "CPU"
                if device.use:
                    enabled.append(f"{device.name} ({device.type})")
            if enabled:
                scene.cycles.device = "GPU"
                gpu_status = ", ".join(enabled)
        except Exception as exc:  # Blender installations vary; CPU remains deterministic fallback.
            gpu_status = f"cpu fallback: {type(exc).__name__}"

    world = bpy.data.worlds.new("Ink-black optical chamber")
    scene.world = world
    world.use_nodes = True
    background = world.node_tree.nodes.get("Background")
    background.inputs["Color"].default_value = (0.0015, 0.006, 0.0065, 1.0)
    background.inputs["Strength"].default_value = 0.055

    scene.view_settings.look = "AgX - Medium High Contrast"
    scene.view_settings.exposure = -0.15

    return {"device": gpu_status, "engine": "CYCLES"}


def build(args: argparse.Namespace) -> None:
    snapshot = load_snapshot(args.input.resolve(), args.max_lines)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    output_png = (args.output_dir / args.png).resolve()
    output_blend = (args.output_dir / args.blend).resolve()
    output_manifest = (args.output_dir / args.manifest).resolve()

    clean_scene()
    scene = bpy.context.scene
    render = configure_render(scene, args)
    low, high, extent = transformed_bounds(snapshot["lines"])
    center = (low + high) * 0.5
    scale = 4.0 / extent
    scene_extent = 4.0

    all_speeds = [speed for line in snapshot["lines"] for speed in (line["speeds"] or [])]
    speed_low = percentile(all_speeds, 0.05)
    speed_high = percentile(all_speeds, 0.95)
    if math.isclose(speed_low, speed_high):
        speed_high = speed_low + 1.0
    glass = velocity_glass_material(snapshot["ior"])
    for index, line in enumerate(snapshot["lines"]):
        add_stream_tube(
            line,
            index,
            center,
            scale,
            snapshot["radius_scale"],
            speed_low,
            speed_high,
            glass,
            not args.disable_mnee,
        )

    receiver_height = scene_point((0.0, snapshot["receiver_y"], 0.0), center, scale).z
    add_receiver(scene_extent, receiver_height, not args.disable_mnee)
    add_lighting(scene_extent, not args.disable_mnee)
    camera = add_camera(scene_extent, Vector((0.0, 0.0, 0.0)), snapshot["camera"])
    scene.camera = camera
    scene.render.filepath = str(output_png)
    scene["navier_source"] = snapshot["source"]
    scene["navier_simulation_time"] = snapshot["time"]
    scene["navier_coordinate_source"] = str(snapshot["coordinates"])
    scene["navier_coordinate_transform"] = "browser display (x,y,z) -> Blender (X,Y,Z) = (x,-z,y)"
    scene["navier_optical_semantics"] = (
        "Refractive tubes optically encode exported advected material paths; they are not a solved free surface."
    )

    bpy.ops.wm.save_as_mainfile(filepath=str(output_blend), check_existing=False)
    bpy.ops.render.render(write_still=True)
    manifest = {
        "schema_version": BLENDER_SCRIPT_VERSION,
        "input": str(args.input.resolve()),
        "input_sha256": sha256(args.input.resolve()),
        "source": snapshot["source"],
        "simulation_time": snapshot["time"],
        "input_line_count": snapshot["input_lines"],
        "rendered_line_count": len(snapshot["lines"]),
        "points": sum(len(line["points"]) for line in snapshot["lines"]),
        "color_encoding": "browser-exported per-point speed palette"
        if all(line["colors"] is not None for line in snapshot["lines"])
        else (
            "derived from per-point |velocity|" if all_speeds else "neutral cyan; speed magnitude unavailable"
        ),
        "radius_encoding": "source line.width * source radiusScale * uniform scene scale",
        "coordinate_source": snapshot["coordinates"],
        "coordinate_transform": "browser display (x,y,z) -> Blender (X,Y,Z) = (x,-z,y)",
        "normalization": {"source_center": list(center), "uniform_scale": scale},
        "optics": {
            "ior": snapshot["ior"],
            "radius_scale": snapshot["radius_scale"],
            "receiver_y": snapshot["receiver_y"],
            "light_direction_toward_light_browser": [-0.35, 0.82, 0.48],
            "browser_photon_approximation": "two-interface local cylinders",
            "blender_reference": "Cycles path-traced closed tube meshes",
            "mnee_enabled": not args.disable_mnee,
        },
        "optical_semantics": (
            "Material-path tubes are evolving-flow geometry rendered with the exported IOR. "
            "Their refractive caustics are an optical encoding, not a Navier–Stokes free-surface solution."
        ),
        "render": {
            **render,
            "resolution": [args.resolution_x, args.resolution_y],
            "samples": args.samples,
            "blender": bpy.app.version_string,
        },
        "artifacts": {
            "png": str(output_png),
            "png_sha256": sha256(output_png),
            "blend": str(output_blend),
            "blend_sha256": sha256(output_blend),
        },
    }
    output_manifest.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print("NAVIER_CAUSTICS_OK " + json.dumps(manifest, separators=(",", ":")))


if __name__ == "__main__":
    try:
        build(parse_args())
    except Exception as exc:
        print(f"NAVIER_CAUSTICS_ERROR {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
