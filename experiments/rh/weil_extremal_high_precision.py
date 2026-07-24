"""Resumable bounded-storage high-precision Weil matrix generation.

Generation requires python-flint. Artifact verification uses only the Python
standard library and exact ``Fraction`` arithmetic.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import shutil
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from experiments.rh import weil_extremal_interval_overlap as overlap
from experiments.rh import weil_extremal_sharded as sharded


ROUTE_SCHEMA = "weil-extremal-high-precision-route-checkpoint/v1"
ROUTE_TILE_SCHEMA = "weil-extremal-high-precision-route-tile/v1"
CROSS_SCHEMA = "weil-extremal-high-precision-cross-checkpoint/v1"
CROSS_TILE_SCHEMA = "weil-extremal-high-precision-cross-tile/v1"
CLAIM_SCOPE = "finite-sharded-arb-matrix-only"
GATE_A_STATUS = "not_satisfied"
ROUTE_NAMES = sharded.ROUTE_NAMES
LEVEL_NAMES = sharded.LEVEL_NAMES
CROSS_FLAG_NAMES = sharded.CROSS_FLAG_NAMES
ROUTE_LIMITATIONS = [
    "The checkpoint records one finite sharded Arb matrix enclosure only.",
    "It contains no LDL sign result, analytic tail, or basis transfer.",
    "It makes no statement about the Riemann Hypothesis.",
]
CROSS_LIMITATIONS = [
    "Both independent formula routes use the same python-flint Arb runtime.",
    "The checkpoint certifies finite entrywise and transpose-aware intersections only.",
    "It contains no analytic tail, basis transfer, or infinite-dimensional argument.",
    "It makes no statement about the Riemann Hypothesis.",
]

BoundsAccessor = Callable[[int, int], tuple[Fraction, Fraction]]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def _canonical_bytes(value: Mapping[str, Any]) -> bytes:
    return (_canonical_json(value) + "\n").encode("ascii")


def _payload_digest(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(value).encode("ascii")).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _source_sha256() -> str:
    return _file_sha256(Path(__file__))


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _parse_fraction(value: Any) -> Fraction | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = Fraction(value)
    except (ValueError, ZeroDivisionError):
        return None
    return parsed if _format_fraction(parsed) == value else None


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def _read_json_record(path: Path) -> dict[str, Any] | None:
    try:
        raw = path.read_bytes()
        record = json.loads(
            raw,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite JSON constant: {value}")
            ),
        )
    except (OSError, TypeError, UnicodeError, ValueError):
        return None
    if not isinstance(record, dict) or raw != _canonical_bytes(record):
        return None
    digest = record.get("payload_sha256")
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    return record if isinstance(digest, str) and _payload_digest(payload) == digest else None


def _write_snapshot(
    output_dir: Path, payload: Mapping[str, Any], *, final: bool
) -> dict[str, Any]:
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    raw = _canonical_bytes(record)
    snapshot = output_dir / "checkpoints" / f"{record['payload_sha256']}.json"
    if snapshot.exists():
        if snapshot.read_bytes() != raw:
            raise ValueError("content-addressed checkpoint collision")
    else:
        _atomic_write(snapshot, raw)
    _atomic_write(output_dir / "checkpoint.json", raw)
    if final:
        _atomic_write(output_dir / "manifest.json", raw)
    return record


def _write_object(
    output_dir: Path, payload: Mapping[str, Any]
) -> dict[str, Any]:
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    raw = _canonical_bytes(record)
    compressed = sharded._deterministic_gzip(raw)
    compressed_sha256 = hashlib.sha256(compressed).hexdigest()
    relative = Path("objects") / f"{compressed_sha256}.json.gz"
    path = output_dir / relative
    if path.exists():
        if path.read_bytes() != compressed:
            raise ValueError("content-addressed tile collision")
    else:
        _atomic_write(path, compressed)
    return {
        "compressed_bytes": len(compressed),
        "compressed_sha256": compressed_sha256,
        "content_sha256": hashlib.sha256(raw).hexdigest(),
        "path": relative.as_posix(),
        "uncompressed_bytes": len(raw),
    }


def read_compressed_record(path: str | Path) -> dict[str, Any]:
    parsed = sharded._read_compressed_record(Path(path))
    if parsed is None:
        raise ValueError(f"invalid compressed record: {path}")
    return parsed[0]


def _check_disk_budget(path: Path, minimum_free_disk_bytes: int) -> None:
    if type(minimum_free_disk_bytes) is not int or minimum_free_disk_bytes < 0:
        raise ValueError("minimum_free_disk_bytes must be a nonnegative integer")
    path.mkdir(parents=True, exist_ok=True)
    free = shutil.disk_usage(path).free
    if free < minimum_free_disk_bytes:
        raise RuntimeError(
            f"free disk budget violated: {free} < {minimum_free_disk_bytes}"
        )


class PreparedRouteEvaluator:
    """An O(N)-storage formula evaluator bound to one Arb precision."""

    def __init__(
        self,
        route: str,
        entry: Callable[[int, int], Any],
        ctx: Any,
        previous_precision: int,
        prec_bits: int,
        flint_version: str,
    ) -> None:
        self.route = route
        self._entry = entry
        self._ctx = ctx
        self._previous_precision = previous_precision
        self.prec_bits = prec_bits
        self.flint_version = flint_version
        self._closed = False

    def entry(self, i: int, j: int) -> Any:
        if self._closed:
            raise RuntimeError("prepared route evaluator is closed")
        if self._ctx.prec != self.prec_bits:
            self._ctx.prec = self.prec_bits
        return self._entry(i, j)

    def close(self) -> None:
        if not self._closed:
            self._ctx.prec = self._previous_precision
            self._closed = True

    def __enter__(self) -> "PreparedRouteEvaluator":
        return self

    def __exit__(self, *_args: Any) -> None:
        self.close()


def _prepare_auxiliary(
    arb: Any, acb: Any, c: int, N: int, prec_bits: int
) -> Callable[[int, int], Any]:
    L = arb(c).log()
    pi = arb.pi()
    quarter = arb(1) / 4
    psi_quarter = quarter.digamma()
    s_values = []
    cc_values = []
    xc_values = []
    for n in range(N + 1):
        argument = acb(quarter, pi * n / L)
        psi = argument.digamma()
        trigamma = argument.polygamma(1)
        g_s, g_cc, g_xc1, g_xc2 = overlap._auxiliary_geometric_sums(
            arb, n, L, c, prec_bits
        )
        if n:
            w = 2 * pi * n / L
            s_values.append(psi.imag / 2 - w * g_s)
            cc_values.append(-(psi.real - psi_quarter) / 2 + g_cc)
        else:
            s_values.append(arb(0))
            cc_values.append(arb(0))
        xc_values.append(trigamma.real / 4 - L * g_xc1 - g_xc2)

    def signed_s(index: int) -> Any:
        return s_values[index] if index >= 0 else -s_values[-index]

    u = (L / 2).exp()
    J = -2 * (u + 1).log() + (u * u + 1).log() + 2 * u.atan()
    J += arb.const_log2() - pi / 2
    kappa = (4 * pi * ((L.exp() - 1) / (L.exp() + 1))).log()
    kappa += arb.const_euler()
    prime_powers = overlap.prime_powers_up_to(c)
    weights = [arb(p).log() / arb(q).sqrt() for q, p in prime_powers]
    positions = [arb(q).log() for q, _p in prime_powers]
    indices = range(-N, N + 1)
    prime_sines = {
        n: sum(
            (
                weight * (2 * pi * n * position / L).sin()
                for weight, position in zip(weights, positions)
            ),
            arb(0),
        )
        for n in indices
    }
    diagonal_primes = {
        n: sum(
            (
                weight
                * 2
                * (1 - position / L)
                * (2 * pi * n * position / L).cos()
                for weight, position in zip(weights, positions)
            ),
            arb(0),
        )
        for n in indices
    }
    diagonal_arch = {
        n: kappa + 2 * cc_values[abs(n)] + J - 2 * xc_values[abs(n)] / L
        for n in indices
    }
    L_squared = L * L
    pi_factor = 16 * pi * pi
    pole_prefactor = 32 * L * (L / 4).sinh() ** 2

    def entry(n: int, m: int) -> Any:
        pole = pole_prefactor * (L_squared - pi_factor * m * n)
        pole /= (L_squared + pi_factor * m * m) * (
            L_squared + pi_factor * n * n
        )
        if n == m:
            archimedean = diagonal_arch[n]
            prime = diagonal_primes[n]
        else:
            archimedean = (signed_s(m) - signed_s(n)) / (pi * (n - m))
            prime = (prime_sines[m] - prime_sines[n]) / (pi * (n - m))
        return pole - archimedean - prime

    return entry


def _prepare_ccm(
    arb: Any, acb: Any, c: int, N: int
) -> Callable[[int, int], Any]:
    L = arb(c).log()
    pi = arb.pi()
    z = arb(1) / (c * c)
    z_complex = acb(z)
    quarter = arb(1) / 4
    inverse_sqrt_c = 1 / arb(c).sqrt()
    prime_powers = overlap.prime_powers_up_to(c)
    prime_terms = tuple(
        (arb(p).log(), arb(q).log(), arb(q).sqrt())
        for q, p in prime_powers
    )
    indices = tuple(range(-N, N + 1))

    def argument(n: int) -> Any:
        return acb(quarter, pi * n / L)

    arguments = {n: argument(n) for n in indices}
    hypergeometric = {
        n: z_complex.hypgeom_2f1(
            1, arguments[n], arguments[n] + 1, abc=True
        )
        for n in indices
    }
    digamma = {n: arguments[n].digamma() for n in indices}
    trigamma_real = {
        n: arguments[n].polygamma(1).real for n in indices
    }

    def alpha(n: int) -> Any:
        quotient = 2 * L * hypergeometric[n] / acb(L, 4 * pi * n)
        return (
            inverse_sqrt_c * quotient.imag + digamma[n].imag / 2
        ) / pi

    def beta(n: int) -> Any:
        denominator = acb(4 * pi * n, -L)
        first = -L * inverse_sqrt_c * (
            2 * L * hypergeometric[n] / denominator
        ).imag
        second = (
            -inverse_sqrt_c
            * z_complex.lerch_phi(2, arguments[n]).real
            / 4
        )
        third = trigamma_real[n] / 4
        return (first + second + third) / L

    c_w = ((arb(c).sqrt() - 1) / (arb(c).sqrt() + 1)).log() / 2
    c_w += arb(c).sqrt().atan() - pi / 4
    c_w += arb.const_euler() / 2 + (8 * pi).log() / 2
    hypergeometric_zero = z_complex.hypgeom_2f1(
        quarter, 1, quarter + 1, abc=True
    )

    def gamma(n: int) -> Any:
        first = -inverse_sqrt_c * (
            2 * L * hypergeometric[n] / acb(L, 4 * pi * n)
        ).real
        second = 2 * inverse_sqrt_c * hypergeometric_zero.real
        third = -(digamma[n].real - quarter.digamma()) / 2
        return first + second + third + c_w

    def prime_value(n: int) -> Any:
        return sum(
            (
                -log_p
                * (2 * pi * n * (1 - log_q / L)).sin()
                / (pi * sqrt_q)
                for log_p, log_q, sqrt_q in prime_terms
            ),
            arb(0),
        )

    def prime_derivative(n: int) -> Any:
        return sum(
            (
                -2
                * log_p
                * (1 - log_q / L)
                * (2 * pi * n * (1 - log_q / L)).cos()
                / sqrt_q
                for log_p, log_q, sqrt_q in prime_terms
            ),
            arb(0),
        )

    p0 = {n: alpha(n) + prime_value(n) for n in indices}
    p0_derivative = {
        n: -2 * (gamma(n) - beta(n)) + prime_derivative(n) for n in indices
    }
    pole_c = {
        n: (L / 4).sinh()
        / L.sqrt()
        / (quarter + (2 * pi * n / L) ** 2)
        for n in indices
    }
    pole_s = {
        n: 4
        * pi
        * (L / 4).sinh()
        * n
        / (L * L.sqrt() * (quarter + (2 * pi * n / L) ** 2))
        for n in indices
    }

    def entry(m: int, n: int) -> Any:
        pole = 2 * (pole_c[m] * pole_c[n] - pole_s[m] * pole_s[n])
        if m == n:
            return p0_derivative[n] + pole
        return (p0[m] - p0[n]) / (m - n) + pole

    return entry


def prepare_route_evaluator(
    route: str, *, c: int, N: int, prec_bits: int
) -> PreparedRouteEvaluator:
    overlap._require_parameters(c, N, prec_bits, 30)
    if route not in ROUTE_NAMES:
        raise ValueError(f"route must be one of {ROUTE_NAMES}")
    arb, acb, ctx, flint_version = overlap._flint()
    previous_precision = ctx.prec
    ctx.prec = prec_bits
    try:
        entry = (
            _prepare_auxiliary(arb, acb, c, N, prec_bits)
            if route == "auxiliary_s_cc_xc"
            else _prepare_ccm(arb, acb, c, N)
        )
    except BaseException:
        ctx.prec = previous_precision
        raise
    return PreparedRouteEvaluator(
        route, entry, ctx, previous_precision, prec_bits, flint_version
    )


def _route_parameters(
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    python_flint_version: str,
    route: str,
    tile_size: int,
) -> dict[str, Any]:
    return {
        "N": N,
        "c": c,
        "decimal_enclosure_digits": decimal_enclosure_digits,
        "dimension": 2 * N + 1,
        "index_order": list(range(-N, N + 1)),
        "prec_bits": prec_bits,
        "python_flint_version": python_flint_version,
        "route": route,
        "tile_size": tile_size,
    }


def _route_payload(
    parameters: Mapping[str, Any], chunks: list[dict[str, Any]]
) -> dict[str, Any]:
    tiles = sharded._tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    entry_count = sum(item["entry_count"] for item in chunks)
    complete = len(chunks) == len(tiles)
    return {
        "chunks": chunks,
        "claim_scope": CLAIM_SCOPE,
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": ROUTE_LIMITATIONS,
        "parameters": dict(parameters),
        "result": {
            "complete": complete,
            "completed_tile_count": len(chunks),
            "entry_count": entry_count,
            "total_tile_count": len(tiles),
        },
        "schema_version": ROUTE_SCHEMA,
    }


def _load_route_chunks(
    output: Path, parameters: Mapping[str, Any]
) -> list[dict[str, Any]]:
    checkpoint = output / "checkpoint.json"
    if not checkpoint.exists():
        return []
    record = _read_json_record(checkpoint)
    if (
        record is None
        or not verify_route_checkpoint(record, checkpoint)
        or record["parameters"] != dict(parameters)
    ):
        raise ValueError("existing route checkpoint is incompatible or invalid")
    return list(record["chunks"])


def write_resumable_route_from_accessor(
    output_dir: str | Path,
    bounds_at: BoundsAccessor,
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    python_flint_version: str,
    route: str,
    tile_size: int,
    minimum_free_disk_bytes: int,
    max_tiles: int | None = None,
) -> dict[str, Any]:
    overlap._require_parameters(c, N, prec_bits, decimal_enclosure_digits)
    if route not in ROUTE_NAMES:
        raise ValueError(f"route must be one of {ROUTE_NAMES}")
    if type(tile_size) is not int or tile_size < 1:
        raise ValueError("tile_size must be a positive integer")
    if max_tiles is not None and (type(max_tiles) is not int or max_tiles < 1):
        raise ValueError("max_tiles must be a positive integer")
    output = Path(output_dir)
    _check_disk_budget(output, minimum_free_disk_bytes)
    parameters = _route_parameters(
        c=c,
        N=N,
        prec_bits=prec_bits,
        decimal_enclosure_digits=decimal_enclosure_digits,
        python_flint_version=python_flint_version,
        route=route,
        tile_size=tile_size,
    )
    tiles = sharded._tile_bounds(2 * N + 1, tile_size)
    chunks = _load_route_chunks(output, parameters)
    produced = 0
    for tile in tiles[len(chunks) :]:
        if max_tiles is not None and produced >= max_tiles:
            break
        _check_disk_budget(output, minimum_free_disk_bytes)
        lower_rows = []
        upper_rows = []
        for local_i, i in enumerate(
            range(tile["row_start"], tile["row_end"])
        ):
            lower_row = []
            upper_row = []
            for j in range(tile["col_start"], tile["col_end"]):
                lower, upper = bounds_at(i - N, j - N)
                if not isinstance(lower, Fraction) or not isinstance(upper, Fraction):
                    raise TypeError("bounds accessor must return Fraction endpoints")
                if lower > upper:
                    raise ValueError(
                        f"empty interval at ({i - N},{j - N})"
                    )
                lower_row.append(lower)
                upper_row.append(upper)
            lower_rows.append(lower_row)
            upper_rows.append(upper_row)
        rows = tile["row_end"] - tile["row_start"]
        columns = tile["col_end"] - tile["col_start"]
        payload = {
            "enclosure": {
                "lower": [
                    [_format_fraction(value) for value in row]
                    for row in lower_rows
                ],
                "upper": [
                    [_format_fraction(value) for value in row]
                    for row in upper_rows
                ],
            },
            "parameters": parameters,
            "result": {
                "all_intervals_nonempty": True,
                "entry_count": rows * columns,
            },
            "schema_version": ROUTE_TILE_SCHEMA,
            "tile": dict(tile),
        }
        storage = _write_object(output, payload)
        chunks.append(
            {
                **storage,
                "entry_count": rows * columns,
                "tile": dict(tile),
            }
        )
        produced += 1
        record = _write_snapshot(
            output,
            _route_payload(parameters, chunks),
            final=len(chunks) == len(tiles),
        )
    if not chunks:
        return _write_snapshot(
            output, _route_payload(parameters, chunks), final=False
        )
    return record


def generate_resumable_route(
    output_dir: str | Path,
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    route: str,
    tile_size: int,
    minimum_free_disk_bytes: int,
    max_tiles: int | None = None,
) -> dict[str, Any]:
    with prepare_route_evaluator(
        route, c=c, N=N, prec_bits=prec_bits
    ) as prepared:
        return write_resumable_route_from_accessor(
            output_dir,
            lambda i, j: overlap.arb_fraction_bounds(
                prepared.entry(i, j), decimal_enclosure_digits
            ),
            c=c,
            N=N,
            prec_bits=prec_bits,
            decimal_enclosure_digits=decimal_enclosure_digits,
            python_flint_version=prepared.flint_version,
            route=route,
            tile_size=tile_size,
            minimum_free_disk_bytes=minimum_free_disk_bytes,
            max_tiles=max_tiles,
        )


def _valid_descriptor(
    root: Path, descriptor: Any, tile: Mapping[str, int], schema: str
) -> dict[str, Any] | None:
    required = {
        "compressed_bytes",
        "compressed_sha256",
        "content_sha256",
        "entry_count",
        "path",
        "tile",
        "uncompressed_bytes",
    }
    if schema == CROSS_TILE_SCHEMA:
        required.add("result")
    if not isinstance(descriptor, dict) or set(descriptor) != required:
        return None
    expected_entries = (tile["row_end"] - tile["row_start"]) * (
        tile["col_end"] - tile["col_start"]
    )
    if (
        descriptor["tile"] != dict(tile)
        or descriptor["entry_count"] != expected_entries
        or descriptor["path"]
        != f"objects/{descriptor['compressed_sha256']}.json.gz"
    ):
        return None
    path = root / descriptor["path"]
    try:
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
    except (OSError, EOFError):
        return None
    if (
        len(compressed) != descriptor["compressed_bytes"]
        or hashlib.sha256(compressed).hexdigest()
        != descriptor["compressed_sha256"]
        or len(raw) != descriptor["uncompressed_bytes"]
        or hashlib.sha256(raw).hexdigest() != descriptor["content_sha256"]
    ):
        return None
    parsed = sharded._read_compressed_record(path)
    if parsed is None:
        return None
    record = parsed[0]
    if (
        record.get("schema_version") != schema
        or record.get("tile") != dict(tile)
    ):
        return None
    if schema == CROSS_TILE_SCHEMA and descriptor["result"] != {
        name: record.get("result", {}).get(name)
        for name in CROSS_FLAG_NAMES
    }:
        return None
    return record


def verify_route_checkpoint(
    record: Any, checkpoint_path: str | Path
) -> bool:
    required = {
        "chunks",
        "claim_scope",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
    }
    if not isinstance(record, dict) or set(record) != required:
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if (
        record["schema_version"] != ROUTE_SCHEMA
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != ROUTE_LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or _payload_digest(payload) != record["payload_sha256"]
    ):
        return False
    parameters = record["parameters"]
    if (
        not isinstance(parameters, dict)
        or parameters.get("dimension") != 2 * parameters.get("N", -1) + 1
        or parameters.get("route") not in ROUTE_NAMES
        or parameters.get("index_order")
        != list(range(-parameters["N"], parameters["N"] + 1))
    ):
        return False
    tiles = sharded._tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    chunks = record["chunks"]
    if not isinstance(chunks, list) or len(chunks) > len(tiles):
        return False
    root = Path(checkpoint_path).parent
    entry_count = 0
    for descriptor, tile in zip(chunks, tiles):
        tile_record = _valid_descriptor(
            root, descriptor, tile, ROUTE_TILE_SCHEMA
        )
        if (
            tile_record is None
            or tile_record.get("parameters") != parameters
            or tile_record.get("result")
            != {
                "all_intervals_nonempty": True,
                "entry_count": descriptor["entry_count"],
            }
        ):
            return False
        enclosure = tile_record.get("enclosure")
        rows = tile["row_end"] - tile["row_start"]
        columns = tile["col_end"] - tile["col_start"]
        lower = sharded._parse_rectangular_matrix(
            enclosure.get("lower") if isinstance(enclosure, dict) else None,
            rows,
            columns,
        )
        upper = sharded._parse_rectangular_matrix(
            enclosure.get("upper") if isinstance(enclosure, dict) else None,
            rows,
            columns,
        )
        if (
            lower is None
            or upper is None
            or any(
                lower[i][j] > upper[i][j]
                for i in range(rows)
                for j in range(columns)
            )
        ):
            return False
        entry_count += descriptor["entry_count"]
    expected = {
        "complete": len(chunks) == len(tiles),
        "completed_tile_count": len(chunks),
        "entry_count": entry_count,
        "total_tile_count": len(tiles),
    }
    return record["result"] == expected


def verify_route_checkpoint_file(path: str | Path) -> bool:
    checkpoint = Path(path)
    record = _read_json_record(checkpoint)
    return record is not None and verify_route_checkpoint(record, checkpoint)


def _load_route(path: Path) -> dict[str, Any]:
    record = _read_json_record(path)
    if (
        record is None
        or not verify_route_checkpoint(record, path)
        or record["result"]["complete"] is not True
    ):
        raise ValueError(f"route manifest is not complete and valid: {path}")
    return {
        "record": record,
        "root": path.parent,
        "manifest": path,
        "descriptors": {
            (item["tile"]["row_start"], item["tile"]["col_start"]): item
            for item in record["chunks"]
        },
    }


def _route_tile(
    source: Mapping[str, Any], row_start: int, col_start: int
) -> tuple[Any, Any]:
    descriptor = source["descriptors"][(row_start, col_start)]
    record = _valid_descriptor(
        source["root"],
        descriptor,
        descriptor["tile"],
        ROUTE_TILE_SCHEMA,
    )
    if record is None:
        raise ValueError("route tile changed after verification")
    enclosure = record["enclosure"]
    rows = descriptor["tile"]["row_end"] - descriptor["tile"]["row_start"]
    columns = descriptor["tile"]["col_end"] - descriptor["tile"]["col_start"]
    lower = sharded._parse_rectangular_matrix(
        enclosure["lower"], rows, columns
    )
    upper = sharded._parse_rectangular_matrix(
        enclosure["upper"], rows, columns
    )
    if lower is None or upper is None:
        raise ValueError("route tile enclosure is invalid")
    return lower, upper


def _cross_parameters(
    sources: Mapping[tuple[str, str], Mapping[str, Any]]
) -> dict[str, Any]:
    parameters = {
        key: source["record"]["parameters"] for key, source in sources.items()
    }
    first = parameters[("low", ROUTE_NAMES[0])]
    common = (
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "index_order",
        "python_flint_version",
        "tile_size",
    )
    if any(
        any(value[key] != first[key] for key in common)
        for value in parameters.values()
    ):
        raise ValueError("route manifests do not share matrix/grid parameters")
    for level in LEVEL_NAMES:
        for route in ROUTE_NAMES:
            if parameters[(level, route)]["route"] != route:
                raise ValueError("route manifest assigned to wrong route")
    low = parameters[("low", ROUTE_NAMES[0])]["prec_bits"]
    high = parameters[("high", ROUTE_NAMES[0])]["prec_bits"]
    if any(
        parameters[(level, route)]["prec_bits"]
        != (low if level == "low" else high)
        for level in LEVEL_NAMES
        for route in ROUTE_NAMES
    ):
        raise ValueError("route precisions differ within a level")
    if high < low + 512:
        raise ValueError("high precision must exceed low by at least 512 bits")
    return {
        "N": first["N"],
        "c": first["c"],
        "decimal_enclosure_digits": first["decimal_enclosure_digits"],
        "dimension": first["dimension"],
        "high_prec_bits": high,
        "index_order": first["index_order"],
        "low_prec_bits": low,
        "python_flint_version": first["python_flint_version"],
        "tile_size": first["tile_size"],
    }


def _cross_tile_payload(
    tile: Mapping[str, int],
    parameters: Mapping[str, Any],
    current: Mapping[tuple[str, str], tuple[Any, Any]],
    transposed: Mapping[tuple[str, str], tuple[Any, Any]],
) -> dict[str, Any]:
    rows = tile["row_end"] - tile["row_start"]
    columns = tile["col_end"] - tile["col_start"]
    bounds = {
        level: {"lower": [], "upper": []} for level in LEVEL_NAMES
    }
    flags = {name: True for name in CROSS_FLAG_NAMES}
    for local_i in range(rows):
        level_rows = {
            level: {"lower": [], "upper": []} for level in LEVEL_NAMES
        }
        for local_j in range(columns):
            symmetric = {}
            for level in LEVEL_NAMES:
                auxiliary = current[(level, ROUTE_NAMES[0])]
                ccm = current[(level, ROUTE_NAMES[1])]
                raw = (
                    max(
                        auxiliary[0][local_i][local_j],
                        ccm[0][local_i][local_j],
                    ),
                    min(
                        auxiliary[1][local_i][local_j],
                        ccm[1][local_i][local_j],
                    ),
                )
                auxiliary_t = transposed[(level, ROUTE_NAMES[0])]
                ccm_t = transposed[(level, ROUTE_NAMES[1])]
                raw_t = (
                    max(
                        auxiliary_t[0][local_j][local_i],
                        ccm_t[0][local_j][local_i],
                    ),
                    min(
                        auxiliary_t[1][local_j][local_i],
                        ccm_t[1][local_j][local_i],
                    ),
                )
                symmetric[level] = (
                    max(raw[0], raw_t[0]),
                    min(raw[1], raw_t[1]),
                )
                flags[f"all_{level}_route_entries_overlap"] &= (
                    raw[0] <= raw[1] and raw_t[0] <= raw_t[1]
                )
                flags["all_symmetric_intersections_nonempty"] &= (
                    symmetric[level][0] <= symmetric[level][1]
                )
            for route in ROUTE_NAMES:
                low = current[("low", route)]
                high = current[("high", route)]
                contained, strict = sharded._contained_and_strict(
                    low[0][local_i][local_j],
                    low[1][local_i][local_j],
                    high[0][local_i][local_j],
                    high[1][local_i][local_j],
                )
                flags["all_route_entries_contained"] &= contained
                flags["all_route_entries_strictly_narrower"] &= strict
            contained, strict = sharded._contained_and_strict(
                symmetric["low"][0],
                symmetric["low"][1],
                symmetric["high"][0],
                symmetric["high"][1],
            )
            flags["all_intersection_entries_contained"] &= contained
            flags["all_intersection_entries_strictly_narrower"] &= strict
            for level in LEVEL_NAMES:
                level_rows[level]["lower"].append(symmetric[level][0])
                level_rows[level]["upper"].append(symmetric[level][1])
        for level in LEVEL_NAMES:
            for endpoint in ("lower", "upper"):
                bounds[level][endpoint].append(level_rows[level][endpoint])
    return {
        "intersection": {
            level: {
                endpoint: [
                    [_format_fraction(value) for value in row]
                    for row in bounds[level][endpoint]
                ]
                for endpoint in ("lower", "upper")
            }
            for level in LEVEL_NAMES
        },
        "parameters": dict(parameters),
        "result": {**flags, "entry_count": rows * columns},
        "schema_version": CROSS_TILE_SCHEMA,
        "tile": dict(tile),
    }


def _source_descriptors(
    output: Path,
    sources: Mapping[tuple[str, str], Mapping[str, Any]],
) -> dict[str, Any]:
    canonical_output = output.resolve()
    return {
        level: {
            route: {
                "manifest_sha256": _file_sha256(
                    sources[(level, route)]["manifest"]
                ),
                "path": os.path.relpath(
                    sources[(level, route)]["manifest"].resolve(),
                    canonical_output,
                ),
            }
            for route in ROUTE_NAMES
        }
        for level in LEVEL_NAMES
    }


def _cross_payload(
    parameters: Mapping[str, Any],
    chunks: list[dict[str, Any]],
    source_routes: Mapping[str, Any],
) -> dict[str, Any]:
    tiles = sharded._tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    aggregate = {name: True for name in CROSS_FLAG_NAMES}
    entry_count = 0
    for descriptor in chunks:
        for name in aggregate:
            aggregate[name] &= descriptor["result"][name]
        entry_count += descriptor["entry_count"]
    complete = len(chunks) == len(tiles)
    return {
        "chunks": chunks,
        "claim_scope": CLAIM_SCOPE,
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": CROSS_LIMITATIONS,
        "parameters": dict(parameters),
        "result": {
            **aggregate,
            "complete": complete,
            "completed_tile_count": len(chunks),
            "entry_count": entry_count,
            "total_tile_count": len(tiles),
        },
        "schema_version": CROSS_SCHEMA,
        "source_routes": dict(source_routes),
    }


def write_resumable_cross_artifact(
    output_dir: str | Path,
    *,
    low_auxiliary_manifest: str | Path,
    low_ccm_manifest: str | Path,
    high_auxiliary_manifest: str | Path,
    high_ccm_manifest: str | Path,
    minimum_free_disk_bytes: int,
    max_tiles: int | None = None,
) -> dict[str, Any]:
    if max_tiles is not None and (type(max_tiles) is not int or max_tiles < 1):
        raise ValueError("max_tiles must be a positive integer")
    output = Path(output_dir)
    _check_disk_budget(output, minimum_free_disk_bytes)
    paths = {
        ("low", ROUTE_NAMES[0]): Path(low_auxiliary_manifest),
        ("low", ROUTE_NAMES[1]): Path(low_ccm_manifest),
        ("high", ROUTE_NAMES[0]): Path(high_auxiliary_manifest),
        ("high", ROUTE_NAMES[1]): Path(high_ccm_manifest),
    }
    sources = {key: _load_route(path) for key, path in paths.items()}
    parameters = _cross_parameters(sources)
    source_routes = _source_descriptors(output, sources)
    checkpoint = output / "checkpoint.json"
    chunks: list[dict[str, Any]] = []
    if checkpoint.exists():
        previous = _read_json_record(checkpoint)
        if (
            previous is None
            or not verify_cross_checkpoint(previous, checkpoint)
            or previous["parameters"] != parameters
            or previous["source_routes"] != source_routes
        ):
            raise ValueError("existing cross checkpoint is incompatible or invalid")
        chunks = list(previous["chunks"])
    tiles = sharded._tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    produced = 0
    for tile in tiles[len(chunks) :]:
        if max_tiles is not None and produced >= max_tiles:
            break
        _check_disk_budget(output, minimum_free_disk_bytes)
        row_start = tile["row_start"]
        col_start = tile["col_start"]
        current = {
            key: _route_tile(source, row_start, col_start)
            for key, source in sources.items()
        }
        transposed = {
            key: _route_tile(source, col_start, row_start)
            for key, source in sources.items()
        }
        payload = _cross_tile_payload(
            tile, parameters, current, transposed
        )
        if not all(payload["result"][name] for name in CROSS_FLAG_NAMES):
            raise ValueError(f"cross intersection failed at tile {dict(tile)}")
        storage = _write_object(output, payload)
        chunks.append(
            {
                **storage,
                "entry_count": payload["result"]["entry_count"],
                "result": {
                    name: payload["result"][name]
                    for name in CROSS_FLAG_NAMES
                },
                "tile": dict(tile),
            }
        )
        produced += 1
        record = _write_snapshot(
            output,
            _cross_payload(parameters, chunks, source_routes),
            final=len(chunks) == len(tiles),
        )
    if not chunks:
        return _write_snapshot(
            output,
            _cross_payload(parameters, chunks, source_routes),
            final=False,
        )
    return record


def _load_cross_sources(
    record: Mapping[str, Any], checkpoint: Path
) -> dict[tuple[str, str], dict[str, Any]] | None:
    try:
        return {
            (level, route): _load_route(
                (checkpoint.parent / record["source_routes"][level][route]["path"]).resolve()
            )
            for level in LEVEL_NAMES
            for route in ROUTE_NAMES
        }
    except (KeyError, OSError, ValueError):
        return None


def verify_cross_checkpoint(
    record: Any, checkpoint_path: str | Path
) -> bool:
    required = {
        "chunks",
        "claim_scope",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
        "source_routes",
    }
    if not isinstance(record, dict) or set(record) != required:
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if (
        record["schema_version"] != CROSS_SCHEMA
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != CROSS_LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or _payload_digest(payload) != record["payload_sha256"]
    ):
        return False
    checkpoint = Path(checkpoint_path)
    sources = _load_cross_sources(record, checkpoint)
    if sources is None:
        return False
    try:
        parameters = _cross_parameters(sources)
    except ValueError:
        return False
    if parameters != record["parameters"]:
        return False
    if _source_descriptors(checkpoint.parent, sources) != record["source_routes"]:
        return False
    tiles = sharded._tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    chunks = record["chunks"]
    if not isinstance(chunks, list) or len(chunks) > len(tiles):
        return False
    aggregate = {name: True for name in CROSS_FLAG_NAMES}
    entry_count = 0
    for descriptor, tile in zip(chunks, tiles):
        stored = _valid_descriptor(
            checkpoint.parent, descriptor, tile, CROSS_TILE_SCHEMA
        )
        if stored is None:
            return False
        current = {
            key: _route_tile(source, tile["row_start"], tile["col_start"])
            for key, source in sources.items()
        }
        transposed = {
            key: _route_tile(source, tile["col_start"], tile["row_start"])
            for key, source in sources.items()
        }
        expected = _cross_tile_payload(
            tile, parameters, current, transposed
        )
        expected_record = {
            **expected,
            "payload_sha256": _payload_digest(expected),
        }
        if stored != expected_record:
            return False
        for name in aggregate:
            aggregate[name] &= stored["result"][name]
        entry_count += stored["result"]["entry_count"]
    expected_result = {
        **aggregate,
        "complete": len(chunks) == len(tiles),
        "completed_tile_count": len(chunks),
        "entry_count": entry_count,
        "total_tile_count": len(tiles),
    }
    return record["result"] == expected_result and all(aggregate.values())


def verify_cross_checkpoint_file(path: str | Path) -> bool:
    checkpoint = Path(path)
    record = _read_json_record(checkpoint)
    return record is not None and verify_cross_checkpoint(record, checkpoint)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate resumable high-precision Weil shards."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    route = subparsers.add_parser("generate-route")
    route.add_argument("output_dir", type=Path)
    route.add_argument("--route", choices=ROUTE_NAMES, required=True)
    route.add_argument("--c", type=int, required=True)
    route.add_argument("--N", type=int, required=True)
    route.add_argument("--prec-bits", type=int, required=True)
    route.add_argument("--decimal-enclosure-digits", type=int, required=True)
    route.add_argument("--tile-size", type=int, default=64)
    route.add_argument("--minimum-free-disk-bytes", type=int, required=True)
    route.add_argument("--max-tiles", type=int)
    cross = subparsers.add_parser("generate-cross")
    cross.add_argument("output_dir", type=Path)
    cross.add_argument("--low-auxiliary-manifest", type=Path, required=True)
    cross.add_argument("--low-ccm-manifest", type=Path, required=True)
    cross.add_argument("--high-auxiliary-manifest", type=Path, required=True)
    cross.add_argument("--high-ccm-manifest", type=Path, required=True)
    cross.add_argument("--minimum-free-disk-bytes", type=int, required=True)
    cross.add_argument("--max-tiles", type=int)
    verify_route = subparsers.add_parser("verify-route")
    verify_route.add_argument("checkpoint", type=Path)
    verify_cross = subparsers.add_parser("verify-cross")
    verify_cross.add_argument("checkpoint", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    if args.command == "generate-route":
        record = generate_resumable_route(
            args.output_dir,
            c=args.c,
            N=args.N,
            prec_bits=args.prec_bits,
            decimal_enclosure_digits=args.decimal_enclosure_digits,
            route=args.route,
            tile_size=args.tile_size,
            minimum_free_disk_bytes=args.minimum_free_disk_bytes,
            max_tiles=args.max_tiles,
        )
        print(
            "route tiles: "
            f"{record['result']['completed_tile_count']}/"
            f"{record['result']['total_tile_count']}"
        )
        return 0
    if args.command == "generate-cross":
        record = write_resumable_cross_artifact(
            args.output_dir,
            low_auxiliary_manifest=args.low_auxiliary_manifest,
            low_ccm_manifest=args.low_ccm_manifest,
            high_auxiliary_manifest=args.high_auxiliary_manifest,
            high_ccm_manifest=args.high_ccm_manifest,
            minimum_free_disk_bytes=args.minimum_free_disk_bytes,
            max_tiles=args.max_tiles,
        )
        print(
            "cross tiles: "
            f"{record['result']['completed_tile_count']}/"
            f"{record['result']['total_tile_count']}"
        )
        return 0
    valid = (
        verify_route_checkpoint_file(args.checkpoint)
        if args.command == "verify-route"
        else verify_cross_checkpoint_file(args.checkpoint)
    )
    print(f"valid high-precision checkpoint: {str(valid).lower()}")
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
