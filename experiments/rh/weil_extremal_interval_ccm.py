"""Rigorous interval assembly of the CCM hypergeometric/Lerch route.

This module upgrades the CCM closed-form route of
``weil_extremal_crosscheck.assemble_ccm_closed_form`` from mpmath point values
to strict interval enclosures computed with python-flint (Arb ``arb``/``acb``
ball arithmetic with outward rounding).  It deliberately does not import the
auxiliary S/CC/XC route or the released upstream assembly script; the only
shared code is the integer-exact prime-power enumeration.

Rigour model
------------
Every matrix entry is evaluated entirely in ``arb``/``acb`` ball arithmetic at
``prec_bits`` working precision.  Arb returns each real entry as a ball
``[m - r, m + r]`` that is guaranteed to contain the exact mathematical value;
no point value plus a guessed radius is ever emitted.  The required special
functions are all provided by Arb with rigorous error bounds:

- ``acb.hypgeom_2f1``   for the 2F1(1, a_n; a_n + 1; z) blocks,
- ``acb.lerch_phi``     for the Lerch transcendent Phi(z, 2, a_n),
- ``acb.digamma`` / ``acb.polygamma`` for psi and psi_1.

Serialization to decimal ``[lo, hi]`` strings keeps the enclosure strict:

1. ``lo_seed = Decimal(value.lower().str(BOUND_PRINT_DIGITS, radius=False))``
   (and symmetrically ``hi_seed``).  Arb's decimal printing guarantees the
   printed midpoint digits are within 1 ulp at the printed scale of the exact
   dyadic bound, so the conversion error is at most
   ``10 ** (adjusted_exponent - (BOUND_PRINT_DIGITS - 1))``.
2. A ``print_slack`` term ``10 ** (e - 100)`` dominates that worst-case print
   error (``BOUND_PRINT_DIGITS = 110``) by eight orders of magnitude, including
   a possible +1 shift of the adjusted exponent between the midpoint and the
   printed bound.
3. A ``reference_margin`` term ``5 * 10 ** (e + 1 - REFERENCE_POINT_DIGITS)``
   (half an ulp at 70 significant digits, with a +1 exponent guard) widens the
   interval so that the frozen high-precision point values of
   ``groskin_2607_02828_v1_small_n_high_precision_crosscheck.json`` — which are
   serialized at ``SERIALIZED_REAL_DIGITS = 70`` — fall inside ``[lo, hi]``.
   The +1 exponent guard covers reference values whose adjusted exponent is
   one higher than the computed midpoint's (values straddling a power of ten).
   The ``print_slack`` term additionally dominates the residual mpmath
   evaluation error of the frozen reference (computed at ``high_dps = 120``,
   i.e. relative error far below ``10 ** (e - 100)``).
4. The widened bounds are rounded at ``SERIALIZED_INTERVAL_DIGITS = 85``
   significant digits with explicit directed rounding (``ROUND_FLOOR`` for
   ``lo``, ``ROUND_CEILING`` for ``hi``), so the emitted decimal strings
   satisfy ``lo <= exact_value <= hi`` unconditionally: widening a rigorous
   ball keeps it rigorous, and every approximation step above is bounded by a
   term that is provably larger.

The interval semantics of the CCM formula are identical to the pointwise
version: each line of ``assemble_ccm_interval`` mirrors the corresponding line
of ``assemble_ccm_closed_form``, with mpmath calls replaced by their Arb
counterparts.  Entrywise agreement with the frozen point values is enforced by
``tests/test_weil_interval_ccm.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_FLOOR, localcontext
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence, Tuple


SCHEMA_VERSION = "weil-extremal-kernel-interval-assembly/v1"
ROUTE = "ccm_hypergeometric_lerch"
INDEX_CONVENTION = "fourier -N..N row-major"
DEFAULT_PREC_BITS = 256
MIN_PREC_BITS = 64
BOUND_PRINT_DIGITS = 110
SERIALIZED_INTERVAL_DIGITS = 85
REFERENCE_POINT_DIGITS = 70
PRINT_SLACK_EXPONENT_DROP = 100
ARTIFACT_NAME_TEMPLATE = (
    "weil_extremal_interval_assembly_ccm_hypergeometric_lerch"
    "_c{c}_N{N}_prec{prec_bits}.json"
)
PROVENANCE_GENERATOR = "experiments/rh/weil_extremal_interval_ccm.py"
PROVENANCE_NOTE = (
    "CCM hypergeometric/Lerch closed-form route assembled in Arb ball "
    "arithmetic (acb.hypgeom_2f1, acb.lerch_phi, acb.digamma, acb.polygamma) "
    "with outward rounding; serialized bounds additionally widened by half an "
    "ulp at 70 significant digits so the frozen 70-digit pointwise "
    "cross-check values are covered."
)

Entry = Tuple[int, int]
IntervalMatrix = Dict[Entry, Any]


def _flint() -> Any:
    try:
        import flint
    except ImportError as error:
        raise RuntimeError(
            "interval assembly requires python-flint; install it in the "
            "interpreter used to execute this module"
        ) from error
    return flint


def _require_parameters(c: int, N: int, prec_bits: int) -> None:
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    if isinstance(N, bool) or not isinstance(N, int) or N < 0:
        raise ValueError("N must be a nonnegative integer")
    if (
        isinstance(prec_bits, bool)
        or not isinstance(prec_bits, int)
        or prec_bits < MIN_PREC_BITS
    ):
        raise ValueError(f"prec_bits must be an integer at least {MIN_PREC_BITS}")


def prime_powers_up_to(c: int) -> Tuple[Tuple[int, int], ...]:
    """Return ``(q, p)`` for every prime power ``q = p^a <= c``."""
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    primes = []
    for candidate in range(2, c + 1):
        if all(candidate % prime for prime in primes):
            primes.append(candidate)
    powers = []
    for prime in primes:
        value = prime
        while value <= c:
            powers.append((value, prime))
            value *= prime
    return tuple(powers)


def assemble_ccm_interval(c: int, N: int, prec_bits: int) -> IntervalMatrix:
    """Assemble all full-matrix entries as rigorous Arb real balls.

    This is the interval counterpart of
    ``weil_extremal_crosscheck.assemble_ccm_closed_form``: the same CCM
    hypergeometric/Lerch formula, evaluated in ``arb``/``acb`` ball arithmetic
    so that every returned ball strictly contains the exact entry value.
    """
    _require_parameters(c, N, prec_bits)
    flint = _flint()
    arb, acb = flint.arb, flint.acb
    previous_prec = flint.ctx.prec
    flint.ctx.prec = prec_bits
    try:
        L = arb(c).log()
        pi = arb.pi()
        z = acb((-2 * L).exp())
        quarter = arb(1) / 4
        exp_neg_half_L = (-L / 2).exp()
        exp_pos_half_L = (L / 2).exp()
        prime_powers = prime_powers_up_to(c)

        def argument(n: int) -> Any:
            return acb(quarter, pi * n / L)

        def hypergeometric(n: int) -> Any:
            a_n = argument(n)
            return z.hypgeom_2f1(1, a_n, a_n + 1)

        def alpha(n: int) -> Any:
            first = exp_neg_half_L * (
                2 * L * hypergeometric(n) / acb(L, 4 * pi * n)
            ).imag
            second = argument(n).digamma().imag / 2
            return (first + second) / pi

        def beta(n: int) -> Any:
            a_n = argument(n)
            first = -L * exp_neg_half_L * (
                2 * L * hypergeometric(n) / acb(4 * pi * n, -L)
            ).imag
            second = -exp_neg_half_L * z.lerch_phi(2, a_n).real / 4
            third = a_n.polygamma(1).real / 4
            return (first + second + third) / L

        c_w = ((exp_pos_half_L - 1) / (exp_pos_half_L + 1)).log() / 2
        c_w += (
            exp_pos_half_L.atan()
            - pi / 4
            + arb.const_euler() / 2
            + (8 * pi).log() / 2
        )
        psi_quarter = acb(quarter).digamma().real
        hypergeometric_quarter = z.hypgeom_2f1(quarter, 1, quarter + 1).real

        def gamma(n: int) -> Any:
            first = -exp_neg_half_L * (
                2 * L * hypergeometric(n) / acb(L, 4 * pi * n)
            ).real
            second = 2 * exp_neg_half_L * hypergeometric_quarter
            third = -(argument(n).digamma().real - psi_quarter) / 2
            return first + second + third + c_w

        def prime_value(n: int) -> Any:
            total = arb(0)
            for q, p in prime_powers:
                total += (
                    arb(p).log()
                    * (2 * pi * n * (1 - arb(q).log() / L)).sin()
                    / (pi * arb(q).sqrt())
                )
            return -total

        def prime_derivative(n: int) -> Any:
            total = arb(0)
            for q, p in prime_powers:
                total += (
                    arb(p).log()
                    * (1 - arb(q).log() / L)
                    * (2 * pi * n * (1 - arb(q).log() / L)).cos()
                    / arb(q).sqrt()
                )
            return -2 * total

        p0 = {n: alpha(n) + prime_value(n) for n in range(-N, N + 1)}
        p0_derivative = {
            n: -2 * (gamma(n) - beta(n)) + prime_derivative(n)
            for n in range(-N, N + 1)
        }

        sinh_quarter_L = (L / 4).sinh()
        sqrt_L = L.sqrt()

        def pole_c(n: int) -> Any:
            return sinh_quarter_L / (sqrt_L * (quarter + (2 * pi * n / L) ** 2))

        def pole_s(n: int) -> Any:
            return (
                4
                * pi
                * sinh_quarter_L
                * n
                / (L * sqrt_L * (quarter + (2 * pi * n / L) ** 2))
            )

        pole_c_values = {n: pole_c(n) for n in range(-N, N + 1)}
        pole_s_values = {n: pole_s(n) for n in range(-N, N + 1)}

        entries: IntervalMatrix = {}
        for m in range(-N, N + 1):
            for n in range(-N, N + 1):
                pole = 2 * (
                    pole_c_values[m] * pole_c_values[n]
                    - pole_s_values[m] * pole_s_values[n]
                )
                if m == n:
                    entries[(m, n)] = p0_derivative[n] + pole
                else:
                    entries[(m, n)] = (p0[m] - p0[n]) / (m - n) + pole
        return entries
    finally:
        flint.ctx.prec = previous_prec


def _decimal(value: Any) -> Decimal | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = Decimal(value)
    except (InvalidOperation, ValueError):
        return None
    return parsed if parsed.is_finite() else None


def _scale_exponent(value: Any, fallback: Decimal | None = None) -> int:
    """Adjusted decimal exponent used for serialization slack scales."""
    mid = Decimal(value.mid().str(30, radius=False))
    if not mid.is_zero():
        return mid.adjusted()
    if fallback is not None and not fallback.is_zero():
        return fallback.adjusted()
    radius = Decimal(value.rad().str(30, radius=False))
    if not radius.is_zero():
        return radius.adjusted()
    return 0


def _printed_ulp(seed: Decimal) -> Decimal:
    """One ulp at the scale of a printed decimal seed (its worst-case error).

    Arb guarantees the printed midpoint digits are correct up to +-1 in the
    last displayed digit, so one ulp at the printed scale is a proven bound on
    the binary-to-decimal conversion error of the seed.
    """
    if seed.is_zero():
        return Decimal(0)
    return Decimal(1).scaleb(seed.adjusted() - len(seed.as_tuple().digits) + 1)


def _interval_strings(value: Any) -> Tuple[str, str]:
    """Serialize an Arb ball to outward-rounded decimal ``[lo, hi]`` strings.

    The emitted decimals satisfy ``lo <= exact value <= hi``; see the module
    docstring for the slack and margin derivation.
    """
    lower_seed = Decimal(value.lower().str(BOUND_PRINT_DIGITS, radius=False))
    upper_seed = Decimal(value.upper().str(BOUND_PRINT_DIGITS, radius=False))
    exponent = _scale_exponent(value, lower_seed)
    print_slack = (
        max(_printed_ulp(lower_seed), _printed_ulp(upper_seed))
        + Decimal(1).scaleb(exponent - PRINT_SLACK_EXPONENT_DROP)
    )
    reference_margin = Decimal(5).scaleb(exponent + 1 - REFERENCE_POINT_DIGITS)
    # The widening arithmetic must run well above the serialized digit count;
    # the thread-default decimal context only carries 28 significant digits.
    with localcontext() as context:
        context.prec = BOUND_PRINT_DIGITS + 30
        raw_lo = lower_seed - print_slack - reference_margin
        raw_hi = upper_seed + print_slack + reference_margin
    with localcontext() as context:
        context.prec = SERIALIZED_INTERVAL_DIGITS
        context.rounding = ROUND_FLOOR
        lo = +raw_lo
    with localcontext() as context:
        context.prec = SERIALIZED_INTERVAL_DIGITS
        context.rounding = ROUND_CEILING
        hi = +raw_hi
    if not lo <= hi:
        raise RuntimeError("interval serialization produced lo > hi")
    return str(lo), str(hi)


def interval_entry_strings(c: int, N: int, prec_bits: int) -> List[List[str]]:
    """Return the ``(2N+1)^2`` ``[lo, hi]`` strings in row-major order."""
    flint = _flint()
    previous_prec = flint.ctx.prec
    flint.ctx.prec = prec_bits
    try:
        # Serialization must run at the assembly precision as well: Arb caps
        # the number of printed midpoint digits at the current precision, and
        # the outward-rounding slack analysis assumes BOUND_PRINT_DIGITS are
        # actually emitted.
        entries = assemble_ccm_interval(c, N, prec_bits)
        dimension = 2 * N + 1
        if len(entries) != dimension * dimension:
            raise RuntimeError("assembly returned an unexpected entry count")
        serialized: List[List[str]] = []
        for i in range(-N, N + 1):
            for j in range(-N, N + 1):
                lo, hi = _interval_strings(entries[(i, j)])
                serialized.append([lo, hi])
        return serialized
    finally:
        flint.ctx.prec = previous_prec


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _created_utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def build_interval_artifact(c: int, N: int, prec_bits: int) -> Dict[str, Any]:
    """Build the schema-v1 interval assembly artifact for one (c, N) case."""
    payload = {
        "N": N,
        "c": c,
        "dimension": 2 * N + 1,
        "entries": interval_entry_strings(c, N, prec_bits),
        "index_convention": INDEX_CONVENTION,
        "prec_bits": prec_bits,
        "provenance": {
            "created_utc": _created_utc(),
            "generator": PROVENANCE_GENERATOR,
            "note": PROVENANCE_NOTE,
        },
        "route": ROUTE,
        "schema_version": SCHEMA_VERSION,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def artifact_filename(c: int, N: int, prec_bits: int) -> str:
    return ARTIFACT_NAME_TEMPLATE.format(c=c, N=N, prec_bits=prec_bits)


def write_interval_artifact(path: str | Path, c: int, N: int, prec_bits: int) -> Dict[str, Any]:
    record = build_interval_artifact(c, N, prec_bits)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def verify_interval_artifact(record: Any) -> bool:
    required_keys = {
        "N",
        "c",
        "dimension",
        "entries",
        "index_convention",
        "payload_sha256",
        "prec_bits",
        "provenance",
        "route",
        "schema_version",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if record["schema_version"] != SCHEMA_VERSION:
        return False
    if record["route"] != ROUTE or record["index_convention"] != INDEX_CONVENTION:
        return False
    if (
        type(record["c"]) is not int
        or type(record["N"]) is not int
        or type(record["dimension"]) is not int
        or type(record["prec_bits"]) is not int
        or record["c"] < 2
        or record["N"] < 0
        or record["prec_bits"] < MIN_PREC_BITS
        or record["dimension"] != 2 * record["N"] + 1
    ):
        return False
    provenance = record["provenance"]
    if (
        not isinstance(provenance, dict)
        or set(provenance) != {"created_utc", "generator", "note"}
        or not all(isinstance(provenance[key], str) for key in provenance)
    ):
        return False
    entries = record["entries"]
    if (
        not isinstance(entries, list)
        or len(entries) != record["dimension"] ** 2
    ):
        return False
    for entry in entries:
        if (
            not isinstance(entry, list)
            or len(entry) != 2
            or not all(isinstance(bound, str) for bound in entry)
        ):
            return False
        lo = _decimal(entry[0])
        hi = _decimal(entry[1])
        if lo is None or hi is None or lo > hi:
            return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    return _payload_digest(payload) == record["payload_sha256"]


def verify_interval_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(source)
        canonical = (_canonical_json(record) + "\n").encode("utf-8")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_interval_artifact(record)


def _parse_case(value: str) -> Tuple[int, int]:
    try:
        c_text, n_text = value.split(":", 1)
        c, N = int(c_text), int(n_text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("cases must use c:N, for example 13:4") from error
    try:
        _require_parameters(c, N, MIN_PREC_BITS)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error
    return c, N


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Assemble cutoff-free Weil matrix entries as rigorous Arb intervals "
            "via the CCM hypergeometric/Lerch closed-form route."
        )
    )
    parser.add_argument("--case", action="append", type=_parse_case, required=True)
    parser.add_argument("--prec-bits", type=int, default=DEFAULT_PREC_BITS)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    _require_parameters(2, 0, args.prec_bits)
    for c, N in args.case:
        record = write_interval_artifact(
            args.output_dir / artifact_filename(c, N, args.prec_bits), c, N, args.prec_bits
        )
        widths = [
            Decimal(hi) - Decimal(lo) for lo, hi in record["entries"]
        ]
        max_width = max(widths)
        print(
            f"case (c={c}, N={N}): {len(record['entries'])} interval entries, "
            f"max width {max_width:.3e}, sha256 {record['payload_sha256'][:16]}..."
        )
    print("CCM interval assembly: wrote rigorous interval artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
