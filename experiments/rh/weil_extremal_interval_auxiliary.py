"""Rigorous interval assembly of the auxiliary S/CC/XC closed-form route.

This is the Gate A interval upgrade of
``weil_extremal_crosscheck.assemble_auxiliary_closed_form``.  The matrix-entry
formula semantics are unchanged; only the arithmetic layer is replaced by
python-flint ``arb``/``acb`` ball arithmetic:

* every constant (pi, log c, Euler--Mascheroni, digamma(1/4), prime-power
  logarithms, ...) is constructed as an ``arb`` ball;
* complex digamma/trigamma values are ``acb`` balls;
* the four exponentially convergent geometric tails are truncated with a
  *rigorous* tail bound derived from the exact geometric ratio exp(-2L):
  for c_k = 2k + 1/2, rho = exp(-2L) and any K >= 1,

      sum_{k>=K} exp(-c_k L)/c_k^2  <=  exp(-c_K L)/(c_K^2 (1-rho)),
      sum_{k>=K} exp(-c_k L)/c_k    <=  exp(-c_K L)/(c_K (1-rho)),

  because c_{k+1} = c_k + 2 implies the term ratio is at most rho.  The
  residual ball arb(0, R) with R a certified rational upper bound of the
  right-hand side is added to each truncated sum;
* each matrix entry is exported as an outward-rounded decimal interval
  [lo, hi].  Export extracts the exact dyadic midpoint and a certified
  rational upper bound of the radius via ``arb.man_exp`` and rounds lo
  toward -infinity and hi toward +infinity at a fixed significant-digit
  count, so no point value is ever disguised as an interval.

Artifact schema: ``weil-extremal-kernel-interval-assembly/v1``.  ``prec_bits``
is the nominal certificate precision requested on the CLI; the computation
runs at ``prec_bits + 64`` working bits so the emitted radii are certified at
a level finer than the nominal precision.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Sequence, Tuple

import flint
from flint import arb, acb, ctx, fmpq


SCHEMA_VERSION = "weil-extremal-kernel-interval-assembly/v1"
ROUTE = "auxiliary_closed_form_interval_arb"
INDEX_CONVENTION = "fourier -N..N row-major"
SERIALIZED_INTERVAL_DIGITS = 80
WORKING_GUARD_BITS = 64
TAIL_GUARD_BITS = 96
MAX_GEOMETRIC_TERMS = 200000
GENERATOR = "experiments/rh/weil_extremal_interval_auxiliary.py"
PROVENANCE_NOTE = (
    "Interval (ball-arithmetic) assembly of the auxiliary S/CC/XC closed-form "
    "route; formula semantics identical to assemble_auxiliary_closed_form in "
    "experiments/rh/weil_extremal_crosscheck.py. Computed with python-flint "
    f"{flint.__version__} arb/acb at prec_bits+64 working bits; geometric tails "
    "truncated with rigorous exp(-2L)-ratio bounds; interval endpoints exported "
    "by outward rounding of exact dyadic ball bounds to "
    f"{SERIALIZED_INTERVAL_DIGITS} significant decimal digits."
)

Entry = Tuple[int, int]
IntervalMatrix = Dict[Entry, Any]


def _require_parameters(c: int, N: int, prec_bits: int) -> None:
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    if isinstance(N, bool) or not isinstance(N, int) or N < 0:
        raise ValueError("N must be a nonnegative integer")
    if isinstance(prec_bits, bool) or not isinstance(prec_bits, int) or prec_bits < 64:
        raise ValueError("prec_bits must be an integer at least 64")


def prime_powers_up_to(c: int) -> Tuple[Tuple[int, int], ...]:
    """Return ``(q, p)`` for every prime power ``q = p^a <= c``.

    This must stay semantically identical to the helper in
    ``weil_extremal_crosscheck.py``; it is duplicated so this module remains a
    self-contained interval route.
    """
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


# ---------------------------------------------------------------------------
# Exact ball introspection and outward-rounded decimal export.
# ---------------------------------------------------------------------------


def _pow2(exponent: int) -> Fraction:
    return Fraction(2) ** exponent


def _exact_fraction(point: Any) -> Fraction:
    """Exact rational value of a radius-zero ``arb`` (its dyadic midpoint)."""
    mantissa, exponent = point.man_exp()
    return Fraction(int(mantissa)) * _pow2(int(exponent))


def _certified_radius(x: Any) -> Fraction:
    """Certified rational upper bound of the radius of an ``arb`` ball.

    ``arb.rad()`` returns a ball containing the true radius; its own radius is
    bounded by the next nesting level with a factor-4 margin, which dominates
    the geometric sum of all deeper nesting levels (each mag mantissa carries
    30 bits, so deeper levels shrink by at least 2^-29 per level).
    """
    rad = x.rad()
    rad_mid = _exact_fraction(rad.mid())
    rad_rad = _exact_fraction(rad.rad().mid())
    return rad_mid + 4 * rad_rad


def _certified_upper(x: Any) -> Fraction:
    """Certified rational upper bound of an ``arb`` ball."""
    return _exact_fraction(x.mid()) + _certified_radius(x)


def _decimal_outward(value: Fraction, digits: int, round_up: bool) -> str:
    """Decimal string of ``value`` rounded outward at ``digits`` sig digits."""
    if value == 0:
        return "0"
    rounding = ROUND_CEILING if round_up else ROUND_FLOOR
    with localcontext() as context:
        context.prec = digits + 25
        context.rounding = rounding
        quotient = Decimal(value.numerator) / Decimal(value.denominator)
        quantum = Decimal(1).scaleb(quotient.adjusted() - digits + 1)
        rounded = quotient.quantize(quantum, rounding=rounding)
    return str(rounded).replace("E", "e")


def _export_ball(x: Any, digits: int = SERIALIZED_INTERVAL_DIGITS) -> Tuple[str, str]:
    """Export an ``arb`` ball as outward-rounded decimal strings [lo, hi]."""
    midpoint = _exact_fraction(x.mid())
    radius = _certified_radius(x)
    lo = _decimal_outward(midpoint - radius, digits, round_up=False)
    hi = _decimal_outward(midpoint + radius, digits, round_up=True)
    return lo, hi


# ---------------------------------------------------------------------------
# Interval assembly of the auxiliary closed form.
# ---------------------------------------------------------------------------


def _geometric_sums_interval(n: int, L: Any, tail_target: Fraction) -> Tuple[Any, Any, Any, Any]:
    """Interval version of the four exponentially convergent geometric tails.

    Same summands as ``weil_extremal_crosscheck._geometric_sums``; the tail
    beyond the truncation index is enclosed by the rigorous exp(-2L)-ratio
    bound documented in the module docstring.
    """
    pi = arb.pi()
    w = 2 * pi * n / L
    w_squared = w * w
    sums = [arb(0) for _ in range(4)]
    rho = (-2 * L).exp()
    one_minus_rho = 1 - rho
    for k in range(MAX_GEOMETRIC_TERMS):
        c_k = arb(4 * k + 1) / 2
        exponential = (-c_k * L).exp()
        denominator = c_k * c_k + w_squared
        sums[0] += exponential / denominator
        # For n == 0, w_squared is exactly zero, so these summands vanish
        # exactly, matching the skipped accumulation in the mpmath route.
        sums[1] += exponential * w_squared / (c_k * denominator)
        sums[2] += exponential * c_k / denominator
        sums[3] += exponential * (c_k * c_k - w_squared) / (denominator * denominator)
        if k >= 2:
            # Tail k+1..infinity: c_next = c_k + 2 >= 6.5 > 1, so
            # sum_{j>=K} exp(-c_j L)/c_j^s <= exp(-c_K L)/(c_K^s (1-rho)).
            c_next = c_k + 2
            tail_exponential = (-c_next * L).exp()
            base = tail_exponential / (c_next * c_next * one_minus_rho)
            bounds = (
                base,  # sum exp(-cL)/(c^2+w^2) <= sum exp(-cL)/c^2
                base * w_squared / c_next,  # <= w^2 sum exp(-cL)/c^3
                base * c_next,  # <= sum exp(-cL)/c
                base,  # |c^2-w^2|/(c^2+w^2)^2 <= 1/c^2
            )
            if all(_certified_upper(bound) < tail_target for bound in bounds):
                for total, bound in zip(sums, bounds):
                    radius = _certified_upper(bound)
                    total += arb(0, fmpq(radius.numerator, radius.denominator))
                return tuple(sums)
    raise RuntimeError("geometric sums did not reach the requested interval target")


def assemble_auxiliary_interval(c: int, N: int, prec_bits: int) -> IntervalMatrix:
    """Assemble all full-matrix entries as rigorous ``arb`` balls.

    Formula semantics are identical to
    ``weil_extremal_crosscheck.assemble_auxiliary_closed_form``; every
    operation is interval arithmetic at ``prec_bits + 64`` working bits.
    """
    _require_parameters(c, N, prec_bits)
    tail_target = Fraction(2) ** (-(prec_bits + TAIL_GUARD_BITS))
    previous_prec = ctx.prec
    ctx.prec = prec_bits + WORKING_GUARD_BITS
    try:
        L = arb(c).log()
        pi = arb.pi()
        quarter = arb(1) / 4
        psi_quarter = quarter.digamma()
        s_values = []
        cc_values = []
        xc_values = []
        for n in range(N + 1):
            w = 2 * pi * n / L
            argument = acb(quarter, pi * n / L)
            psi = argument.digamma()
            trigamma = argument.polygamma(1)
            g_s, g_cc, g_xc1, g_xc2 = _geometric_sums_interval(n, L, tail_target)
            if n:
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
        J += arb(2).log() - pi / 2
        kappa = (4 * pi * (L.exp() - 1) / (L.exp() + 1)).log() + arb.const_euler()
        prime_powers = prime_powers_up_to(c)
        weights = [arb(p).log() / arb(q).sqrt() for q, p in prime_powers]
        positions = [arb(q).log() for q, _ in prime_powers]

        entries = {}
        L_squared = L * L
        pi_factor = 16 * pi * pi
        pole_prefactor = 32 * L * (L / 4).sinh() ** 2
        for n in range(-N, N + 1):
            for m in range(-N, N + 1):
                pole = pole_prefactor * (L_squared - pi_factor * m * n)
                pole /= (L_squared + pi_factor * m * m) * (
                    L_squared + pi_factor * n * n
                )
                if n == m:
                    archimedean = (
                        kappa
                        + 2 * cc_values[abs(n)]
                        + J
                        - 2 * xc_values[abs(n)] / L
                    )
                else:
                    archimedean = (signed_s(m) - signed_s(n)) / (pi * (n - m))
                prime = arb(0)
                for weight, position in zip(weights, positions):
                    if n == m:
                        prime += (
                            weight
                            * 2
                            * (1 - position / L)
                            * (2 * pi * n * position / L).cos()
                        )
                    else:
                        prime += (
                            weight
                            * (
                                (2 * pi * m * position / L).sin()
                                - (2 * pi * n * position / L).sin()
                            )
                            / (pi * (n - m))
                        )
                entries[(n, m)] = pole - archimedean - prime
        return entries
    finally:
        ctx.prec = previous_prec


# ---------------------------------------------------------------------------
# Artifact construction, verification, and CLI.
# ---------------------------------------------------------------------------


def artifact_filename(c: int, N: int, prec_bits: int) -> str:
    return (
        f"weil_extremal_interval_{ROUTE}_c{c}_N{N}_prec{prec_bits}.json"
    )


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def build_interval_artifact(c: int, N: int, prec_bits: int) -> Dict[str, Any]:
    """Assemble the interval matrix and wrap it in the v1 artifact schema."""
    _require_parameters(c, N, prec_bits)
    matrix = assemble_auxiliary_interval(c, N, prec_bits)
    dimension = 2 * N + 1
    entries = []
    for n in range(-N, N + 1):
        for m in range(-N, N + 1):
            lo, hi = _export_ball(matrix[(n, m)])
            entries.append([lo, hi])
    payload = {
        "c": c,
        "N": N,
        "dimension": dimension,
        "entries": entries,
        "index_convention": INDEX_CONVENTION,
        "prec_bits": prec_bits,
        "provenance": {
            "created_utc": datetime.now(timezone.utc)
            .isoformat(timespec="seconds")
            .replace("+00:00", "Z"),
            "generator": GENERATOR,
            "note": PROVENANCE_NOTE,
        },
        "route": ROUTE,
        "schema_version": SCHEMA_VERSION,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_interval_artifact(path: str | Path, c: int, N: int, prec_bits: int) -> Dict[str, Any]:
    record = build_interval_artifact(c, N, prec_bits)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def _is_decimal_string(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    try:
        return Decimal(value).is_finite()
    except (InvalidOperation, ValueError):
        return False


def verify_interval_artifact(record: Any) -> bool:
    """Structural verification of a v1 interval-assembly artifact."""
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
    if (
        record["schema_version"] != SCHEMA_VERSION
        or record["route"] != ROUTE
        or record["index_convention"] != INDEX_CONVENTION
        or type(record["c"]) is not int
        or type(record["N"]) is not int
        or type(record["dimension"]) is not int
        or type(record["prec_bits"]) is not int
        or record["c"] < 2
        or record["N"] < 0
        or record["prec_bits"] < 64
        or record["dimension"] != 2 * record["N"] + 1
        or not isinstance(record["entries"], list)
        or len(record["entries"]) != record["dimension"] ** 2
    ):
        return False
    provenance = record["provenance"]
    if not isinstance(provenance, dict) or set(provenance) != {
        "created_utc",
        "generator",
        "note",
    }:
        return False
    if not all(isinstance(provenance[key], str) for key in provenance):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if _payload_digest(payload) != record["payload_sha256"]:
        return False
    for entry in record["entries"]:
        if (
            not isinstance(entry, list)
            or len(entry) != 2
            or not all(_is_decimal_string(bound) for bound in entry)
        ):
            return False
        if Decimal(entry[0]) > Decimal(entry[1]):
            return False
    return True


def verify_interval_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(source)
        canonical = (_canonical_json(record) + "\n").encode("utf-8")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_interval_artifact(record)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Assemble the cutoff-free Weil matrix through the auxiliary S/CC/XC "
            "closed form in rigorous arb interval arithmetic."
        )
    )
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec-bits", type=int, default=256)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_interval_artifact(args.out, args.c, args.N, args.prec_bits)
    widths = [
        Decimal(hi) - Decimal(lo) for lo, hi in record["entries"]
    ]
    max_width = max(widths)
    print(
        "interval auxiliary assembly: "
        f"c={args.c} N={args.N} prec_bits={args.prec_bits} "
        f"entries={len(record['entries'])} max_radius={max_width / 2:.3e} "
        f"-> {args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
