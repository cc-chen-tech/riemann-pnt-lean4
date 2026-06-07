from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class PNTSample:
    x: int
    pi_x: int
    theta_x: float
    psi_x: float
    li_x: float
    psi_error: float
    pi_minus_li: float


def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []

    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    limit = math.isqrt(n)
    for candidate in range(2, limit + 1):
        if sieve[candidate]:
            start = candidate * candidate
            step = candidate
            sieve[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [value for value in range(2, n + 1) if sieve[value]]


def prime_count(n: int) -> int:
    return len(primes_up_to(n))


def chebyshev_theta(n: int) -> float:
    return sum(math.log(prime) for prime in primes_up_to(n))


def chebyshev_psi(n: int) -> float:
    total = 0.0
    for prime in primes_up_to(n):
        power = prime
        log_prime = math.log(prime)
        while power <= n:
            total += log_prime
            power *= prime
    return total


def log_integral(x: float, intervals: int = 4096) -> float:
    """Offset logarithmic integral Li(x) = integral from 2 to x of dt/log(t)."""
    if x < 2:
        raise ValueError("log_integral is defined here only for x >= 2")
    if x == 2:
        return 0.0

    if intervals % 2:
        intervals += 1
    width = (x - 2.0) / intervals

    def integrand(t: float) -> float:
        return 1.0 / math.log(t)

    total = integrand(2.0) + integrand(x)
    for index in range(1, intervals):
        coefficient = 4 if index % 2 else 2
        total += coefficient * integrand(2.0 + index * width)
    return total * width / 3.0


def sample_row(x: int) -> PNTSample:
    if x < 2:
        raise ValueError("sample points must be at least 2")

    pi_x = prime_count(x)
    theta_x = chebyshev_theta(x)
    psi_x = chebyshev_psi(x)
    li_x = log_integral(x)
    return PNTSample(
        x=x,
        pi_x=pi_x,
        theta_x=theta_x,
        psi_x=psi_x,
        li_x=li_x,
        psi_error=psi_x - x,
        pi_minus_li=pi_x - li_x,
    )


def generate_dataset(start: int, stop: int, points: int) -> list[PNTSample]:
    if start < 2:
        raise ValueError("start must be at least 2")
    if stop < start:
        raise ValueError("stop must be greater than or equal to start")
    if points < 2:
        raise ValueError("points must be at least 2")

    if start == stop:
        sample_points = [start]
    else:
        log_start = math.log(start)
        log_stop = math.log(stop)
        raw_points = [
            round(math.exp(log_start + (log_stop - log_start) * index / (points - 1)))
            for index in range(points)
        ]
        sample_points = sorted({max(start, min(stop, value)) for value in raw_points})
        sample_points[0] = start
        sample_points[-1] = stop
    return [sample_row(point) for point in sample_points]


def write_csv(rows: Iterable[PNTSample], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(PNTSample.__dataclass_fields__)
    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: getattr(row, field) for field in fieldnames})


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate PNT numerical experiment data.")
    parser.add_argument("--start", type=int, default=10)
    parser.add_argument("--stop", type=int, default=100_000)
    parser.add_argument("--points", type=int, default=40)
    parser.add_argument("--output", type=Path, default=Path("experiments/pnt/output/pnt_samples.csv"))
    args = parser.parse_args()

    rows = generate_dataset(args.start, args.stop, args.points)
    write_csv(rows, args.output)
    print(f"wrote {len(rows)} rows to {args.output}")


if __name__ == "__main__":
    main()
