#!/usr/bin/env python3
"""Convert exact JSON certificate corpora to compact Lean input files.

This converter is deliberately untrusted: the Lean checker must reconstruct
the LP cases and validate every emitted integer multiplier. The converter
does reject malformed metadata, changed case order, and certificates rejected
by the existing exact Python verifiers.

Each output begins with one ASCII header line::

    GSCERT1 <five|six> <n> <record-count> <source-sha256>

Every remaining line is one positional certificate in canonical case order::

    scale z bound ny (y_index y_value)* nlo (lo_index lo_value)*
        nup (up_index up_value)*

All values after ``scale`` are integers. Dividing z, bound, and every sparse
multiplier by the positive per-record scale exactly recovers the source
rationals. Sparse indices are zero based and strictly increasing.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import sys
import tempfile
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
GENERALIZE = ROOT / "generalize"
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(GENERALIZE))

import five_string_lp_model as five_model  # noqa: E402
import verify_five_string_certificates as five_verifier  # noqa: E402
import six_string_lp_model as six_model  # noqa: E402
import verify_six_string_certificates_v2 as six_verifier  # noqa: E402


FIVE_METADATA = {
    "case_count": 2880,
    "format": "greedy-superstring-five-string-lp-duals-v1",
    "maximum_certificate_denominator": 12,
    "maximum_certificate_support": 20,
    "maximum_numerical_relaxed_ratio": 2.0,
    "normalization": "OPT = 1",
}
FIVE_CERTIFICATE_KEYS = {
    "dual_lower_bound",
    "equality_multiplier",
    "greedy_edge_order",
    "inequality_multipliers",
    "lower_bound_multipliers",
    "optimal_path",
    "upper_bound_multipliers",
}
SIX_HEADER = {
    "format": "greedy-superstring-six-string-lp-duals-v1",
    "n": 6,
    "normalization": "OPT=1",
    "representative_greedy_orders": 60,
    "optimal_paths_per_order": 720,
    "certificate_count": 43200,
    "covered_case_count_by_involution": 86400,
}
SIX_CERTIFICATE_KEYS = {"bound", "lo", "up", "y", "z"}


Sparse = list[tuple[int, Fraction]]
DecodedRecord = tuple[Fraction, Fraction, Sparse, Sparse, Sparse]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_fraction(encoded: object, context: str) -> Fraction:
    if not isinstance(encoded, str):
        raise ValueError(f"{context}: rational is not encoded as a string")
    try:
        value = Fraction(encoded)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f"{context}: invalid rational {encoded!r}") from error
    if str(value) != encoded:
        raise ValueError(
            f"{context}: noncanonical rational {encoded!r}; expected {str(value)!r}"
        )
    return value


def parse_sparse(
    encoded: object,
    *,
    size: int,
    sign: str,
    context: str,
) -> Sparse:
    if not isinstance(encoded, list):
        raise ValueError(f"{context}: sparse vector is not a list")
    result: Sparse = []
    previous_index = -1
    for position, entry in enumerate(encoded):
        if not isinstance(entry, list) or len(entry) != 2:
            raise ValueError(f"{context}[{position}]: expected [index, rational]")
        index, raw_value = entry
        if not isinstance(index, int) or isinstance(index, bool):
            raise ValueError(f"{context}[{position}]: index is not an integer")
        if not 0 <= index < size:
            raise ValueError(
                f"{context}[{position}]: index {index} outside 0..{size - 1}"
            )
        if index <= previous_index:
            raise ValueError(
                f"{context}[{position}]: indices are not strictly increasing"
            )
        previous_index = index
        value = parse_fraction(raw_value, f"{context}[{position}]")
        if value == 0:
            raise ValueError(f"{context}[{position}]: zero stored in sparse vector")
        if sign == "nonpositive" and value > 0:
            raise ValueError(f"{context}[{position}]: expected a nonpositive value")
        if sign == "nonnegative" and value < 0:
            raise ValueError(f"{context}[{position}]: expected a nonnegative value")
        result.append((index, value))
    return result


def integer_at_scale(value: Fraction, scale: int, context: str) -> int:
    scaled = value * scale
    if scaled.denominator != 1:
        raise AssertionError(f"{context}: scale {scale} does not clear {value}")
    return scaled.numerator


def encode_record(record: DecodedRecord, context: str) -> str:
    z, bound, y, lower, upper = record
    values: list[Fraction] = [z, bound]
    values.extend(value for _, value in y)
    values.extend(value for _, value in lower)
    values.extend(value for _, value in upper)
    scale = math.lcm(*(value.denominator for value in values))
    if scale <= 0:
        raise AssertionError(f"{context}: nonpositive scale")

    tokens = [
        str(scale),
        str(integer_at_scale(z, scale, f"{context}.z")),
        str(integer_at_scale(bound, scale, f"{context}.bound")),
    ]
    for name, entries in (("y", y), ("lo", lower), ("up", upper)):
        tokens.append(str(len(entries)))
        for index, value in entries:
            tokens.extend(
                (
                    str(index),
                    str(integer_at_scale(value, scale, f"{context}.{name}[{index}]")),
                )
            )

    line = " ".join(tokens)
    decoded = decode_record(line, context)
    if decoded != record:
        raise AssertionError(f"{context}: integer encoding failed rational round trip")
    integer_values = [
        abs(integer_at_scale(value, scale, context)) for value in values
    ]
    if math.gcd(scale, *integer_values) != 1:
        raise AssertionError(f"{context}: scale is not primitive")
    return line


def decode_record(line: str, context: str) -> DecodedRecord:
    """Decode our positional format to verify exact rational reconstruction."""
    try:
        tokens = [int(token) for token in line.split()]
    except ValueError as error:
        raise AssertionError(f"{context}: emitted a noninteger token") from error
    if len(tokens) < 6:
        raise AssertionError(f"{context}: emitted a truncated record")

    position = 0

    def take() -> int:
        nonlocal position
        if position >= len(tokens):
            raise AssertionError(f"{context}: emitted a truncated record")
        value = tokens[position]
        position += 1
        return value

    scale = take()
    if scale <= 0:
        raise AssertionError(f"{context}: emitted a nonpositive scale")
    z = Fraction(take(), scale)
    bound = Fraction(take(), scale)

    sections: list[Sparse] = []
    for name in ("y", "lo", "up"):
        count = take()
        if count < 0:
            raise AssertionError(f"{context}: emitted a negative {name} count")
        entries: Sparse = []
        previous_index = -1
        for _ in range(count):
            index = take()
            if index <= previous_index:
                raise AssertionError(
                    f"{context}: emitted non-increasing {name} indices"
                )
            previous_index = index
            entries.append((index, Fraction(take(), scale)))
        sections.append(entries)
    if position != len(tokens):
        raise AssertionError(f"{context}: emitted trailing record tokens")
    return z, bound, sections[0], sections[1], sections[2]


def convert_five(path: Path) -> tuple[list[str], int, str]:
    source_hash = sha256_file(path)
    with path.open("r", encoding="utf-8") as stream:
        payload = json.load(stream)
    if not isinstance(payload, dict):
        raise ValueError("five corpus: top-level JSON value is not an object")
    if set(payload) != set(FIVE_METADATA) | {"certificates"}:
        raise ValueError("five corpus: unexpected top-level metadata keys")
    metadata = {key: payload[key] for key in FIVE_METADATA}
    if metadata != FIVE_METADATA:
        raise ValueError(
            f"five corpus: metadata mismatch: {metadata!r} != {FIVE_METADATA!r}"
        )

    certificates = payload["certificates"]
    expected_cases = [
        (greedy_order, optimal_path)
        for greedy_order in five_model.GREEDY_EDGE_ORDERS
        for optimal_path in five_model.OPTIMAL_PATHS
    ]
    if not isinstance(certificates, list):
        raise ValueError("five corpus: certificates is not a list")
    if (
        len(certificates) != len(expected_cases)
        or len(expected_cases) != FIVE_METADATA["case_count"]
    ):
        raise ValueError("five corpus: case count disagrees with the model")

    lines: list[str] = []
    for case_index, (certificate, case) in enumerate(
        zip(certificates, expected_cases)
    ):
        context = f"five record {case_index}"
        if not isinstance(certificate, dict):
            raise ValueError(f"{context}: certificate is not an object")
        if set(certificate) != FIVE_CERTIFICATE_KEYS:
            raise ValueError(f"{context}: unexpected certificate keys")
        greedy_order, optimal_path = case
        expected_order = [
            five_model.GREEDY_PATH_EDGES.index(edge) for edge in greedy_order
        ]
        if certificate["greedy_edge_order"] != expected_order:
            raise ValueError(f"{context}: greedy order differs from case position")
        if certificate["optimal_path"] != list(optimal_path):
            raise ValueError(f"{context}: optimal path differs from case position")

        rows, _, _, _, _ = five_model.build_case(greedy_order, optimal_path)
        y = parse_sparse(
            certificate["inequality_multipliers"],
            size=len(rows),
            sign="nonpositive",
            context=f"{context}.y",
        )
        lower = parse_sparse(
            certificate["lower_bound_multipliers"],
            size=five_model.NVAR,
            sign="nonnegative",
            context=f"{context}.lo",
        )
        upper = parse_sparse(
            certificate["upper_bound_multipliers"],
            size=five_model.N,
            sign="nonpositive",
            context=f"{context}.up",
        )
        z = parse_fraction(certificate["equality_multiplier"], f"{context}.z")
        bound = parse_fraction(certificate["dual_lower_bound"], f"{context}.bound")

        five_verifier.verify_one(certificate, greedy_order, optimal_path)
        lines.append(encode_record((z, bound, y, lower, upper), context))

    return lines, len(expected_cases), source_hash


def convert_six(path: Path) -> tuple[list[str], int, str]:
    source_hash = sha256_file(path)
    if six_verifier.EXPECTED_HEADER != SIX_HEADER:
        raise ValueError("six verifier and converter disagree on expected metadata")
    if six_verifier.EXPECTED_CERTIFICATE_KEYS != SIX_CERTIFICATE_KEYS:
        raise ValueError("six verifier and converter disagree on certificate keys")
    six_verifier.verify_symmetry_reduction()

    expected_count = (
        len(six_model.REPRESENTATIVE_GREEDY_ORDERS)
        * len(six_model.OPTIMAL_PATHS)
    )
    if expected_count != SIX_HEADER["certificate_count"]:
        raise ValueError("six corpus: model dimensions disagree with metadata")

    lines: list[str] = []
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        try:
            header_line = next(stream)
        except StopIteration as error:
            raise ValueError("six corpus: empty gzip stream") from error
        try:
            header = json.loads(header_line)
        except json.JSONDecodeError as error:
            raise ValueError("six corpus: invalid JSON header") from error
        if header != SIX_HEADER:
            raise ValueError(f"six corpus: metadata mismatch: {header!r}")

        record_index = 0
        for order_index, greedy_order in enumerate(
            six_model.REPRESENTATIVE_GREEDY_ORDERS
        ):
            rows, rhs, _, objective, _ = six_model.build_case(
                greedy_order, six_model.OPTIMAL_PATHS[0]
            )
            for path_index, optimal_path in enumerate(six_model.OPTIMAL_PATHS):
                context = (
                    f"six record {record_index} "
                    f"(order {order_index}, path {path_index})"
                )
                try:
                    line = next(stream)
                except StopIteration as error:
                    raise ValueError(f"{context}: corpus ended early") from error
                try:
                    certificate = json.loads(line)
                except json.JSONDecodeError as error:
                    raise ValueError(f"{context}: invalid JSON") from error
                if not isinstance(certificate, dict):
                    raise ValueError(f"{context}: certificate is not an object")
                if set(certificate) != SIX_CERTIFICATE_KEYS:
                    raise ValueError(f"{context}: unexpected certificate keys")

                y = parse_sparse(
                    certificate["y"],
                    size=len(rows),
                    sign="nonpositive",
                    context=f"{context}.y",
                )
                lower = parse_sparse(
                    certificate["lo"],
                    size=six_model.NVAR,
                    sign="nonnegative",
                    context=f"{context}.lo",
                )
                upper = parse_sparse(
                    certificate["up"],
                    size=six_model.N,
                    sign="nonpositive",
                    context=f"{context}.up",
                )
                z = parse_fraction(certificate["z"], f"{context}.z")
                bound = parse_fraction(certificate["bound"], f"{context}.bound")

                six_verifier.verify_certificate(
                    certificate,
                    rows,
                    rhs,
                    six_verifier.equality_for_path(optimal_path),
                    objective,
                )
                lines.append(encode_record((z, bound, y, lower, upper), context))
                record_index += 1

        try:
            trailing = next(stream)
        except StopIteration:
            trailing = None
        if trailing is not None:
            raise ValueError("six corpus: trailing records after expected case count")
    if record_index != expected_count:
        raise AssertionError("six corpus: internal record-count mismatch")
    return lines, record_index, source_hash


def output_text(
    kind: str,
    n: int,
    count: int,
    source_hash: str,
    records: Sequence[str],
) -> str:
    if len(records) != count:
        raise AssertionError(f"{kind}: header count differs from record count")
    header = f"GSCERT1 {kind} {n} {count} {source_hash}"
    return "\n".join((header, *records, ""))


def atomic_write_ascii(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="ascii", newline="\n") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary_path, path)
    finally:
        if temporary_path.exists():
            temporary_path.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--five-source",
        type=Path,
        default=ROOT / "five_string_certificates.json",
    )
    parser.add_argument(
        "--six-source",
        type=Path,
        default=ROOT / "generalize" / "six_string_certificates.jsonl.gz",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=ROOT / "Lean" / "Data",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_dir = args.output_dir.resolve()
    five_records, five_count, five_source_hash = convert_five(args.five_source)
    six_records, six_count, six_source_hash = convert_six(args.six_source)

    outputs = [
        (
            "five",
            output_dir / "five.cert",
            output_text("five", 5, five_count, five_source_hash, five_records),
            five_count,
            five_source_hash,
        ),
        (
            "six",
            output_dir / "six.cert",
            output_text("six", 6, six_count, six_source_hash, six_records),
            six_count,
            six_source_hash,
        ),
    ]
    summary = {}
    for kind, path, text, count, source_hash in outputs:
        atomic_write_ascii(path, text)
        try:
            reported_path = path.relative_to(ROOT)
        except ValueError:
            reported_path = path
        summary[kind] = {
            "records": count,
            "source_sha256": source_hash,
            "output": str(reported_path),
            "output_bytes": path.stat().st_size,
            "output_sha256": sha256_file(path),
        }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
