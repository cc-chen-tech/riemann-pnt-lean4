from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Graph:
    vertices: int
    edges: frozenset[tuple[int, int]]


def _edge(a: int, b: int) -> tuple[int, int]:
    if a == b:
        raise ValueError("loops are not supported")
    return (a, b) if a < b else (b, a)


def complete_graph(vertices: int) -> Graph:
    return Graph(vertices=vertices, edges=frozenset(combinations(range(vertices), 2)))


def empty_graph(vertices: int) -> Graph:
    return Graph(vertices=vertices, edges=frozenset())


def contains_clique(graph: Graph, size: int) -> bool:
    for subset in combinations(range(graph.vertices), size):
        if all(_edge(a, b) in graph.edges for a, b in combinations(subset, 2)):
            return True
    return False


def contains_independent_set(graph: Graph, size: int) -> bool:
    for subset in combinations(range(graph.vertices), size):
        if all(_edge(a, b) not in graph.edges for a, b in combinations(subset, 2)):
            return True
    return False


def find_counterexample(vertices: int, clique_size: int, independent_size: int) -> Graph | None:
    all_edges = list(combinations(range(vertices), 2))
    for mask in range(1 << len(all_edges)):
        graph = Graph(
            vertices=vertices,
            edges=frozenset(edge for index, edge in enumerate(all_edges) if mask & (1 << index)),
        )
        if not contains_clique(graph, clique_size) and not contains_independent_set(graph, independent_size):
            return graph
    return None


def _certificate_for_graph(graph: Graph, clique_size: int, independent_size: int) -> dict[str, Any]:
    has_clique = contains_clique(graph, clique_size)
    has_independent_set = contains_independent_set(graph, independent_size)
    return {
        "vertices": graph.vertices,
        "edges": [[a, b] for a, b in sorted(graph.edges)],
        "clique_size": clique_size,
        "independent_size": independent_size,
        "has_clique": has_clique,
        "has_independent_set": has_independent_set,
        "is_counterexample": not has_clique and not has_independent_set,
    }


def export_certificate(
    graph: Graph, clique_size: int, independent_size: int, path: str | Path
) -> dict[str, Any]:
    certificate = _certificate_for_graph(graph, clique_size, independent_size)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    return certificate


def load_certificate(path: str | Path) -> dict[str, Any]:
    certificate = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(certificate, dict):
        raise ValueError("Ramsey certificate must be a JSON object")
    return certificate


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def verify_certificate(certificate: Any) -> bool:
    required_keys = {
        "vertices",
        "edges",
        "clique_size",
        "independent_size",
        "has_clique",
        "has_independent_set",
        "is_counterexample",
    }
    if not isinstance(certificate, dict) or set(certificate) != required_keys:
        return False

    vertices = certificate["vertices"]
    clique_size = certificate["clique_size"]
    independent_size = certificate["independent_size"]
    if not _is_int(vertices) or not _is_int(clique_size) or not _is_int(independent_size):
        return False
    if vertices < 0 or clique_size < 0 or independent_size < 0:
        return False
    if not isinstance(certificate["has_clique"], bool):
        return False
    if not isinstance(certificate["has_independent_set"], bool):
        return False
    if not isinstance(certificate["is_counterexample"], bool):
        return False

    raw_edges = certificate["edges"]
    if not isinstance(raw_edges, list):
        return False

    edges: set[tuple[int, int]] = set()
    for raw_edge in raw_edges:
        if not isinstance(raw_edge, list) or len(raw_edge) != 2:
            return False
        a, b = raw_edge
        if not _is_int(a) or not _is_int(b):
            return False
        if a < 0 or b < 0 or a >= vertices or b >= vertices or a == b:
            return False
        edge = _edge(a, b)
        if edge in edges:
            return False
        edges.add(edge)

    graph = Graph(vertices=vertices, edges=frozenset(edges))
    actual_has_clique = contains_clique(graph, clique_size)
    actual_has_independent_set = contains_independent_set(graph, independent_size)
    actual_is_counterexample = not actual_has_clique and not actual_has_independent_set
    return (
        certificate["has_clique"] is actual_has_clique
        and certificate["has_independent_set"] is actual_has_independent_set
        and certificate["is_counterexample"] is actual_is_counterexample
    )


def _format_graph(graph: Graph | None) -> str:
    if graph is None:
        return "none"
    return " ".join(f"{a}-{b}" for a, b in sorted(graph.edges))


def main() -> None:
    parser = argparse.ArgumentParser(description="Search for small Ramsey counterexample graphs.")
    parser.add_argument("--vertices", type=int, default=5)
    parser.add_argument("--clique-size", type=int, default=3)
    parser.add_argument("--independent-size", type=int, default=3)
    parser.add_argument("--certificate-output", type=Path)
    args = parser.parse_args()

    graph = find_counterexample(args.vertices, args.clique_size, args.independent_size)
    if graph is not None and args.certificate_output is not None:
        export_certificate(graph, args.clique_size, args.independent_size, args.certificate_output)
    print(_format_graph(graph))


if __name__ == "__main__":
    main()
