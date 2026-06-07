from experiments.discrete import ramsey_search as ramsey


def test_contains_clique_detects_complete_subgraphs():
    complete_four = ramsey.complete_graph(4)
    empty_four = ramsey.empty_graph(4)

    assert ramsey.contains_clique(complete_four, 3)
    assert not ramsey.contains_clique(empty_four, 2)


def test_contains_independent_set_uses_graph_complement():
    complete_four = ramsey.complete_graph(4)
    empty_four = ramsey.empty_graph(4)

    assert not ramsey.contains_independent_set(complete_four, 2)
    assert ramsey.contains_independent_set(empty_four, 3)


def test_find_ramsey_counterexample_respects_small_known_values():
    triangle_free_or_independent_3_on_five = ramsey.find_counterexample(5, clique_size=3, independent_size=3)
    triangle_free_or_independent_3_on_six = ramsey.find_counterexample(6, clique_size=3, independent_size=3)

    assert triangle_free_or_independent_3_on_five is not None
    assert not ramsey.contains_clique(triangle_free_or_independent_3_on_five, 3)
    assert not ramsey.contains_independent_set(triangle_free_or_independent_3_on_five, 3)
    assert triangle_free_or_independent_3_on_six is None
