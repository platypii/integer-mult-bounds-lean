#!/usr/bin/env python3
"""Check that translating degree-seven polynomials by 2 gives prefix pivots for PR589."""
import gzip
import hashlib
import json
from collections import Counter
from functools import lru_cache
from fractions import Fraction
from itertools import permutations
from math import comb, gcd, lcm
from pathlib import Path

from generate_pr589_moves import SHA256
from generate_pr589_copy_ranks import inverse

WORD = (Path(__file__).resolve().parents[1] / "integer-mult-bounds/research/"
        "e8-bit-p111-tuned/tune/bitE8mut-p111-tuned.json.gz")


def pivots(rows):
    """Return the pivot columns over the rationals by fraction-free row elimination."""
    basis = {}
    for row in rows:
        v = list(row)
        for j in range(len(v)):
            if not v[j]:
                continue
            if j not in basis:
                basis[j] = v
                break
            b = basis[j]
            v = [b[j] * x - v[j] * y for x, y in zip(v, b)]
            divisor = gcd(*v)
            if divisor:
                v = [x // divisor for x in v]
    return set(basis)


def graph_rows(rows, rank):
    """Recover the prefix graph [I | A] by reducing the integral generators."""
    rows = [list(map(Fraction, row)) for row in rows]
    for j in range(rank):
        pivot = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        rows[j] = [x / rows[j][j] for x in rows[j]]
        for i, row in enumerate(rows):
            if i != j and row[j]:
                rows[i] = [x - row[j] * y for x, y in zip(row, rows[j])]
    assert all(not any(row) for row in rows[rank:])
    return rows[:rank]


def translate(row):
    return [sum(row[k] * comb(k, j) * 2 ** (k - j) for k in range(j, 8))
            for j in range(8)]


def check_helper_windows(endpoint_positions, gates):
    """Check scalar dependence across each potential same-helper crossing window."""
    group_sizes = []
    windows = 0
    for helper, positions in enumerate(endpoint_positions[222:], start=222):
        for start in positions.get((0, 1), []):
            for stop in positions.get((7, 8), []):
                assert start < stop
                # MOVEs precede their gate: include the opening gate, exclude the closing gate.
                # One bit per input register tracks exact XOR cancellation.
                rows = [1 << i for i in range(len(endpoint_positions))]
                for target, sources in gates[start:stop]:
                    delta = 0
                    for source in sources:
                        delta ^= rows[source]
                    rows[target] ^= delta
                assert rows[helper] & ~(1 << helper)
                assert any(row & (1 << helper) for i, row in enumerate(rows) if i != helper)
                # A common reindexing on a fixed set of registers commutes with this
                # scalar map precisely when no nonzero coefficient crosses its boundary.
                group = 1 << helper
                while True:
                    expanded = group
                    for i, row in enumerate(rows):
                        if group & (1 << i) or group & row:
                            expanded |= row | (1 << i)
                    if expanded == group:
                        break
                    group = expanded
                ports = (1 << 111) - 1
                group_sizes.append(group.bit_count())
                assert group & ports == ports
                assert (group >> 111) & ports == ports
                windows += 1
    assert (min(group_sizes), max(group_sizes)) == (477, 661)
    print("Each helper crossing requires all 222 ports in its fixed scalar reindexing group; "
          "the smallest such groups range from 477 to 661 registers.")
    assert windows == 179
    print(f"All {windows} helper windows import and export scalar data between endpoint MOVEs.")


def cycle_lengths(permutation):
    visited = set()
    lengths = []
    for start in range(len(permutation)):
        if start in visited:
            continue
        k = start
        length = 0
        while k not in visited:
            visited.add(k)
            length += 1
            k = permutation[k]
        assert k == start
        lengths.append(length)
    return sorted(lengths)


def block_placements(width):
    for a in range(17 - 2 * width):
        for b in range(a + width, 17 - width):
            perm = list(range(16))
            perm[a:a+width], perm[b:b+width] = perm[b:b+width], perm[a:a+width]
            yield perm


def check_two_child_ranks(widths, prefix_masks):
    """Filter all charts simultaneously by necessary submatrix ranks over the residue field."""
    @lru_cache(maxsize=None)
    def allowed(i, j, low, high):
        # One bit per chart; pack once per distinct rectangle constraint.
        bits = bytearray((len(prefix_masks) + 7) // 8)
        for chart, masks in enumerate(prefix_masks):
            if low <= (masks[i] >> j).bit_count() <= high:
                bits[chart // 8] |= 1 << (chart % 8)
        return int.from_bytes(bits, "little")

    survivors = 0
    example = None
    for first in block_placements(widths[0]):
        for last in block_placements(widths[1]):
            possible = (1 << len(prefix_masks)) - 1
            for i in range(1, 16):
                rows = sorted(last[:i])
                for j in range(1, 16):
                    cols = sorted(first[j:])
                    # Outer triangular factors preserve northeast rectangle ranks.
                    # In the middle triangular factor common indices force a
                    # nonsingular principal minor; matching bounds every nonzero minor.
                    low = len(set(rows).intersection(cols))
                    high = 0
                    for row in rows:
                        if high < len(cols) and cols[high] <= row:
                            high += 1
                    possible &= allowed(i, j, low, high)
                    if not possible:
                        break
                if not possible:
                    break
            if possible and example is None:
                example = ((possible & -possible).bit_length() - 1, first, last)
            survivors |= possible
    return survivors, example


def check_port_swap_distance(port_moves):
    """Compare the paid widths with the exact transposition distance in the swap-only model."""
    target_profiles = Counter(tuple(hi - lo for lo, hi in moves) for moves in port_moves[111:])
    assert target_profiles == {(2, 5): 92, (1, 6): 10, (7,): 9}
    assert all(moves == [(0, 7)] for moves in port_moves[111:] if len(moves) == 1)
    print("Nine targets have only one paid MOVE, exchanging the full seven-coordinate prefix.")
    patterns = set()
    for register, moves in enumerate(port_moves):
        # Track which input atom each output reads. Interior MOVE swaps commute
        # here because the scalar gates and triangular adapters are omitted.
        permutation = list(range(16))
        paid = 0
        for lo, hi in moves:
            paid += hi - lo
            for k in range(lo, hi):
                permutation[k], permutation[8 + k] = permutation[8 + k], permutation[k]
        patterns.add(tuple(permutation))
        for a, b in [(0, 7), (8, 15)]:
            permutation[a], permutation[b] = permutation[b], permutation[a]
        cycles = cycle_lengths(permutation)
        # Each transposition changes the cycle count by one, and a cycle
        # of length n is a product of n-1 transpositions.
        assert cycles == [2] * 6 + [4], register
        assert paid == 7 and 16 - len(cycles) == 9, register
    target = list(range(16))
    for k in range(7):
        target[k], target[k + 8] = target[k + 8], target[k]
    prefix_masks = []
    charts = [(*leading, 0) for leading in permutations(range(1, 8))]
    for chart in charts:
        masks = [0]
        for base in (0, 8):
            for k in chart:
                masks.append(masks[-1] | (1 << target[base + k]))
        prefix_masks.append(masks)
    for widths in target_profiles:
        if len(widths) == 2:
            survivors, example = check_two_child_ranks(widths, prefix_masks)
            assert survivors.bit_count() == {(2, 5): 192, (1, 6): 0}[widths]
            endpoint_swap = (7, 1, 2, 3, 4, 5, 6, 0)
            assert not (survivors >> charts.index(endpoint_swap)) & 1
            if example is not None:
                index, first, last = example
                assert charts[index] == (3, 4, 5, 6, 7, 1, 2, 0)
                assert first[0:2] == [14, 15] and last[0:5] == [11, 12, 13, 14, 15]
    print("With triangular adapters the rectangle-rank test admits 192 common charts "
          "for widths (2, 5) and none for (1, 6).")
    print("On every source and target register the seven paid atom swaps plus the port "
          "permutation have exact transposition distance nine.")

    # A coordinate permutation carries the trailing seven-dimensional support
    # onto the leading seven-dimensional support iff output 7 reads input 0.
    assert len(patterns) == 2
    for move in patterns:
        distances = Counter()
        for leading in permutations(range(1, 8)):
            chart = (*leading, 0)
            routed = [move[base + k] for base in (0, 8) for k in chart]
            distances[16 - len(cycle_lengths(routed))] += 1
        assert distances == {9: 232, 11: 1540, 13: 2548, 15: 720}
    print("Among all 5040 compatible common coordinate permutations, 232 achieve the "
          "minimum of nine swaps on each port MOVE pattern.")


def layout_components(register_count, cuts, gates, scatter_start, scatter_end, *, share_temps=False):
    """Return the equality classes at port boundaries when layouts can change at cuts."""
    current = list(range(register_count))
    parent = current.copy()

    def root(node):
        while node != parent[node]:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    temp_targets = {}
    for step, (target, sources) in enumerate(gates):
        if scatter_start <= step < scatter_end:
            # Each retained source can choose its temporary layout independently.
            # Reusing that temporary requires all targets in its fanout to agree.
            if share_temps:
                for source in sources:
                    first = temp_targets.setdefault(source, current[target])
                    parent[root(current[target])] = root(first)
            continue
        for register in [target, *sources]:
            if (step, register) in cuts:
                current[register] = len(parent)
                parent.append(len(parent))
        # Each nonzero XOR coefficient requires the same extra layout as the target.
        for source in set(sources):
            if sources.count(source) % 2:
                parent[root(current[source])] = root(current[target])

    return [(root(r), root(current[r])) for r in range(222)]


def main():
    raw = WORD.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    word = json.loads(gzip.decompress(raw))
    lines = word["lines"]
    shifted = [translate(row) for row in lines]
    max_entry = max(abs(x) for row in shifted for x in row)
    ranks = []
    max_denominator = 1
    max_relation_denominator = 1
    relations = 0
    for i, frame in enumerate(word["frames"]):
        rank = len(pivots(lines[j] for j in frame))
        assert pivots(shifted[j] for j in frame) == set(range(rank)), i
        graph = graph_rows((shifted[j] for j in frame), rank)
        basis = []
        for j in frame:
            row = shifted[j]
            if len(pivots([*basis, row])) > len(basis):
                basis.append(row)
        assert len(basis) == rank
        dual = inverse([row[:rank] for row in basis]) if rank else []
        for j in frame:
            row = shifted[j]
            coefficients = [sum(x * y for x, y in zip(row[:rank], column)) for column in zip(*dual)]
            den = lcm(*(x.denominator for x in coefficients))
            weights = [int(den * x) for x in coefficients]
            assert all(den * row[k] == sum(a * b[k] for a, b in zip(weights, basis)) for k in range(8))
            max_relation_denominator = max(max_relation_denominator, den)
            relations += 1
        max_denominator = max([max_denominator] + [x.denominator for row in graph for x in row])
        ranks.append(rank)

    labels = [set(frame) for frame in word["frames"]]
    refs = word["start"].copy()
    moves = 0
    port_moves = [[] for _ in range(222)]
    move_widths = {}
    width_six_moves = {}
    intervals = [set() for _ in refs]
    endpoint_positions = [{} for _ in refs]
    gates = []
    # The scatter COPY windows have a separate rank bill. This is the phase replay
    # in generate_pr589_moves.py, whose scatter boundary preserves the phase refs.
    for section in "DABC":
        if section == "B":
            copy_frames = [refs[source] for source in word["ret"]]
            assert copy_frames == list(range(510, 519))
            assert all(ranks[f] == 7 for f in copy_frames)
            adds = [(111 + t, k) for t, indices in enumerate(word["scatter"]) for k in indices]
            assert len(adds) == 527
            assert all(refs[t] == 0 and 0 <= k < len(copy_frames) for t, k in adds)
            assert ranks[0] == 0
            scatter_start = len(gates)
            gates.extend((111 + t, [word["ret"][k] for k in indices])
                         for t, indices in enumerate(word["scatter"]))
            scatter_end = len(gates)
        for gate_index, (frame, target, sources) in enumerate(word[section]):
            for register in [target, *sources]:
                old = refs[register]
                assert labels[old] <= labels[frame] or labels[frame] <= labels[old]
                if ranks[old] != ranks[frame]:
                    interval = tuple(sorted((ranks[old], ranks[frame])))
                    intervals[register].add(interval)
                    if register < len(port_moves):
                        port_moves[register].append(interval)
                    move_widths[len(gates), register] = interval[1] - interval[0]
                    if interval[1] - interval[0] == 6:
                        width_six_moves[len(gates), register] = (section, gate_index, ranks[old], ranks[frame])
                    if interval in ((0, 1), (7, 8)):
                        endpoint_positions[register].setdefault(interval, []).append(len(gates))
                    moves += 1
                refs[register] = frame
            gates.append((target, sources))
    assert (len(ranks), moves) == (636, 2911)
    # An endpoint crossing on one register needs both endpoint coordinates.
    # Count wider MOVEs too, to distinguish missing coordinates from batching.
    source_intervals, target_intervals = intervals[:111], intervals[111:222]
    assert all(not any(a == 0 for a, b in source) and any(b == 8 for a, b in source)
               for source in source_intervals)
    assert all(any(a == 0 for a, b in target) and not any(b == 8 for a, b in target)
               for target in target_intervals)
    source_singletons = sum((7, 8) in source for source in source_intervals)
    target_singletons = sum((0, 1) in target for target in target_intervals)
    helper_pairs = sum({(0, 1), (7, 8)} <= helper for helper in intervals[222:])
    assert (source_singletons, target_singletons, helper_pairs) == (108, 10, 179)
    print(f"Phase endpoint singleton MOVEs: coordinate 7 on {source_singletons} source registers, "
          f"coordinate 0 on {target_singletons} target registers, both on {helper_pairs} helpers.")
    print("No source phase MOVE touches coordinate 0; no target phase MOVE touches coordinate 7.")
    check_port_swap_distance(port_moves)
    check_helper_windows(endpoint_positions, gates)
    endpoint_cuts = {(step, register) for register, endpoints in enumerate(endpoint_positions)
                     for steps in endpoints.values() for step in steps}
    boundary = layout_components(len(refs), endpoint_cuts, gates, scatter_start, scatter_end)
    assert len({label for pair in boundary for label in pair}) == 1
    conflicts = []
    for width in range(1, 8):
        cuts = {key for key, size in move_widths.items() if size <= width}
        boundary = layout_components(len(refs), cuts, gates, scatter_start, scatter_end)
        source_inputs = {x for x, _ in boundary[:111]}
        target_outputs = {y for _, y in boundary[111:]}
        conflicts.append(len(source_inputs & target_outputs))
    assert conflicts == [1, 1, 10, 10, 10, 0, 0]
    print("Endpoint singleton cuts force a common layout on all port boundaries. "
          "Allowing arbitrary layout changes at MOVEs of width up to six first separates "
          "all source inputs from all target outputs in the phase XOR constraints.")
    six = {key for key, size in move_widths.items() if size == 6}
    cuts = {key for key, size in move_widths.items() if size <= 6}

    def separates(allowed):
        boundary = layout_components(len(refs), allowed, gates, scatter_start, scatter_end,
                                     share_temps=True)
        return {x for x, _ in boundary[:111]}.isdisjoint(y for _, y in boundary[111:])

    assert separates(cuts)
    necessary = sorted(key for key in six if not separates(cuts - {key}))
    target_registers = [116, 122, 161, 165, 167, 168, 173, 174, 176, 178]
    assert [r for _, r in necessary] == target_registers
    assert all(width_six_moves[step, r] == ("B", 490 + r, 1, 7) for step, r in necessary)
    print("The ten mandatory width-six cuts are 1-to-7 phase B MOVEs on target registers "
          + ", ".join(map(str, target_registers)) + ".")
    assert separates((cuts - six) | set(necessary))
    assert max_relation_denominator <= 2 ** 100
    print(f"Verified {relations} integral generator relations; maximum denominator: {max_relation_denominator}.")
    print("Verified nine rank-seven COPY prefixes and 527 zero-frame ADD targets.")
    print(f"Maximum translated entry magnitude: {max_entry}. Maximum graph denominator: {max_denominator}.")
    print(f"Verified prefix pivots for {len(ranks)} labels and consecutive pivots for {moves} positive-rank phase MOVEs.")


if __name__ == "__main__":
    main()
