"""Check the closed double-determinant web with normalized two-strand clasps.

Run this script next to check_opening_closure.py. Only Python's standard
library is required.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import factorial
from pathlib import Path
from runpy import run_path


def permutation_sign(order):
    inversions = sum(a > b for i, a in enumerate(order) for b in order[i + 1:])
    return (-1) ** inversions


def packet_orbit(left, right):
    """Index the basis orbit under the independent swaps of the packet ends."""
    return tuple((min(a, b), max(a, b)) for a, b in zip(left, right))


def projected_coordinates(size):
    # Each permutation assigns the size colours to one determinant sink.
    signed_orders = [(order, permutation_sign(order))
                     for order in permutations(range(size))]
    orbit_sums = Counter()
    for left, left_sign in signed_orders:
        for right, right_sign in signed_orders:
            orbit_sums[packet_orbit(left, right)] += left_sign * right_sign

    coordinates = {}
    norm_squared = Fraction()
    for orbit, signed_sum in orbit_sums.items():
        # A packet with unequal colours has two distinct orders. Taking
        # the mean over the orbit applies all the normalized pair clasps.
        orbit_size = 2 ** sum(a != b for a, b in orbit)
        coefficient = Fraction(signed_sum, orbit_size)
        coordinates[orbit] = coefficient
        norm_squared += orbit_size * coefficient ** 2
    return coordinates, norm_squared


def main(tree_checker):
    native_three = run_path(str(tree_checker))['projected']
    for size in range(2, 6):
        coordinates, norm_squared = projected_coordinates(size)
        expected = Fraction((size + 1) * factorial(size) ** 2, 2 ** size)
        assert norm_squared == expected, (size, norm_squared, expected)
        print(f'm={size}: closed double determinant = {norm_squared}')
        if size == 3:
            for ends in product(range(3), repeat=6):
                orbit = packet_orbit(ends[::2], ends[1::2])
                assert coordinates.get(orbit, 0) == native_three(ends), ends
            print('All 729 ordered thin-basis entries agree with the opening tree.')


if __name__ == '__main__':
    main(Path(__file__).with_name('check_opening_closure.py'))
