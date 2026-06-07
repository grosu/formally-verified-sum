import unittest

from summation import sum


class TestSum(unittest.TestCase):
    def test_sums_one_to_n(self):
        self.assertEqual(sum(5), 15)

    def test_sum_of_one(self):
        self.assertEqual(sum(1), 1)

    def test_zero_or_below_sums_to_zero(self):
        self.assertEqual(sum(0), 0)
        self.assertEqual(sum(-3), 0)


if __name__ == "__main__":
    unittest.main()
