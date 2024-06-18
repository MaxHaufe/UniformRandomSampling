import unittest
from src.samplers.diversity_promotion import DiversityPromotionSampler
from src.samplers import VariabilityModel
import z3

path = '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs'


def make_models():
    return VariabilityModel(path), VariabilityModel(path)


class MyTestCase(unittest.TestCase):
    def test_clause_shuffle_true_10(self):
        vm1, vm2 = make_models()
        n = 10
        dps1 = DiversityPromotionSampler(vm1)
        dps2 = DiversityPromotionSampler(vm2)

        c1 = dps1.sample(n)
        c2 = dps2.sample(n)

        self.assertNotEqual(str(c1), str(c2))

    def test_clause_shuffle_true_1(self):
        vm1, vm2 = make_models()
        n = 1
        dps1 = DiversityPromotionSampler(vm1)
        dps2 = DiversityPromotionSampler(vm2)

        c1 = dps1.sample(n)
        c2 = dps2.sample(n)

        self.assertNotEqual(str(c1), str(c2))

    def test_clause_shuffle_false(self):
        vm1, vm2 = make_models()
        n = 5
        dps1 = DiversityPromotionSampler(vm1, shuffle_clauses=False, shuffle_literals=False, random_phase=False,
                                         seed=42)
        dps2 = DiversityPromotionSampler(vm2, shuffle_clauses=False, shuffle_literals=False, random_phase=False,
                                         seed=42)

        c1 = dps1.sample(n)
        c2 = dps2.sample(n)

        self.assertEqual(str(c1), str(c2))


if __name__ == '__main__':
    unittest.main()
