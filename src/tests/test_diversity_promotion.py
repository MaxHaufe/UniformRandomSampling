import unittest
from src.samplers.diversity_promotion import DiverseVM
from src.samplers import VariabilityModel
import z3

path = '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs'


def solve(vm: z3.Solver, n: int):
    ret = []
    for _ in range(n):
        if vm.check() == z3.sat:
            c = vm.model()
            # TODO: check if c ist None
            ret.append(c)
            # manipulate model
            conj = []
            for decl in c.decls():
                lit = z3.Bool(decl.name())
                if c[decl]:
                    conj.append(lit)
                else:
                    conj.append(z3.Not(lit))
            vm.add(z3.Not(z3.And(conj)))

    return ret


class MyTestCase(unittest.TestCase):

    def test_clause_shuffle_true_10(self):
        vm1, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=True)
        vm2, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=True)
        c1 = solve(vm1, 10)
        c2 = solve(vm2, 10)
        self.assertNotEqual(str(c1), str(c2))

    def test_clause_shuffle_true_1(self):
        vm1, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=True)
        vm2, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=True)
        c1 = solve(vm1, 1)
        c2 = solve(vm2, 1)
        self.assertNotEqual(str(c1), str(c2))

    def test_clause_shuffle_false(self):
        vm1, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=False)
        vm2, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=False)
        c1 = solve(vm1, 10)
        c2 = solve(vm2, 10)
        self.assertEqual(str(c1), str(c2))

    def test_clause_shuffle_false_1(self):
        vm1, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=False)
        vm2, _, _, _ = DiverseVM.parse_dimacs(path, shuffle=False)
        c1 = solve(vm1, 1)
        c2 = solve(vm2, 1)
        self.assertEqual(str(c1), str(c2))


if __name__ == '__main__':
    unittest.main()
