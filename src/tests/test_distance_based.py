import unittest

import z3

from src.samplers.distance_based import DistanceBasedSampler
from src.samplers import VariabilityModel


class TestDistanceBased(unittest.TestCase):
    def test_vm(self):
        vm = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
        mandat = vm.get_amount_of_mandatory_features()
        print(mandat)
        assert mandat == 1

    def test_custom_vm(self):
        vm = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/custom.dimacs')
        mandat = vm.get_amount_of_mandatory_features()
        assert mandat == 1

    def test_search_config_with_distance(self):
        vm = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
        db = DistanceBasedSampler(vm, None)
        ns = [i for i in range(db._min_distance, db._max_distance + 1)]
        for n in ns:
            c = db.search_config_with_distance(n)
            if c is None:
                print(f"n = {n} is unsat")
                continue  # UNSAT
            is_true = [1 if c[decl] else 0 for decl in c.decls()]
            num_true = sum(is_true)
            assert n == num_true

    def test_dbs_uniqueness(self):
        vm = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
        db = DistanceBasedSampler(vm, None)
        db.select_distance = lambda: 20
        s = db.sample(10)
        assert len(s) == 10



if __name__ == '__main__':
    unittest.main()
