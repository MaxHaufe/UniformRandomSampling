from typing import Callable

import z3
from src.samplers import VariabilityModel, ISampler
import numpy as np


# class DistanceBasedSampler(ISampler):
class DistanceBasedSampler(ISampler):
    def __init__(self, vm: VariabilityModel):
        """


        :param vm:
        :type vm:
        :param distance_metric:  function that evaluates the distance of a configuration (from origin)
        :type distance_metric:
        """
        super().__init__(vm)
        self._min_distance, self._max_distance = self._init_distribution(vm)
        self._rng = np.random.default_rng()

    @staticmethod
    def _init_distribution(vm: VariabilityModel) -> (int, int):
        """
        Without computing the whole population or understanding all
        constraints in the variability model, we have no knowledge
        about the value domain of D

        We
        can approximate the lower and the upper bound for D, though,
        by using the number of mandatory configuration options and
        the number of all configuration options, respectively.

        max(D) = card({o | o ∈ O})
        min(D) = card({o | o ∈ O ∧ o is mandatory})

        :param vm:
        :type vm:
        :return: min, max
        :rtype:
        """
        min_feat = vm.get_amount_of_mandatory_features()
        max_feat = vm.num_literals
        return min_feat, max_feat

    def sample(self, n_samples: int) -> set:
        sample_set = set()
        while len(sample_set) < n_samples:
            # if all entries are set to False, there are no solutions
            # change this every iteration since the model changes each iter
            solution_exists = dict.fromkeys(range(self._min_distance,
                                                  self._max_distance + 1))
            if all(x is False for x in solution_exists.values()):
                break  # no more solutions exist
            d = self.select_distance()
            if solution_exists[d] is False:
                continue
            c: z3.ModelRef = self.search_config_with_distance(d)
            # add c to num_smpls and add insert c to cnf in model

            if c is not None:
                solution_exists[d] = True
                sample_set.add(c)
                self.add_conjunction_to_model(c)
            else:
                solution_exists[d] = False
        return sample_set

    def select_distance(self) -> int:
        """
        draws a distance from the (uniform) distribution

        technically this could be modified to draw from a different distribution

        :return:
        :rtype:
        """
        return self._rng.integers(self._min_distance, self._max_distance + 1)

    def search_config_with_distance(self, d: int) -> z3.ModelRef:
        """
        search for configuiration c with exactly d config options selected

        "To this end, we add an additional
        constraint to the solver describing that exactly d options have
        to be selected in the configuration."

        LMAO, if I see it correctly I get n^k runtime here :(

        let's say I have the berkleydb model with 76. with (randomly drawn) k = 30 I get 1e+21
        but I guess SAT is also NP complete so I guess it's fine

        :param vm:
        :type vm:
        :param d:
        :type d:
        :return:
        :rtype:
        """
        m: z3.Solver = self.vm.solver.translate(z3.main_ctx())
        variables = [f'k!{i}' for i in range(1, self.vm.num_literals + 1)]
        m.add(z3.PbEq([(z3.Bool(v), 1) for v in variables], d))
        if m.check() == z3.sat:
            return m.model()
        else:
            return None


if __name__ == '__main__':
    _vm = VariabilityModel(
        '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')

    # print(_vm.model)
    print("num_vars", _vm.num_literals)
    print("num_clauses", _vm.num_clauses)
    print("mandatory features", _vm.get_amount_of_mandatory_features())

    # def manhattan_distance(config: list) -> int:
    #     """
    #
    #     [0,0,0] returns 0
    #     [1,0,0] returns 1
    #     [0,1,1] returns 2
    #     [1,1,1] returns 3
    #
    #     :param config: feature model
    #     :type config:
    #     :return: manhattan distance
    #     :rtype: int
    #     """
    #     return np.sum(config)

    dbs = DistanceBasedSampler(_vm)
    s = dbs.sample(5)
    print(s)

    pass
