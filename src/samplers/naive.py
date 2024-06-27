import z3
from .import VariabilityModel, ISampler


class NaiveSampler(ISampler):
    """
    Naive brute force sampler that samples all possible configurations.
    This was created so the problem configurations could be benchmarked.
    Due to diversity enforcement the other samplers have too much overhead.
    """
    def sample(self, n_samples: int) -> set:
        sample_set = set()
        for _ in range(n_samples):
            # print progress every 1000 samples
            if _ % 10_000 == 0 and _ != 0:
                print(f"Sampled {_} configurations.")
            if self.vm.solver.check() == z3.sat:
                c = self.vm.solver.model()
                sample_set.add(c)
                self.add_conjunction_to_model(c)
            else:
                print("Model is unsat, no more solutions exist."
                      "Returning the current sample set of size: ", len(sample_set))
                return sample_set
        return sample_set

    def sample_all(self):
        # approximate n as the number of all possible configurations
        n = 2 ** len(self.vm.literals)
        return self.sample(n)


if __name__ == '__main__':
    vm1 = VariabilityModel(
        # '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')

        # '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/dimacs/uf20-0100.cnf')
        '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/dimacs/blasted_case110.cnf')
    n = 5
    dps = NaiveSampler(vm1)
    s = dps.sample_all()
    print(len(s))
    # print(s)

    # compare()
