import numpy as np
import z3
from src.samplers import VariabilityModel, ISampler
import random
import matplotlib.pyplot as plt


class DiversityPromotionSampler(ISampler):

    def __init__(self, vm: VariabilityModel, shuffle_clauses: bool = True, shuffle_literals: bool = True,
                 random_phase: bool = True, seed: int = None):
        super().__init__(vm)
        self.shuffle_clauses = shuffle_clauses
        self.shuffle_literals = shuffle_literals
        self.switch_phase = random_phase
        self.vm.solver = None  # destroy model since we re-create the model for each sampling step
        self.seed = seed

    def sample(self, n_samples: int) -> set:
        sample_set = set()
        for _ in range(n_samples):
            # permute the clauses
            if self.shuffle_clauses:
                random.shuffle(self.vm.clauses)  # in-place
            # permute the literals
            # TODO: check if this will work
            if self.shuffle_literals:
                for clause in self.vm.clauses:
                    random.shuffle(clause.children())  # in-place

            # create the solver
            self.vm.solver = z3.Solver()
            if self.seed:
                # testing
                self.vm.solver.set('random_seed', self.seed)
            self.vm.solver.add(self.vm.clauses)

            # change phase
            if self.switch_phase:
                self.vm.solver.set('phase', 'random')

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


def compare():
    vm = VariabilityModel(
        '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')

    num_iter = 100
    num_samples = 100

    def count_activated_features(samples):
        counts = {str(feature): 0 for feature in vm.literals}
        for sample in samples:
            model_dict = {str(d): 1 if sample[d] else 0 for d in sample.decls()}
            counts = {key: counts[key] + model_dict[key] for key in counts}
        return counts

    samples_diverse = []
    samples_non_diverse = []
    for _ in range(num_iter):
        vm1 = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
        vm2 = VariabilityModel(
            '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
        sampler_diverse = DiversityPromotionSampler(vm1, shuffle_clauses=True, shuffle_literals=True, random_phase=True,
                                                    seed=42)
        sampler_non_diverse = DiversityPromotionSampler(vm2, shuffle_clauses=False, shuffle_literals=False,
                                                        random_phase=False, seed=42)
        samples_diverse = samples_diverse + list(sampler_diverse.sample(num_samples))
        samples_non_diverse = samples_non_diverse + list(sampler_non_diverse.sample(num_samples))

    counts_diverse = count_activated_features(samples_diverse)
    counts_non_diverse = count_activated_features(samples_non_diverse)

    # Plot the results
    x = np.arange(len(vm.literals))
    features = [str(lit) for lit in vm.literals]

    fig, ax = plt.subplots(2, 1, figsize=(15, 10), sharex=True)

    ax[0].bar(x, [counts_diverse[f] for f in features], color='blue', alpha=0.7)
    ax[0].set_title('Diverse Sampling')
    ax[0].set_ylabel('Activation Count')

    ax[1].bar(x, [counts_non_diverse[f] for f in features], color='red', alpha=0.7)
    ax[1].set_title('Non-Diverse Sampling')
    ax[1].set_ylabel('Activation Count')
    ax[1].set_xlabel('Features')

    plt.xticks(x, features, rotation=90)
    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    vm1 = VariabilityModel(
        # '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
    '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/dimacs/uf20-0100.cnf')
    n = 5
    dps = DiversityPromotionSampler(vm1)
    s = dps.sample_all()
    print(len(s))
    # print(s)

    # compare()
