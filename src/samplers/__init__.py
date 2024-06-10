from abc import ABC, abstractmethod
import pycosat
import z3


# class ISampler(ABC):
#     @abstractmethod
#     def sample(self, data, n_samples):
#         pass


class VariabilityModel:
    def __init__(self, path: str):
        """

        Args:
            path ():
        """
        self.path: str = path

        # self.dimacs_list, self.num_vars, self.num_clauses = self.parse_dimacs(path)
        self.model, self.num_literals, self.num_clauses, _ = self.parse_dimacs(path)  # :TODO
        self.model: z3.Solver

    @staticmethod
    def parse_dimacs(path: str) -> (z3.Solver, int, int):
        solver = z3.Solver()
        literals = set()
        num_clauses = 0
        num_literals = 0
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line.startswith('p'):
                    # Problem line
                    parts = line.split()
                    num_literals = int(parts[2])
                    num_clauses = int(parts[3])
                elif line.startswith('c') or line == '':
                    # Comment line or empty line, ignore
                    continue
                else:
                    # Clause line
                    clause = []
                    for lit in line.split():
                        lit = int(lit)
                        if lit == 0:
                            break
                        abs_lit = abs(lit)
                        var = z3.Bool(f'k!{abs_lit}')
                        literals.add(var)
                        clause.append(var if lit > 0 else z3.Not(var))
                    solver.add(z3.Or(*clause))

        return solver, num_literals, num_clauses, literals

    def get_amount_of_mandatory_features(self) -> int:
        """
        Returns the amount of mandatory features in the model
        :return:
        :rtype:
        """
        mandatory = 0
        for literal in range(1, self.num_literals + 1):
            formatted = f"k!{literal}"
            # m = self.model.copy()
            # appearently it copies
            # https://stackoverflow.com/a/36775158
            m = self.model.translate(z3.main_ctx())
            m.add(z3.Not(z3.Bool(formatted)))
            if m.check() == z3.unsat:
                mandatory += 1
        return mandatory


if __name__ == '__main__':
    vm = VariabilityModel(
        '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
    vm.model.check()
    print(vm.model.model())
