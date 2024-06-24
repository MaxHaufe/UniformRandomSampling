from abc import ABC, abstractmethod
import pycosat
import z3


class VariabilityModel:
    def __init__(self, path: str):
        """

        Args:
            path ():
        """
        self.path: str = path

        # self.dimacs_list, self.num_vars, self.num_clauses = self.parse_dimacs(path)
        self.solver, self.num_literals, self.num_clauses, self.literals, self.clauses = self.parse_dimacs(path)
        self.solver: z3.Solver

    @staticmethod
    def parse_dimacs(path: str) -> (z3.Solver, int, int, list, list):
        solver = z3.Solver()
        literals = set()
        num_clauses = 0
        num_literals = 0
        clauses = []
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
                elif line.startswith('%'):
                    # End of file
                    break
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
                    clauses.append(z3.Or(*clause))
                    solver.add(z3.Or(*clause))

        return solver, num_literals, num_clauses, literals, clauses

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
            m = self.solver.translate(z3.main_ctx())
            m.add(z3.Not(z3.Bool(formatted)))
            if m.check() == z3.unsat:
                mandatory += 1
        return mandatory


class ISampler(ABC):
    def __init__(self, vm: VariabilityModel):
        self.vm = vm

    @abstractmethod
    def sample(self, n_samples: int) -> set:
        pass

    def add_conjunction_to_model(self, c: z3.ModelRef) -> None:
        """

        :param c: a valid configuration from which a conjunction will be constructed and added to the model
        :type c:
        :return:
        :rtype:
        """
        conj = []
        for decl in c.decls():
            lit = z3.Bool(decl.name())
            if c[decl]:
                conj.append(lit)
            else:
                conj.append(z3.Not(lit))
        self.vm.clauses.append(z3.Not(z3.And(conj)))  # this will be important for the diversity promotion sampler
        self.vm.solver.add(z3.Not(z3.And(conj)))  # this is important for the distance based sampler


if __name__ == '__main__':
    vm = VariabilityModel(
        '/home/max/Nextcloud/Uni/3.Semester/AutoSE/seminar/emse-evaluation-sharpsat/cnf/berkeleydb/berkeleydb.dimacs')
    vm.solver.check()
    print(vm.solver.solver())
