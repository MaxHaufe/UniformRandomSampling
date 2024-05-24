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

    # @staticmethod
    # def parse_dimacs(path: str) -> (list, int, int):
    #     """
    #     Parse the DIMACS file and return a list of lists of literals
    #
    #     :param path:
    #     :type path:
    #     :return:
    #     :rtype:
    #     """
    #     dimacs = list()
    #     dimacs.append(list())
    #     with open(path) as mfile:
    #         for line in mfile:
    #             tokens = line.split()
    #             # get amount of variables and clauses
    #             if len(tokens) > 0 and tokens[0] == "p":
    #                 n_vars = int(tokens[2])
    #                 n_clauses = int(tokens[3])
    #             if len(tokens) != 0 and tokens[0] not in ("p", "c"):
    #                 for tok in tokens:
    #                     lit = int(tok)
    #                     if lit == 0:
    #                         dimacs.append(list())
    #                     else:
    #                         dimacs[-1].append(lit)
    #     assert len(dimacs[-1]) == 0
    #     dimacs.pop()
    #     return dimacs, n_vars, n_clauses

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

    @staticmethod
    def parse_dimacs_z3(path: str) -> (z3.Solver, int, int):
        """
        Parse the DIMACS file and return a z3 expression

        :param path:
        :type path:
        :return:
        :rtype:
        """
        s = z3.Solver()
        s.from_file(path)

        header = s.dimacs().split('\n')[0]
        num_vars = header.split()[2]
        num_clauses = header.split()[3]

        return s, int(num_vars), int(num_clauses)

    # def get_amount_of_mandatory_features(self) -> int:
    #     """
    #     Returns the amount of mandatory features in the model
    #
    #     TODO: this is a very naive implementation, it may underestimate the amount of mandatory features
    #     for (a v b) ∧ (a v c) the amount of mandatory features is 0, but it should be 1 (because of a)
    #     but it is not possible to determine this without a SAT solver (I think)
    #
    #     :param dimacs:
    #     :type dimacs:
    #     :return:
    #     :rtype:
    #     """
    #     mandatory = 0
    #     for clause in self.dimacs_list:
    #         if len(clause) == 1:
    #             mandatory += 1
    #     return mandatory

    # def get_amount_of_mandatory_features(self) -> int:
    #     """
    #     Returns the amount of optional features in the model
    #
    #     :param dimacs:
    #     :type dimacs:
    #     :return:
    #     :rtype:
    #     """
    #     mandatory = 0
    #     for feat in range(1, self.num_vars + 1):
    #         l = self.dimacs_list.copy()
    #         l.append([-feat])
    #         if pycosat.solve(l) == "UNSAT":
    #             mandatory += 1
    #     return mandatory

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
