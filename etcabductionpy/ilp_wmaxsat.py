# ilp_wmaxsat.py
#  Integer Linear Programming implementation of Weighted Max Sat Solver.
# Naoya Inoue

import itertools

import gurobipy
import os
import math0

class ilp_wmaxsat_solver_t:
    def __init__(self):
        self.gm   = gurobipy.Model("ilp_wmaxsat_solver")
        self.vars = {}
        self.cost_vars = {}

    def encode(self, f):
        '''Encode the WMAXSAT problem of f as an ILP problem.'''
        self._encode_variables(f)
        self._encode_constraints(f)
        self._encode_objective(f)

    def write_lp(self, out):
        '''Write the encoded problem into a file.'''
        self.gm.write(out)

    def find_solutions(self, n):
        '''find n-best solutions. '''
        for i in xrange(n):

            # find the best assignment.
            self.gm.optimize()

            #
            # add new solution (if any).
            if self.gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
                yield []
                break

            yield [
                [k[0], k[-1]]
                for k, var in self.cost_vars.iteritems()
                if var.getAttr(gurobipy.GRB.Attr.X) == 1.0
                ]

            # deny the current sol.
            if 1+i < n:
                self.gm.addConstr(sum([
                    var
                    if var.getAttr(gurobipy.GRB.Attr.X) == 1.0 else
                    1.0 - var
                    for k, var in self.cost_vars.iteritems()
                    ]) <= len(self.cost_vars)-1)

    def _encode_variables(self, f):
        # create one ILP variable for each node.
        for node in f.nxg.nodes_iter():
            self.vars[node] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name=repr(node))

            # create cost variable.
            if node[1][0].startswith("etc"):
                if f.unifiables.has_key(node[1]):
                    self.cost_vars[node[1]] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name=repr(node[1]))

                else:
                    self.cost_vars[node[1]] = self.vars[node]

        self.gm.update()

    def _encode_constraints(self, f):
        # create and-or constraints.
        for node in f.nxg.nodes_iter():
            if "^" == node[1]:
                self._encode_and(f, node)

            elif "v" == node[1]:
                self._encode_or(f, node)

            elif len(f.nxg.successors(node)) == 0:
                # leaf node?

                if not node[1][0].startswith("etc"):
                    # non-abducible is at leaf!
                    # make it disable.
                    self.vars[node].setAttr(gurobipy.GRB.Attr.UB, 0.0)

        #
        for k, literals in f.unifiables.iteritems():
            self.gm.addConstr(self.cost_vars[k] <= sum([self.vars[node] for node in literals]))
            self.gm.addConstr(sum([self.vars[node] for node in literals]) <= len(literals)*self.cost_vars[k])

        # the given formula must be satisfied.
        self.gm.addConstr(self.vars[(1, "^")] >= 1)
        self.gm.update()

    def _encode_and(self, f, node):
        # c=1 <=> x1=1 \land x2=1 \land ... \land xn=1
        cvar, xvars = self.vars[node], [self.vars[x] for x in f.nxg.successors(node)]

        self.gm.addConstr(sum(xvars) == len(xvars)*cvar)

        '''the above is short for:
        self.gm.addConstr(len(xvars)*cvar <= sum(xvars))
        self.gm.addConstr(sum(xvars) - len(xvars) + 1 <= cvar)

        # to avoid redundant explanation
        if len(xvars) > 1:
            self.gm.addConstr((len(xvars)-1)*xvars[0] == sum(xvars[1:]))
        '''

    def _encode_or(self, f, node):
        # dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1
        dvar, xvars = self.vars[node], [self.vars[x] for x in f.nxg.successors(node)]

        self.gm.addConstr(sum(xvars) == dvar)

        '''the above is short for:
        self.gm.addConstr(dvar <= sum(xvars))
        self.gm.addConstr(sum(xvars) <= len(xvars)*dvar)

        # to avoid redundant explanation
        if len(xvars) > 1:
            self.gm.addSOS(gurobipy.GRB.SOS_TYPE1, xvars)
            # or self.gm.addConstr(sum(xvars) <= 1)
        '''

    def _encode_objective(self, f):
        '''set ILP objective.'''
        self.gm.setObjective(
            sum([math.log(lit[-1]) * var
                for lit, var in self.cost_vars.iteritems()
                ]),
                gurobipy.GRB.MAXIMIZE)
        self.gm.update()