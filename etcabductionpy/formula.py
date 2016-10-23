
import unify
import parse

import itertools

import sys
import math
import collections
import networkx as nx
import bisect

class formula_t(object):
    def __init__(self):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.levels = {}
        self.parents = {}
        self.unifiables = collections.defaultdict(list)

    def copy(self):
        f = formula_t()
        f.nxg = self.nxg.copy()
        f.levels = self.levels.copy()
        f.parents = self.parents.copy()
        f.unique_id = self.unique_id
        return f

    def visualize(self, out):
        '''Visualize the formula as a DAG.'''
        gvz = nx.to_agraph(self.nxg)
        gvz.layout()
        gvz.draw(out)

    def print_info(self):
        print nx.info(self.nxg)

    def _scan_unifiables(self):
        '''store list of literals with the same predicates.'''
        _unifiables = collections.defaultdict(list)

        for node in self.nxg.nodes_iter():
            if node[1] in ["^", "v", "<->"]:
                continue

            _unifiables[node[1]] += [node]

            if len(_unifiables[node[1]]) >= 2:
                self.unifiables[node[1]] = _unifiables[node[1]]

    def _create_node(self, dat, level = 0, parent = None):
        self.unique_id += 1
        self.levels[(self.unique_id, dat)] = level
        self.parents[(self.unique_id, dat)] = parent

        if parse.is_etc(dat):
            self.nxg.add_node((self.unique_id, dat), color='red', fontcolor='red')

        return (self.unique_id, dat)


class explanation_formula_t(formula_t):
    def __init__(self, ikb, maxdepth):
        super(explanation_formula_t, self).__init__()

        self.ikb = ikb
        self.maxdepth = maxdepth
        self.lower_bound  = 0

    def derive(self, obs):
        self.lower_bound = self.generate(obs, 0)
        self._scan_unifiables()

    def generate(self, conj, level, from_id = -1):
        '''Generate an explanation formula for the conjunction F of literals. The formula is encoded as an AND-OR tree (networkx.DiGraph). At the same, this function returns a lower bound.'''

        if from_id == -1 or len(conj) > 1:
            gnid_conj    = self._create_node("^")

            if -1 != from_id:
                self.nxg.add_edge(from_id, gnid_conj)

            from_id = gnid_conj

        lower_bound = 0

        for literal in conj:
            predicate = literal[0]

            if (level < self.maxdepth) and (predicate in self.ikb):

                from_node = from_id
                num_qualified = 0

                if len(self.ikb[predicate]) > 1:
                    gnid_disj = self._create_node("v")
                    from_node = gnid_disj
                    self.nxg.add_edge(gnid_conj, gnid_disj)

                # backchain on the literal.
                probs = []

                for rule in self.ikb[predicate]:
                    qualified = True

                    if level == self.maxdepth-1:
                        # does it contain non-abducible?
                        for lit in parse.antecedent(rule):
                            if not parse.is_etc(lit):
                                qualified = False
                                break

                    if qualified:
                        num_qualified += 1
                        probs += [self.generate(parse.antecedent(rule), level+1, from_node)]

                lower_bound += max(probs)

                # delete the "or" node if nothing is hypothesized.
                if len(self.ikb[predicate]) > 1 and 0 == num_qualified:
                    self.nxg.remove_node(gnid_disj)

            else:
                if 0 == level:
                    continue

                # create new node for literal
                gnid_lit = self._create_node(tuple(literal))
                self.nxg.add_edge(from_id, gnid_lit)

                if parse.is_etc(literal):
                    lower_bound += math.log(literal[-1])

        return lower_bound
