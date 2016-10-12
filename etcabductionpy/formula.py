
import unify
import parse

import itertools

import math
import collections
import networkx as nx

class formula_t(object):
    def __init__(self):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.unifiables = collections.defaultdict(list)

    def _shrink(self):
        self._shrink_conj()
        self._shrink_disj()

    def visualize(self, out):
        '''Visualize the formula as a DAG.'''
        gvz = nx.to_agraph(self.nxg)
        gvz.layout()
        gvz.draw(out)

    def _scan_unifiables(self):
        '''store list of literals with the same predicates.'''
        _unifiables = collections.defaultdict(list)

        for node in self.nxg.nodes_iter():
            if node[1] in ["^", "v", "<->"]:
                continue

            _unifiables[node[1]] += [node]

        for k, literals in _unifiables.iteritems():
            if len(literals) >= 2:
                self.unifiables[k] = literals

    def _shrink_conj(self):
        removed_nodes = []

        for node in self.nxg.nodes_iter():
            if node[1] != "^":
                continue

            # check if there is non-abducible in the conjunction
            non_abducibles = [suc
                for suc in self.nxg.successors(node)
                if len(self.nxg.successors(suc)) == 0 and not suc[1][0].startswith("etc")]

            # remove "^" and its successors.
            if len(non_abducibles) > 0:
                removed_nodes += [node]
                removed_nodes += self.nxg.successors(node)
                continue

            # for just one successor.
            if len(self.nxg.successors(node)) == 1:
                removed_nodes += [node]
                self.nxg.add_edge(self.nxg.predecessors(node)[0], self.nxg.successors(node)[0])

        for node in removed_nodes:
            self.nxg.remove_node(node)

    def _shrink_disj(self):
        removed_nodes = []

        for node in self.nxg.nodes_iter():
            if node[1] != "v":
                continue

            # for just one successor.
            if len(self.nxg.successors(node)) == 1:
                removed_nodes += [node]
                self.nxg.add_edge(self.nxg.predecessors(node)[0], self.nxg.successors(node)[0])

        for node in removed_nodes:
            self.nxg.remove_node(node)

    def _create_node(self, dat):
        self.unique_id += 1
        return (self.unique_id, dat)


class explanation_formula_t(formula_t):
    def __init__(self, obs, ikb, maxdepth):
        super(explanation_formula_t, self).__init__()

        self.ikb = ikb
        self.maxdepth = maxdepth
        self.generate(obs, 0, -1)

        self._shrink()
        self._scan_unifiables()
        # self.unify()

    def generate(self, conj, level, from_id = 0):
        '''Generate an explanation formula for the conjunction F of literals. The formula is encoded as an AND-OR tree (networkx.DiGraph).'''
        gnid_conj  = self._create_node("^")

        if -1 != from_id:
            self.nxg.add_edge(from_id, gnid_conj)

        for literal in conj:
            predicate = literal[0]

            if level < self.maxdepth and predicate in self.ikb:
                gnid_disj = self._create_node("v")
                self.nxg.add_edge(gnid_conj, gnid_disj)

                # backchain on the literal.
                for rule in self.ikb[predicate]:
                    self.generate(parse.antecedent(rule), level+1, gnid_disj)

            else:
                gnid_lit = self._create_node(tuple(literal))
                self.nxg.add_edge(gnid_conj, gnid_lit)
