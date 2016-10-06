
import unify
import parse

import itertools

import math
import collections
import networkx as nx

class explanation_formula_t:
    def __init__(self, obs, ikb, maxdepth):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.ikb = ikb
        self.maxdepth = maxdepth
        self.unifiables = collections.defaultdict(list)

        self.generate(obs, 0, -1)
        self._shrink_conj()
        self._shrink_disj()
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
                    theta = unify.unify(literal, parse.consequent(rule))

                    if theta == None:
                        continue

                    self.generate(unify.standardize(unify.subst(theta, parse.antecedent(rule))), level+1, gnid_disj)

            else:
                gnid_lit = self._create_node(tuple(literal))
                self.nxg.add_edge(gnid_conj, gnid_lit)

    def visualize(self, out):
        '''Visualize the formula as a DAG.'''
        gvz = nx.to_agraph(self.nxg)
        gvz.layout()
        gvz.draw(out)
                
    def _scan_unifiables(self):
        for node in self.nxg.nodes_iter():
            # store list of literals with the same predicates.
            if node[1][0].startswith("etc"):
                self.unifiables[node[1]] += [node]

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

    def unify(self):
        for k, unifiable_literals in self.unifiables.iteritems():
            for i in xrange(2, len(unifiable_literals)+1):
                for literals in itertools.combinations(unifiable_literals, i):
                    # create a unified literal node.
                    gnid_cnj = self._create_node("^")
                    gnid_lit = self._create_node(k)

                    # collect its grand father (OR node)
                    for literal in literals:
                        pa      = self.nxg.predecessors(literal)[0]
                        grandpa = self.nxg.predecessors(pa)[0]

                        self.nxg.add_edge(grandpa, gnid_cnj)
                        self.nxg.add_edge(gnid_cnj, gnid_lit)
