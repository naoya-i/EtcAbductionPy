# etcetera_search.py
# Etcetera Abduction
#  -- Search-based formulation plugin
# Naoya Inoue

import aostar_search
import itertools

import math
import time
import logging
import os

import collections

class stopwatch_t:
    def __init__(self):
        self.records = {}

    def start(self):
        self.time    = time.time()

    def stop(self, name):
        self.records[name] = time.time() - self.time

def nbest_aostar(obs, kb, indexed_kb, maxdepth, n, graph = False):

    sw = stopwatch_t()
    s  = aostar_search.aostar_searcher_t(indexed_kb,  maxdepth, n, graph)
    logging.info("Searching...")

    sw.start()

    sols = []

    for sol in s.search(obs):
        if not graph:
            sols += [sol]

        logging.info("  Got %d-best solution!" % (len(sols)))

    sw.stop("search")

    logging.info("  Inference time: %.2f" % (
        sw.records["search"],
        ))
    logging.info("  # expanded: %d" % (
        s.num_expanded,
        ))

    return sols
