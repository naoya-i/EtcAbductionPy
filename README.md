# EtcAbductionPy

## An implementation of Etcetera Abduction in Python

This software is a reference implementation of Etcetera Abduction. Given a knowledge base of first-order definite clauses and a set of observables, this software identifies the most probable set of assumptions that logically entails the observations, assuming the conditional independence of each assumption.

For more information, see the following:

* Gordon, Andrew S. (2016) Commonsense Interpretation of Triangle Behavior. In Proceedings of the Thirtieth AAAI Conference on Artificial Intelligence (AAAI-16), February 12-17, 2016, Phoenix, Arizona.

# Short memo on updates from the original version

This is a forked project from Andrew Gordon's EtcAbductionPy (https://github.com/asgordon/EtcAbductionPy).

## Efficient S-expression parsing

The use of collections.deque makes S-expression parsing much faster.

## Knowledge base caching

For large knowledge base. This function requires python-mcdb (https://github.com/gstrauss/mcdb).

* `--kbcache [FILE]` or `-kc [FILE]`: create cache of knowledge base on FILE.
* `--kbmcdb [FILE]` or `-km [FILE]`: use cached knowledge base from FILE.

Example:

    # Create a cache.
    python etcabductionpy -k kb.lisp -kc kb.lisp.mcdb

    # Use the cache for inference.
    python etcabductionpy -km kb.lisp.mcdb ...


## Integer Linear Programming-based inference for propositional abduction

* `--ilp` or `-l`: use ILP solver (gurobi) to search the (n-)best solution(s).
* `--ilp-show-nonetc` or `-lnonetc`: output non-etc literals.
* `--ilp-verbose` or `-lv`: output an ILP solver log.
