# Dafny DP foundation pilot

This pilot turns the earlier AIM marginal examples into a shared end-to-end proof chain.

It verifies:

- stable first-`cap` contribution bounding for each user block;
- a flattened two-way marginal specification;
- a mutable array implementation refining the same specification;
- a user-add sensitivity certificate: the added user's delta histogram has squared L2 norm at most `cap^2`;
- exact rational privacy-cost addition and a budget filter;
- a checked Python-facing entry point that rejects records outside the declared domain.

The Gaussian mechanism and the zCDP composition theorem remain trusted theorem interfaces. This pilot verifies the deterministic query, its sensitivity input, and the implementation of the budget ledger.

The GitHub workflow verifies the Dafny file, translates it to Python, executes the generated Python, and archives all outputs.
