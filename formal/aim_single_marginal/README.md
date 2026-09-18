# AIM single-marginal Dafny pilot

This pilot verifies the deterministic histogram computed for one selected AIM marginal. The Gaussian mechanism is outside the proof boundary.

The Dafny method proves that each output coordinate is the exact count for that cell. A second lemma proves that appending one valid record increases its own cell by one and leaves all other cells unchanged. Under add/remove-one adjacency, this is the required sensitivity-one certificate.

The workflow verifies the Dafny source, translates it to Python, runs the generated Python, and saves the proof logs and generated files.
