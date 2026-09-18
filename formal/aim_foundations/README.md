# Dafny AIM Foundations Pilot

This pilot extends the single-cell-index histogram experiment in two directions.

1. `TwoWayMarginal` computes a genuine two-attribute marginal over records `(a, b)`. Dafny proves that every output cell equals the mathematical count and that adding one valid record changes exactly one cell by one. This is the deterministic fact needed to invoke the sensitivity-1 Gaussian mechanism theorem under add/remove adjacency.

2. `SpendUntilBudget` is a small privacy-budget ledger. Given exact nonnegative zCDP costs expressed in shared integer units, it accepts the longest prefix that fits within the budget. Dafny proves exact accounting, no overspend, and correct stopping. The zCDP composition theorem itself remains an imported mathematical fact.

The workflow performs:

```text
Dafny verification -> Python translation -> generated Python execution
```

Expected output:

```text
AIM_FOUNDATIONS_OK
[[1, 2], [1, 1]]
7 2
```

The Gaussian sampler, the Gaussian privacy theorem, and the zCDP composition theorem are deliberately outside this pilot. The experiment focuses on deterministic implementation correctness, sensitivity witnesses, and budget accounting.
