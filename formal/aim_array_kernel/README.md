# Dafny AIM Mutable Array Kernel

This experiment replaces the immutable nested-sequence implementation with an in-place `array2<nat>` histogram.

The executable code performs one constant-time array update per record. A ghost nested-sequence model is maintained only during verification and is erased from generated Python. Dafny proves that every mutable array cell equals the mathematical two-way marginal count at return.

This tests the implementation pattern needed for a practical verified marginal library:

```text
mutable executable state + ghost functional model + refinement invariant
```

Expected generated-Python output:

```text
AIM_ARRAY_OK
1 2 1 1
```
