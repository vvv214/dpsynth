from pathlib import Path

path = Path("formal/dp_foundation/FoundationPilot.dfy")
text = path.read_text(encoding="utf-8")

if ("lemma ValidRowsElement(" in text and
    "method CheckedSpendUntilBudget(" in text and
    "function AtOrZero(" in text):
    print("proof fixes already applied")
    raise SystemExit(0)

def replace_once(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one match, found {count}: {old[:80]!r}")
    text = text.replace(old, new, 1)

replace_once(
"""  lemma ClipRowsBound(rows: seq<Cell>, cap: nat)
""",
"""  lemma ValidRowsElement(
    rows: seq<Cell>, i: nat, aCard: nat, bCard: nat
  )
    requires ValidRows(rows, aCard, bCard)
    requires i < |rows|
    ensures ValidCell(rows[i], aCard, bCard)
    decreases |rows|
  {
    if i == |rows| - 1 {
    } else {
      assert i < |rows| - 1;
      ValidRowsElement(
        rows[..|rows| - 1], i, aCard, bCard
      );
      assert rows[..|rows| - 1][i] == rows[i];
    }
  }

  lemma ClipRowsBound(rows: seq<Cell>, cap: nat)
"""
)

replace_once(
"""  lemma CellIndexBound(c: Cell, aCard: nat, bCard: nat)
""",
"""  lemma MulMonotone(x: nat, y: nat, z: nat)
    requires x <= y
    ensures x * z <= y * z
    decreases z
  {
    if z > 0 {
      MulMonotone(x, y, z - 1);
      assert x * z == x * (z - 1) + x;
      assert y * z == y * (z - 1) + y;
    }
  }

  lemma CellIndexBound(c: Cell, aCard: nat, bCard: nat)
"""
)

replace_once(
"""  lemma CellIndexBound(c: Cell, aCard: nat, bCard: nat)
    requires ValidCell(c, aCard, bCard)
    ensures CellIndex(c, bCard) < aCard * bCard
  {
  }
""",
"""  lemma CellIndexBound(c: Cell, aCard: nat, bCard: nat)
    requires ValidCell(c, aCard, bCard)
    ensures CellIndex(c, bCard) < aCard * bCard
  {
    assert c.a + 1 <= aCard;
    MulMonotone(c.a + 1, aCard, bCard);
    assert (c.a + 1) * bCard ==
      c.a * bCard + bCard;
    assert c.a * bCard + c.b <
      c.a * bCard + bCard;
  }
"""
)

replace_once(
"""  {
    seq(|left|, i => left[i] + right[i])
  }

  lemma VecAddZeroRight""",
"""  {
    seq(
      |left|,
      i => left[i] +
        (if i < |right| then right[i] else 0)
    )
  }

  lemma VecAddZeroRight"""
)

replace_once(
"""  function VecAdd(left: seq<nat>, right: seq<nat>): (result: seq<nat>)
    requires |left| == |right|
    ensures |result| == |left|
  {
    seq(
      |left|,
      i => left[i] +
        (if i < |right| then right[i] else 0)
    )
  }
""",
"""  function AtOrZero(values: seq<nat>, i: int): nat
  {
    if 0 <= i < |values| then values[i] else 0
  }

  function VecAdd(left: seq<nat>, right: seq<nat>): (result: seq<nat>)
    requires |left| == |right|
    ensures |result| == |left|
  {
    seq(
      |left|,
      i => AtOrZero(left, i) + AtOrZero(right, i)
    )
  }
"""
)

replace_once(
"""  lemma SumSquaresLeSquareSum(values: seq<nat>)
    ensures
      SumSquares(values) <= Sum(values) * Sum(values)
    decreases |values|
  {
    if |values| > 0 {
      var prefix := values[..|values| - 1];
      var x := values[|values| - 1];
      SumSquaresLeSquareSum(prefix);
      assert 0 <=
        2 * Sum(prefix) * x;
    }
  }
""",
"""  lemma SumSquaresLeSquareSum(values: seq<nat>)
    ensures
      SumSquares(values) <= Sum(values) * Sum(values)
    decreases |values|
  {
    if |values| > 0 {
      var prefix := values[..|values| - 1];
      var x := values[|values| - 1];
      var prefixSum := Sum(prefix);
      var prefixSquares := SumSquares(prefix);
      SumSquaresLeSquareSum(prefix);
      assert prefixSquares <= prefixSum * prefixSum;
      assert Sum(values) == prefixSum + x;
      assert SumSquares(values) == prefixSquares + x * x;
      assert prefixSquares + x * x <=
        prefixSum * prefixSum + x * x;
      assert prefixSum * prefixSum + x * x <=
        prefixSum * prefixSum +
        2 * prefixSum * x + x * x;
      assert (prefixSum + x) * (prefixSum + x) ==
        prefixSum * prefixSum +
        2 * prefixSum * x + x * x;
    }
  }
"""
)

replace_once(
"""  lemma SquareMonotone(x: nat, y: nat)
    requires x <= y
    ensures x * x <= y * y
  {
    assert y == x + (y - x);
    assert 0 <= 2 * x * (y - x) + (y - x) * (y - x);
  }
""",
"""  lemma SquareMonotone(x: nat, y: nat)
    requires x <= y
    ensures x * x <= y * y
  {
    MulMonotone(x, y, x);
    MulMonotone(x, y, y);
    assert y * x == x * y;
  }
"""
)

replace_once(
"""      var c := rows[i];
      CellIndexBound(c, aCard, bCard);
""",
"""      var c := rows[i];
      ValidRowsElement(rows, i, aCard, bCard);
      CellIndexBound(c, aCard, bCard);
"""
)

replace_once(
"""  method SpendUntilBudget(
""",
"""  method CheckCosts(costs: seq<Rat>) returns (ok: bool)
    ensures ok == ValidCosts(costs)
    decreases |costs|
  {
    if |costs| == 0 {
      ok := true;
    } else {
      var prefixOk :=
        CheckCosts(costs[..|costs| - 1]);
      ok := prefixOk &&
        0 < costs[|costs| - 1].den;
    }
  }

  method SpendUntilBudget(
"""
)

replace_once(
"""  }
}

module PythonBoundary {
""",
"""  }

  method CheckedSpendUntilBudget(
    costs: seq<Rat>, budget: Rat
  ) returns (ok: bool, used: Rat, accepted: nat)
    ensures !ok ==> used == ZeroRat() && accepted == 0
    ensures ok ==> accepted <= |costs|
    ensures ok ==> used == SumRat(costs[..accepted])
    ensures ok ==> LeRat(used, budget)
    ensures ok ==> accepted == |costs| ||
      !LeRat(AddRat(used, costs[accepted]), budget)
  {
    var costsOk := CheckCosts(costs);
    ok := costsOk && 0 < budget.den;
    if ok {
      used, accepted :=
        SpendUntilBudget(costs, budget);
    } else {
      used := ZeroRat();
      accepted := 0;
    }
  }
}

module PythonBoundary {
"""
)

replace_once(
"""    UserAddSensitivityCertificate(
      db, added, 2, 2, 2
    );

    var ok, hist :=
      CheckedUserBoundedMarginal(db, 2, 2, 2);

    var costs: seq<Rat> := [
      Rat(1, 4), Rat(1, 3), Rat(1, 2)
    ];
    var used, accepted :=
      SpendUntilBudget(costs, Rat(3, 4));
""",
"""    var dbOk := CheckDatabase(db, 2, 2);
    var addedOk := CheckRows(added.rows, 2, 2);
    if dbOk && addedOk {
      UserAddSensitivityCertificate(
        db, added, 2, 2, 2
      );
    }

    var ok, hist :=
      CheckedUserBoundedMarginal(db, 2, 2, 2);

    var costs: seq<Rat> := [
      Rat(1, 4), Rat(1, 3), Rat(1, 2)
    ];
    var budgetOk, used, accepted :=
      CheckedSpendUntilBudget(costs, Rat(3, 4));
"""
)

replace_once(
"""    if ok &&
       hist[0] == 1""",
"""    if ok && budgetOk &&
       hist[0] == 1"""
)

replace_once(
"""    forall i: nat | i < |left|
      ensures
""",
"""    forall i: nat {:trigger} | i < |left|
      ensures
"""
)

replace_once(
"""    ensures ok ==> accepted == |costs| ||
      !LeRat(AddRat(used, costs[accepted]), budget)
""",
"""    ensures ok ==> (accepted == |costs| ||
      !LeRat(AddRat(used, costs[accepted]), budget))
"""
)

path.write_text(text, encoding="utf-8")
