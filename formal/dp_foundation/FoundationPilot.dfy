module DataModel {

  datatype Cell = Cell(a: nat, b: nat)
  datatype UserBlock = UserBlock(uid: nat, rows: seq<Cell>)

  predicate ValidCell(c: Cell, aCard: nat, bCard: nat)
  {
    c.a < aCard && c.b < bCard
  }

  predicate ValidRows(rows: seq<Cell>, aCard: nat, bCard: nat)
    decreases |rows|
  {
    |rows| == 0 ||
    (ValidRows(rows[..|rows| - 1], aCard, bCard) &&
     ValidCell(rows[|rows| - 1], aCard, bCard))
  }

  predicate ValidDatabase(db: seq<UserBlock>, aCard: nat, bCard: nat)
    decreases |db|
  {
    |db| == 0 ||
    (ValidDatabase(db[..|db| - 1], aCard, bCard) &&
     ValidRows(db[|db| - 1].rows, aCard, bCard))
  }

  function ClipRows(rows: seq<Cell>, cap: nat): seq<Cell>
  {
    if |rows| <= cap then rows else rows[..cap]
  }

  lemma ValidRowsPrefix(
    rows: seq<Cell>, n: nat, aCard: nat, bCard: nat
  )
    requires ValidRows(rows, aCard, bCard)
    requires n <= |rows|
    ensures ValidRows(rows[..n], aCard, bCard)
    decreases |rows|
  {
    if n == |rows| {
      assert rows[..n] == rows;
    } else {
      assert n < |rows|;
      assert n <= |rows| - 1;
      ValidRowsPrefix(rows[..|rows| - 1], n, aCard, bCard);
      assert (rows[..|rows| - 1])[..n] == rows[..n];
    }
  }

  lemma ValidRowsElement(
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
    ensures |ClipRows(rows, cap)| <= cap
  {
    if |rows| <= cap {
    } else {
      assert |rows[..cap]| == cap;
    }
  }

  lemma ClipRowsValid(
    rows: seq<Cell>, cap: nat, aCard: nat, bCard: nat
  )
    requires ValidRows(rows, aCard, bCard)
    ensures ValidRows(ClipRows(rows, cap), aCard, bCard)
  {
    if |rows| <= cap {
    } else {
      ValidRowsPrefix(rows, cap, aCard, bCard);
    }
  }

  lemma ValidRowsConcat(
    left: seq<Cell>, right: seq<Cell>, aCard: nat, bCard: nat
  )
    requires ValidRows(left, aCard, bCard)
    requires ValidRows(right, aCard, bCard)
    ensures ValidRows(left + right, aCard, bCard)
    decreases |right|
  {
    if |right| == 0 {
      assert left + right == left;
    } else {
      var prefix := right[..|right| - 1];
      ValidRowsConcat(left, prefix, aCard, bCard);
      assert left + right ==
        (left + prefix) + [right[|right| - 1]];
    }
  }

  function FlattenBounded(db: seq<UserBlock>, cap: nat): seq<Cell>
    decreases |db|
  {
    if |db| == 0 then []
    else
      FlattenBounded(db[..|db| - 1], cap) +
      ClipRows(db[|db| - 1].rows, cap)
  }

  lemma FlattenBoundedAppend(
    db: seq<UserBlock>, user: UserBlock, cap: nat
  )
    ensures FlattenBounded(db + [user], cap) ==
      FlattenBounded(db, cap) + ClipRows(user.rows, cap)
  {
    assert |db + [user]| == |db| + 1;
    assert (db + [user])[..|db|] == db;
    assert (db + [user])[|db|] == user;
  }

  lemma FlattenBoundedValid(
    db: seq<UserBlock>, cap: nat, aCard: nat, bCard: nat
  )
    requires ValidDatabase(db, aCard, bCard)
    ensures ValidRows(FlattenBounded(db, cap), aCard, bCard)
    decreases |db|
  {
    if |db| == 0 {
    } else {
      var prefix := db[..|db| - 1];
      var user := db[|db| - 1];
      FlattenBoundedValid(prefix, cap, aCard, bCard);
      ClipRowsValid(user.rows, cap, aCard, bCard);
      ValidRowsConcat(
        FlattenBounded(prefix, cap),
        ClipRows(user.rows, cap),
        aCard,
        bCard
      );
    }
  }
}

module MarginalSpec {
  import opened DataModel

  function CellIndex(c: Cell, bCard: nat): nat
  {
    c.a * bCard + c.b
  }

  lemma MulMonotone(x: nat, y: nat, z: nat)
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

  function Histogram(
    rows: seq<Cell>, aCard: nat, bCard: nat
  ): (result: seq<nat>)
    ensures |result| == aCard * bCard
    decreases |rows|
  {
    if |rows| == 0 then
      seq(aCard * bCard, i => 0)
    else
      var prefix := rows[..|rows| - 1];
      var c := rows[|rows| - 1];
      var h := Histogram(prefix, aCard, bCard);
      var idx := CellIndex(c, bCard);
      if idx < aCard * bCard then
        h[idx := h[idx] + 1]
      else
        h
  }

  function AtOrZero(values: seq<nat>, i: int): nat
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

  lemma VecAddZeroRight(values: seq<nat>)
    ensures VecAdd(values, seq(|values|, i => 0)) == values
  {
    forall i: nat | i < |values|
      ensures VecAdd(values, seq(|values|, j => 0))[i] == values[i]
    {
    }
  }

  lemma VecAddUpdateRight(
    left: seq<nat>, right: seq<nat>, idx: nat
  )
    requires |left| == |right|
    requires idx < |right|
    ensures
      VecAdd(left, right[idx := right[idx] + 1]) ==
      VecAdd(left, right)[
        idx := VecAdd(left, right)[idx] + 1
      ]
  {
    forall i: nat {:trigger} | i < |left|
      ensures
        VecAdd(left, right[idx := right[idx] + 1])[i] ==
        VecAdd(left, right)[
          idx := VecAdd(left, right)[idx] + 1
        ][i]
    {
      if i == idx {
      } else {
      }
    }
  }

  lemma HistogramAppendCell(
    rows: seq<Cell>, c: Cell, aCard: nat, bCard: nat
  )
    ensures Histogram(rows + [c], aCard, bCard) ==
      if CellIndex(c, bCard) < aCard * bCard then
        Histogram(rows, aCard, bCard)[
          CellIndex(c, bCard) :=
            Histogram(rows, aCard, bCard)[CellIndex(c, bCard)] + 1
        ]
      else
        Histogram(rows, aCard, bCard)
  {
    assert |rows + [c]| == |rows| + 1;
    assert (rows + [c])[..|rows|] == rows;
    assert (rows + [c])[|rows|] == c;
  }

  lemma HistogramConcat(
    base: seq<Cell>, extra: seq<Cell>, aCard: nat, bCard: nat
  )
    ensures Histogram(base + extra, aCard, bCard) ==
      VecAdd(
        Histogram(base, aCard, bCard),
        Histogram(extra, aCard, bCard)
      )
    decreases |extra|
  {
    if |extra| == 0 {
      assert base + extra == base;
      VecAddZeroRight(Histogram(base, aCard, bCard));
    } else {
      var prefix := extra[..|extra| - 1];
      var c := extra[|extra| - 1];
      var idx := CellIndex(c, bCard);
      HistogramConcat(base, prefix, aCard, bCard);
      HistogramAppendCell(base + prefix, c, aCard, bCard);
      HistogramAppendCell(prefix, c, aCard, bCard);
      assert base + extra == (base + prefix) + [c];
      if idx < aCard * bCard {
        VecAddUpdateRight(
          Histogram(base, aCard, bCard),
          Histogram(prefix, aCard, bCard),
          idx
        );
      }
    }
  }

  function Sum(values: seq<nat>): nat
    decreases |values|
  {
    if |values| == 0 then 0
    else Sum(values[..|values| - 1]) + values[|values| - 1]
  }

  function SumSquares(values: seq<nat>): nat
    decreases |values|
  {
    if |values| == 0 then 0
    else
      SumSquares(values[..|values| - 1]) +
      values[|values| - 1] * values[|values| - 1]
  }

  lemma SumZero(k: nat)
    ensures Sum(seq(k, i => 0)) == 0
    decreases k
  {
    if k > 0 {
      SumZero(k - 1);
      assert seq(k, i => 0)[..k - 1] ==
        seq(k - 1, i => 0);
    }
  }

  lemma SumUpdateOne(values: seq<nat>, idx: nat)
    requires idx < |values|
    ensures
      Sum(values[idx := values[idx] + 1]) ==
      Sum(values) + 1
    decreases |values|
  {
    if idx == |values| - 1 {
      assert
        (values[idx := values[idx] + 1])[..|values| - 1] ==
        values[..|values| - 1];
      assert
        (values[idx := values[idx] + 1])[|values| - 1] ==
        values[|values| - 1] + 1;
    } else {
      assert idx < |values| - 1;
      SumUpdateOne(values[..|values| - 1], idx);
      assert
        (values[idx := values[idx] + 1])[..|values| - 1] ==
        values[..|values| - 1][idx := values[idx] + 1];
      assert
        (values[idx := values[idx] + 1])[|values| - 1] ==
        values[|values| - 1];
    }
  }

  lemma HistogramMass(
    rows: seq<Cell>, aCard: nat, bCard: nat
  )
    requires ValidRows(rows, aCard, bCard)
    ensures Sum(Histogram(rows, aCard, bCard)) == |rows|
    decreases |rows|
  {
    if |rows| == 0 {
      SumZero(aCard * bCard);
    } else {
      var prefix := rows[..|rows| - 1];
      var c := rows[|rows| - 1];
      HistogramMass(prefix, aCard, bCard);
      CellIndexBound(c, aCard, bCard);
      HistogramAppendCell(prefix, c, aCard, bCard);
      SumUpdateOne(
        Histogram(prefix, aCard, bCard),
        CellIndex(c, bCard)
      );
    }
  }

  lemma SumSquaresLeSquareSum(values: seq<nat>)
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

  lemma HistogramL2SquaredBound(
    rows: seq<Cell>, aCard: nat, bCard: nat
  )
    requires ValidRows(rows, aCard, bCard)
    ensures
      SumSquares(Histogram(rows, aCard, bCard)) <=
      |rows| * |rows|
  {
    HistogramMass(rows, aCard, bCard);
    SumSquaresLeSquareSum(Histogram(rows, aCard, bCard));
  }

  lemma SquareMonotone(x: nat, y: nat)
    requires x <= y
    ensures x * x <= y * y
  {
    MulMonotone(x, y, x);
    MulMonotone(x, y, y);
    assert y * x == x * y;
  }

  lemma UserAddSensitivityCertificate(
    db: seq<UserBlock>,
    user: UserBlock,
    cap: nat,
    aCard: nat,
    bCard: nat
  )
    requires ValidDatabase(db, aCard, bCard)
    requires ValidRows(user.rows, aCard, bCard)
    ensures
      Histogram(
        FlattenBounded(db + [user], cap), aCard, bCard
      ) ==
      VecAdd(
        Histogram(FlattenBounded(db, cap), aCard, bCard),
        Histogram(ClipRows(user.rows, cap), aCard, bCard)
      )
    ensures
      SumSquares(
        Histogram(ClipRows(user.rows, cap), aCard, bCard)
      ) <= cap * cap
  {
    FlattenBoundedAppend(db, user, cap);
    ClipRowsValid(user.rows, cap, aCard, bCard);
    ClipRowsBound(user.rows, cap);
    HistogramConcat(
      FlattenBounded(db, cap),
      ClipRows(user.rows, cap),
      aCard,
      bCard
    );
    HistogramL2SquaredBound(
      ClipRows(user.rows, cap), aCard, bCard
    );
    SquareMonotone(|ClipRows(user.rows, cap)|, cap);
  }
}

module MarginalImpl {
  import opened DataModel
  import opened MarginalSpec

  method ArrayHistogram(
    rows: seq<Cell>, aCard: nat, bCard: nat
  ) returns (hist: array<nat>)
    requires ValidRows(rows, aCard, bCard)
    ensures hist.Length == aCard * bCard
    ensures forall j: nat :: j < hist.Length ==>
      hist[j] == Histogram(rows, aCard, bCard)[j]
  {
    var k := aCard * bCard;
    hist := new nat[k](j => 0);
    ghost var model := Histogram([], aCard, bCard);

    var i: nat := 0;
    while i < |rows|
      invariant i <= |rows|
      invariant hist.Length == k
      invariant |model| == k
      invariant model == Histogram(rows[..i], aCard, bCard)
      invariant forall j: nat :: j < k ==> hist[j] == model[j]
      decreases |rows| - i
    {
      var c := rows[i];
      ValidRowsElement(rows, i, aCard, bCard);
      CellIndexBound(c, aCard, bCard);
      var idx := CellIndex(c, bCard);
      assert idx < k;
      assert rows[..i] + [c] == rows[..i + 1];

      ghost var nextModel :=
        model[idx := model[idx] + 1];

      var previous := hist[idx];
      assert previous == model[idx];
      hist[idx] := previous + 1;

      forall j: nat | j < k
        ensures hist[j] == nextModel[j]
      {
        if j == idx {
        } else {
        }
      }

      HistogramAppendCell(rows[..i], c, aCard, bCard);
      assert nextModel ==
        Histogram(rows[..i + 1], aCard, bCard);

      model := nextModel;
      i := i + 1;
    }

    assert i == |rows|;
    assert rows[..i] == rows;
  }

  method UserBoundedMarginal(
    db: seq<UserBlock>,
    cap: nat,
    aCard: nat,
    bCard: nat
  ) returns (hist: array<nat>)
    requires ValidDatabase(db, aCard, bCard)
    ensures hist.Length == aCard * bCard
    ensures forall j: nat :: j < hist.Length ==>
      hist[j] ==
        Histogram(FlattenBounded(db, cap), aCard, bCard)[j]
  {
    var rows := FlattenBounded(db, cap);
    FlattenBoundedValid(db, cap, aCard, bCard);
    hist := ArrayHistogram(rows, aCard, bCard);
  }
}

module PrivacyCost {

  datatype Rat = Rat(num: nat, den: nat)

  predicate ValidRat(r: Rat)
  {
    0 < r.den
  }

  predicate ValidCosts(costs: seq<Rat>)
    decreases |costs|
  {
    |costs| == 0 ||
    (ValidCosts(costs[..|costs| - 1]) &&
     ValidRat(costs[|costs| - 1]))
  }

  function ZeroRat(): Rat
  {
    Rat(0, 1)
  }

  function AddRat(x: Rat, y: Rat): Rat
  {
    Rat(
      x.num * y.den + y.num * x.den,
      x.den * y.den
    )
  }

  function LeRat(x: Rat, y: Rat): bool
  {
    x.num * y.den <= y.num * x.den
  }

  function SumRat(costs: seq<Rat>): Rat
    decreases |costs|
  {
    if |costs| == 0 then ZeroRat()
    else
      AddRat(
        SumRat(costs[..|costs| - 1]),
        costs[|costs| - 1]
      )
  }

  lemma SumRatAppend(costs: seq<Rat>, c: Rat)
    ensures SumRat(costs + [c]) == AddRat(SumRat(costs), c)
  {
    assert |costs + [c]| == |costs| + 1;
    assert (costs + [c])[..|costs|] == costs;
    assert (costs + [c])[|costs|] == c;
  }

  method CheckCosts(costs: seq<Rat>) returns (ok: bool)
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
    costs: seq<Rat>, budget: Rat
  ) returns (used: Rat, accepted: nat)
    requires ValidCosts(costs)
    requires ValidRat(budget)
    ensures accepted <= |costs|
    ensures used == SumRat(costs[..accepted])
    ensures LeRat(used, budget)
    ensures accepted == |costs| ||
      !LeRat(AddRat(used, costs[accepted]), budget)
  {
    used := ZeroRat();
    accepted := 0;

    while accepted < |costs| &&
      LeRat(AddRat(used, costs[accepted]), budget)
      invariant accepted <= |costs|
      invariant used == SumRat(costs[..accepted])
      invariant LeRat(used, budget)
      decreases |costs| - accepted
    {
      var c := costs[accepted];
      SumRatAppend(costs[..accepted], c);
      assert costs[..accepted] + [c] ==
        costs[..accepted + 1];
      used := AddRat(used, c);
      accepted := accepted + 1;
    }

    if accepted < |costs| {
      assert !LeRat(
        AddRat(used, costs[accepted]), budget
      );
    }
  }

  method CheckedSpendUntilBudget(
    costs: seq<Rat>, budget: Rat
  ) returns (ok: bool, used: Rat, accepted: nat)
    ensures !ok ==> used == ZeroRat() && accepted == 0
    ensures ok ==> accepted <= |costs|
    ensures ok ==> used == SumRat(costs[..accepted])
    ensures ok ==> LeRat(used, budget)
    ensures ok ==> (accepted == |costs| ||
      !LeRat(AddRat(used, costs[accepted]), budget))
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
  import opened DataModel
  import opened MarginalSpec
  import opened MarginalImpl

  method CheckRows(
    rows: seq<Cell>, aCard: nat, bCard: nat
  ) returns (ok: bool)
    ensures ok == ValidRows(rows, aCard, bCard)
    decreases |rows|
  {
    if |rows| == 0 {
      ok := true;
    } else {
      var prefixOk :=
        CheckRows(rows[..|rows| - 1], aCard, bCard);
      var c := rows[|rows| - 1];
      ok := prefixOk && c.a < aCard && c.b < bCard;
    }
  }

  method CheckDatabase(
    db: seq<UserBlock>, aCard: nat, bCard: nat
  ) returns (ok: bool)
    ensures ok == ValidDatabase(db, aCard, bCard)
    decreases |db|
  {
    if |db| == 0 {
      ok := true;
    } else {
      var prefixOk :=
        CheckDatabase(db[..|db| - 1], aCard, bCard);
      var rowsOk :=
        CheckRows(db[|db| - 1].rows, aCard, bCard);
      ok := prefixOk && rowsOk;
    }
  }

  method CheckedUserBoundedMarginal(
    db: seq<UserBlock>,
    cap: nat,
    aCard: nat,
    bCard: nat
  ) returns (ok: bool, hist: array<nat>)
    ensures hist.Length == aCard * bCard
    ensures ok ==> forall j: nat :: j < hist.Length ==>
      hist[j] ==
        Histogram(FlattenBounded(db, cap), aCard, bCard)[j]
  {
    ok := CheckDatabase(db, aCard, bCard);
    if ok {
      hist := UserBoundedMarginal(db, cap, aCard, bCard);
    } else {
      hist := new nat[aCard * bCard](j => 0);
    }
  }
}

module FoundationDemo {
  import opened DataModel
  import opened MarginalSpec
  import opened PrivacyCost
  import opened PythonBoundary

  method Main()
  {
    var db: seq<UserBlock> := [
      UserBlock(10, [
        Cell(0, 1), Cell(0, 1), Cell(1, 1)
      ]),
      UserBlock(11, [
        Cell(1, 0), Cell(0, 0)
      ])
    ];

    var added := UserBlock(12, [
      Cell(1, 1), Cell(1, 1), Cell(1, 1)
    ]);

    var dbOk := CheckDatabase(db, 2, 2);
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

    if ok && budgetOk &&
       hist[0] == 1 && hist[1] == 2 &&
       hist[2] == 1 && hist[3] == 0 &&
       used.num == 7 && used.den == 12 &&
       accepted == 2 {
      print "DP_FOUNDATION_OK\n";
    } else {
      print "DP_FOUNDATION_BAD\n";
    }

    print hist[0], " ", hist[1], " ",
          hist[2], " ", hist[3], "\n";
    print used.num, " ", used.den, " ",
          accepted, "\n";
  }
}
