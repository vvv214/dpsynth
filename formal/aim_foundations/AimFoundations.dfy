module AimFoundations {

  datatype Rec = Rec(a: nat, b: nat)

  predicate ValidRecords(records: seq<Rec>, aCard: nat, bCard: nat)
  {
    0 < aCard && 0 < bCard &&
    forall i: nat :: i < |records| ==>
      records[i].a < aCard && records[i].b < bCard
  }

  function CountPair(records: seq<Rec>, x: nat, y: nat): nat
    decreases |records|
  {
    if |records| == 0 then 0
    else
      CountPair(records[..|records| - 1], x, y) +
      (if records[|records| - 1].a == x &&
          records[|records| - 1].b == y then 1 else 0)
  }

  function Histogram2DSpec(
    records: seq<Rec>, aCard: nat, bCard: nat
  ): seq<seq<nat>>
  {
    seq(aCard, x: int requires 0 <= x < aCard =>
      seq(bCard, y: int requires 0 <= y < bCard =>
        CountPair(records, x as nat, y as nat)))
  }

  lemma CountPairAppend(
    records: seq<Rec>, r: Rec, x: nat, y: nat
  )
    ensures CountPair(records + [r], x, y) ==
      CountPair(records, x, y) +
      (if r.a == x && r.b == y then 1 else 0)
  {
    assert |records + [r]| == |records| + 1;
    assert (records + [r])[..|records|] == records;
    assert (records + [r])[|records|] == r;
  }

  method TwoWayMarginal(
    records: seq<Rec>, aCard: nat, bCard: nat
  ) returns (hist: seq<seq<nat>>)
    requires ValidRecords(records, aCard, bCard)
    ensures |hist| == aCard
    ensures forall x: nat :: x < aCard ==> |hist[x]| == bCard
    ensures forall x: nat, y: nat ::
      x < aCard && y < bCard ==>
        hist[x][y] == CountPair(records, x, y)
  {
    hist := seq(aCard, x: int requires 0 <= x < aCard =>
      seq(bCard, y: int requires 0 <= y < bCard => 0));

    var i: nat := 0;
    while i < |records|
      invariant i <= |records|
      invariant |hist| == aCard
      invariant forall x: nat :: x < aCard ==> |hist[x]| == bCard
      invariant forall x: nat, y: nat ::
        x < aCard && y < bCard ==>
          hist[x][y] == CountPair(records[..i], x, y)
      decreases |records| - i
    {
      var r := records[i];
      assert r.a < aCard && r.b < bCard;
      assert records[..i] + [r] == records[..i + 1];

      var row := hist[r.a];
      var nextRow := row[r.b := row[r.b] + 1];
      var next := hist[r.a := nextRow];

      forall x: nat, y: nat |
        x < aCard && y < bCard
        ensures next[x][y] == CountPair(records[..i + 1], x, y)
      {
        CountPairAppend(records[..i], r, x, y);
        if x == r.a {
          assert next[x] == nextRow;
          assert row == hist[x];
          if y == r.b {
            assert nextRow[y] == row[y] + 1;
          } else {
            assert nextRow[y] == row[y];
          }
        } else {
          assert next[x] == hist[x];
        }
      }

      hist := next;
      i := i + 1;
    }

    assert records[..i] == records;
  }

  lemma AddOnePairIsOneHot(
    records: seq<Rec>, aCard: nat, bCard: nat, r: Rec
  )
    requires ValidRecords(records, aCard, bCard)
    requires r.a < aCard && r.b < bCard
    ensures Histogram2DSpec(records + [r], aCard, bCard)[r.a][r.b] ==
      Histogram2DSpec(records, aCard, bCard)[r.a][r.b] + 1
    ensures forall x: nat, y: nat ::
      x < aCard && y < bCard && (x != r.a || y != r.b) ==>
        Histogram2DSpec(records + [r], aCard, bCard)[x][y] ==
        Histogram2DSpec(records, aCard, bCard)[x][y]
  {
    CountPairAppend(records, r, r.a, r.b);
    forall x: nat, y: nat |
      x < aCard && y < bCard && (x != r.a || y != r.b)
      ensures Histogram2DSpec(records + [r], aCard, bCard)[x][y] ==
        Histogram2DSpec(records, aCard, bCard)[x][y]
    {
      CountPairAppend(records, r, x, y);
    }
  }

  function Sum(costs: seq<nat>): nat
    decreases |costs|
  {
    if |costs| == 0 then 0
    else Sum(costs[..|costs| - 1]) + costs[|costs| - 1]
  }

  lemma SumAppend(costs: seq<nat>, c: nat)
    ensures Sum(costs + [c]) == Sum(costs) + c
  {
    assert |costs + [c]| == |costs| + 1;
    assert (costs + [c])[..|costs|] == costs;
    assert (costs + [c])[|costs|] == c;
  }

  // costs are exact nonnegative zCDP budget units under a shared denominator.
  // This method verifies accounting and stopping, not the composition theorem itself.
  method SpendUntilBudget(
    costs: seq<nat>, budget: nat
  ) returns (used: nat, accepted: nat)
    ensures accepted <= |costs|
    ensures used == Sum(costs[..accepted])
    ensures used <= budget
    ensures accepted == |costs| || used + costs[accepted] > budget
  {
    used := 0;
    accepted := 0;

    while accepted < |costs| && used + costs[accepted] <= budget
      invariant accepted <= |costs|
      invariant used == Sum(costs[..accepted])
      invariant used <= budget
      decreases |costs| - accepted
    {
      var c := costs[accepted];
      SumAppend(costs[..accepted], c);
      assert costs[..accepted] + [c] == costs[..accepted + 1];
      used := used + c;
      accepted := accepted + 1;
    }

    if accepted < |costs| {
      assert used + costs[accepted] > budget;
    }
  }

  method Main()
  {
    var records: seq<Rec> := [
      Rec(0, 1), Rec(1, 0), Rec(0, 1), Rec(1, 1), Rec(0, 0)
    ];
    var hist := TwoWayMarginal(records, 2, 2);

    assert hist[0][0] == 1;
    assert hist[0][1] == 2;
    assert hist[1][0] == 1;
    assert hist[1][1] == 1;

    AddOnePairIsOneHot(records, 2, 2, Rec(1, 0));

    var costs: seq<nat> := [3, 4, 5, 2];
    var used, accepted := SpendUntilBudget(costs, 10);
    assert used <= 10;

    print "AIM_FOUNDATIONS_OK\n";
    print hist, "\n";
    print used, " ", accepted, "\n";
  }
}
