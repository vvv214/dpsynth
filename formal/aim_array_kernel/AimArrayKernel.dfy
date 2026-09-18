module AimArrayKernel {

  datatype Rec = Rec(a: nat, b: nat)

  predicate ValidRecords(records: seq<Rec>, aCard: nat, bCard: nat)
  {
    0 < aCard && 0 < bCard &&
    forall i: nat :: i < |records| ==>
      records[i].a < aCard && records[i].b < bCard
  }

  function CountPair(records: seq<Rec>, x: int, y: int): nat
    decreases |records|
  {
    if |records| == 0 then 0
    else
      CountPair(records[..|records| - 1], x, y) +
      (if records[|records| - 1].a == x &&
          records[|records| - 1].b == y then 1 else 0)
  }

  lemma CountPairAppend(
    records: seq<Rec>, r: Rec, x: int, y: int
  )
    ensures CountPair(records + [r], x, y) ==
      CountPair(records, x, y) +
      (if r.a == x && r.b == y then 1 else 0)
  {
    assert |records + [r]| == |records| + 1;
    assert (records + [r])[..|records|] == records;
    assert (records + [r])[|records|] == r;
  }

  method ArrayTwoWayMarginal(
    records: seq<Rec>, aCard: nat, bCard: nat
  ) returns (hist: array2<nat>)
    requires ValidRecords(records, aCard, bCard)
    ensures hist.Length0 == aCard
    ensures hist.Length1 == bCard
    ensures forall x: nat, y: nat ::
      x < aCard && y < bCard ==>
        hist[x, y] == CountPair(records, x, y)
  {
    hist := new nat[aCard, bCard]((x, y) => 0);
    ghost var model :=
      seq(aCard, x => seq(bCard, y => 0));

    var i: nat := 0;
    while i < |records|
      invariant i <= |records|
      invariant hist.Length0 == aCard
      invariant hist.Length1 == bCard
      invariant |model| == aCard
      invariant forall x: nat :: x < aCard ==> |model[x]| == bCard
      invariant forall x: nat, y: nat ::
        x < aCard && y < bCard ==> hist[x, y] == model[x][y]
      invariant forall x: nat, y: nat ::
        x < aCard && y < bCard ==>
          model[x][y] == CountPair(records[..i], x, y)
      decreases |records| - i
    {
      var r := records[i];
      assert r.a < aCard && r.b < bCard;
      assert records[..i] + [r] == records[..i + 1];

      ghost var oldModel := model;
      ghost var nextRow :=
        oldModel[r.a][r.b := oldModel[r.a][r.b] + 1];
      ghost var nextModel := oldModel[r.a := nextRow];

      var previous := hist[r.a, r.b];
      assert previous == oldModel[r.a][r.b];
      hist[r.a, r.b] := previous + 1;

      forall x: nat, y: nat |
        x < aCard && y < bCard
        ensures hist[x, y] == nextModel[x][y]
        ensures nextModel[x][y] == CountPair(records[..i + 1], x, y)
      {
        CountPairAppend(records[..i], r, x, y);
        if x == r.a {
          assert nextModel[x] == nextRow;
          if y == r.b {
            assert nextRow[y] == oldModel[x][y] + 1;
            assert hist[x, y] == previous + 1;
          } else {
            assert nextRow[y] == oldModel[x][y];
            assert hist[x, y] == oldModel[x][y];
          }
        } else {
          assert nextModel[x] == oldModel[x];
          assert hist[x, y] == oldModel[x][y];
        }
      }

      model := nextModel;
      i := i + 1;
    }

    assert i == |records|;
    assert records[..i] == records;
  }

  method Main()
  {
    var records: seq<Rec> := [
      Rec(0, 1), Rec(1, 0), Rec(0, 1), Rec(1, 1), Rec(0, 0)
    ];
    var hist := ArrayTwoWayMarginal(records, 2, 2);

    if hist[0, 0] == 1 && hist[0, 1] == 2 &&
       hist[1, 0] == 1 && hist[1, 1] == 1 {
      print "AIM_ARRAY_OK\n";
    } else {
      print "AIM_ARRAY_BAD\n";
    }
    print hist[0, 0], " ", hist[0, 1], " ",
          hist[1, 0], " ", hist[1, 1], "\n";
  }
}
