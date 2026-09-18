module AimSingleMarginal {

  predicate ValidCells(cells: seq<nat>, k: nat)
  {
    0 < k &&
    forall i: nat :: i < |cells| ==> cells[i] < k
  }

  function Count(cells: seq<nat>, target: nat): nat
    decreases |cells|
  {
    if |cells| == 0 then 0
    else
      Count(cells[..|cells| - 1], target) +
      (if cells[|cells| - 1] == target then 1 else 0)
  }

  function HistogramSpec(cells: seq<nat>, k: nat): seq<nat>
  {
    seq(k, j => Count(cells, j))
  }

  lemma CountAppend(cells: seq<nat>, x: nat, target: nat)
    ensures Count(cells + [x], target) ==
      Count(cells, target) + (if x == target then 1 else 0)
  {
    assert |cells + [x]| == |cells| + 1;
    assert (cells + [x])[..|cells|] == cells;
    assert (cells + [x])[|cells|] == x;
  }

  method Marginal(cells: seq<nat>, k: nat) returns (hist: seq<nat>)
    requires ValidCells(cells, k)
    ensures |hist| == k
    ensures forall j: nat :: j < k ==> hist[j] == Count(cells, j)
  {
    hist := seq(k, j => 0);
    var i: nat := 0;

    while i < |cells|
      invariant i <= |cells|
      invariant |hist| == k
      invariant forall j: nat :: j < k ==>
        hist[j] == Count(cells[..i], j)
      decreases |cells| - i
    {
      var c := cells[i];
      assert c < k;
      assert cells[..i] + [c] == cells[..i + 1];

      var next := hist[c := hist[c] + 1];

      forall j: nat | j < k
        ensures next[j] == Count(cells[..i + 1], j)
      {
        CountAppend(cells[..i], c, j);
        if j == c {
          assert next[j] == hist[j] + 1;
        } else {
          assert next[j] == hist[j];
        }
      }

      hist := next;
      i := i + 1;
    }
  }

  lemma AddOneIsOneHot(cells: seq<nat>, k: nat, x: nat)
    requires ValidCells(cells, k)
    requires x < k
    ensures HistogramSpec(cells + [x], k)[x] ==
      HistogramSpec(cells, k)[x] + 1
    ensures forall j: nat :: j < k && j != x ==>
      HistogramSpec(cells + [x], k)[j] == HistogramSpec(cells, k)[j]
  {
    CountAppend(cells, x, x);
    forall j: nat | j < k && j != x
      ensures HistogramSpec(cells + [x], k)[j] ==
        HistogramSpec(cells, k)[j]
    {
      CountAppend(cells, x, j);
    }
  }

  method Main()
  {
    var cells: seq<nat> := [0, 2, 2, 1, 2];
    var hist := Marginal(cells, 3);

    assert |hist| == 3;
    assert hist[0] == 1;
    assert hist[1] == 1;
    assert hist[2] == 3;

    AddOneIsOneHot(cells, 3, 1);

    print "AIM_MARGINAL_OK\n";
    print hist, "\n";
  }
}
