include "FoundationPilot.dfy"

module NumericBoundary {
  import opened MarginalSpec

  const I64Max:nat := 9223372036854775807

  function Clamp(x:nat, ceiling:nat):nat {
    if x <= ceiling then x else ceiling
  }

  function Clamped(values:seq<nat>, ceiling:nat):seq<nat> {
    seq(|values|, i => Clamp(AtOrZero(values,i),ceiling))
  }

  ghost function DistanceSquared(x:seq<nat>,y:seq<nat>):int
    requires |x|==|y|
    decreases |x|
  {
    if |x|==0 then 0 else
      DistanceSquared(x[..|x|-1],y[..|y|-1]) +
      ((x[|x|-1] as int)-(y[|y|-1] as int))*((x[|x|-1] as int)-(y[|y|-1] as int))
  }

  lemma ClampDifference(x:nat,y:nat,ceiling:nat)
    requires y<=x
    ensures 0<=Clamp(x,ceiling)-Clamp(y,ceiling)<=x-y
  {
    if x<=ceiling {} else if y<=ceiling {} else {}
  }

  lemma DistanceBound(x:seq<nat>,y:seq<nat>,delta:seq<nat>)
    requires |x|==|y|==|delta|
    requires forall i:int :: 0<=i<|x| ==> 0<=(x[i] as int)-(y[i] as int)<=(delta[i] as int)
    ensures DistanceSquared(x,y)<=SumSquares(delta)
    decreases |x|
  {
    if |x|>0 {
      var n:=|x|-1;
      DistanceBound(x[..n],y[..n],delta[..n]);
      var d:nat:=(x[n] as int)-(y[n] as int);
      SquareMonotone(d,delta[n]);
    }
  }

  // Coordinate saturation is nonexpansive for an added user's nonnegative delta.
  lemma SaturatedDeltaBound(base:seq<nat>,delta:seq<nat>,ceiling:nat)
    requires |base|==|delta|
    ensures DistanceSquared(Clamped(VecAdd(base,delta),ceiling),
      Clamped(base,ceiling)) <= SumSquares(delta)
  {
    var x:=Clamped(VecAdd(base,delta),ceiling);
    var y:=Clamped(base,ceiling);
    forall i:int | 0<=i<|base|
      ensures 0<=(x[i] as int)-(y[i] as int)<=(delta[i] as int)
    {
      ClampDifference(base[i]+delta[i],base[i],ceiling);
    }
    DistanceBound(x,y,delta);
  }

  method Saturate(values:seq<nat>) returns (out:seq<nat>)
    ensures out==Clamped(values,I64Max)
    ensures |out|==|values|
    ensures forall i:int :: 0<=i<|out| ==> out[i]<=I64Max
  {
    var a:=new nat[|values|](i=>0);
    var i:nat:=0;
    while i<|values|
      invariant i<=|values|
      invariant a.Length==|values|
      invariant forall j:int :: 0<=j<i ==>
        a[j]==Clamp(values[j],I64Max) && a[j]<=I64Max
      decreases |values|-i
    {
      a[i]:=Clamp(values[i],I64Max);
      i:=i+1;
    }
    out:=a[..];
  }
}
