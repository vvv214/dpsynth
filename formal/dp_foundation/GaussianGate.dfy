include "FlatGrouping.dfy"
include "NumericBoundary.dfy"

module FlatInput {
  import opened DataModel
  import opened FlatGrouping
  datatype RawRecord = RawRecord(uid:int, a:int, b:int)

  predicate RawValid(raw:seq<RawRecord>, a:nat,b:nat) {
    forall i:int :: 0 <= i < |raw| ==>
      0 <= raw[i].uid && 0 <= raw[i].a < a && 0 <= raw[i].b < b
  }

  method Convert(raw:seq<RawRecord>, a:nat,b:nat)
    returns (ok:bool, rs:seq<Flat>)
    ensures ok <==> RawValid(raw,a,b)
    ensures ok ==> |rs|==|raw|
    ensures ok ==> ValidFlat(rs,a,b)
    ensures ok ==> forall i:int :: 0 <= i < |raw| ==>
      rs[i].uid == raw[i].uid && rs[i].cell.a == raw[i].a && rs[i].cell.b == raw[i].b
  {
    rs := [];
    var i:nat := 0;
    while i < |raw|
      invariant i <= |raw|
      invariant |rs|==i
      invariant ValidFlat(rs,a,b)
      invariant forall j:int :: 0 <= j < i ==>
        0 <= raw[j].uid && 0 <= raw[j].a < a && 0 <= raw[j].b < b &&
        rs[j].uid==raw[j].uid && rs[j].cell.a==raw[j].a && rs[j].cell.b==raw[j].b
      decreases |raw|-i
    {
      var r := raw[i];
      if r.uid < 0 || r.a < 0 || r.a >= a || r.b < 0 || r.b >= b {
        ok := false;
        assert !RawValid(raw,a,b);
        return;
      }
      var x := Flat(r.uid,Cell(r.a,r.b));
      assert (rs+[x])[..|rs|]==rs;
      assert (rs+[x])[|rs|]==x;
      rs := rs+[x];
      i := i+1;
    }
    ok := true;
  }
}

module RationalSemantics {
  import opened PrivacyCost

  ghost function Value(r:Rat):real {
    if r.den==0 then 0.0 else (r.num as real)/(r.den as real)
  }

  lemma RealAdd(a:real,b:real,c:real,d:real)
    requires b>0.0 && d>0.0
    ensures (a*d+c*b)/(b*d) == a/b+c/d
  {}
  lemma RealCompare(a:real,b:real,c:real,d:real)
    requires b>0.0 && d>0.0
    ensures a*d<=c*b <==> a/b<=c/d
  {}
  lemma CastProduct(a:nat,b:nat)
    ensures ((a*b) as real) == (a as real)*(b as real)
  {}

  ghost predicate Represents(r:Rat, v:real) {
    r.den>0 && (r.num as real)==v*(r.den as real)
  }
  lemma ValueRepresents(r:Rat)
    requires ValidRat(r)
    ensures Represents(r,Value(r))
  {}
  lemma Cancel(v:real,w:real,d:real)
    requires d>0.0 && v*d==w*d
    ensures v==w
  {}
  lemma {:induction false} RepresentationUnique(r:Rat,v:real,w:real)
    requires Represents(r,v) && Represents(r,w)
    ensures v==w
  {
    assert r.den>0;
    assert (r.den as real)>0.0;
    assert v*(r.den as real)==w*(r.den as real);
    assert (v-w)*(r.den as real)==0.0;
    Cancel(v,w,r.den as real);
  }
  lemma AddRepresentations(x:Rat,y:Rat,v:real,w:real)
    requires Represents(x,v) && Represents(y,w)
    ensures Represents(AddRat(x,y),v+w)
  {
    CastProduct(x.num,y.den);
    CastProduct(y.num,x.den);
    CastProduct(x.den,y.den);
  }
  lemma AddCorrect(x:Rat,y:Rat)
    requires ValidRat(x) && ValidRat(y)
    ensures ValidRat(AddRat(x,y))
    ensures Value(AddRat(x,y)) == Value(x)+Value(y)
  {
    ValueRepresents(x);
    ValueRepresents(y);
    AddRepresentations(x,y,Value(x),Value(y));
    ValueRepresents(AddRat(x,y));
    RepresentationUnique(AddRat(x,y),Value(AddRat(x,y)),Value(x)+Value(y));
  }

  lemma CompareCorrect(x:Rat,y:Rat)
    requires ValidRat(x) && ValidRat(y)
    ensures LeRat(x,y) <==> Value(x)<=Value(y)
  {
    assert x.den>0 && y.den>0;
    CastProduct(x.num,y.den);
    CastProduct(y.num,x.den);
    assert (x.num*y.den<=y.num*x.den) <==>
      ((x.num*y.den) as real)<=((y.num*x.den) as real);
    RealCompare(x.num as real,x.den as real,y.num as real,y.den as real);
  }

  lemma GaussianCalibration(cap:nat,vn:nat,vd:nat)
    requires vn>0 && vd>0
    ensures Value(Rat(cap*cap*vd,2*vn)) ==
      (cap as real)*(cap as real)/(2.0*((vn as real)/(vd as real)))
  {}
}

module GaussianGate {
  // EXTERNAL ASSUMPTION: the pinned OpenDP discrete-Gaussian backend has
  // zCDP cost <= cap^2 * varianceDen / (2 * varianceNum) at L2 sensitivity cap.
  // It may increase the scale for conservative floating-point calibration.
  // Fresh randomness and no extra observable outputs are trusted. Dafny checks
  // finite integer input range and output shape, NOT the probability law.
  module {:extern "trusted_gaussian"} GaussianBackend {
    method {:extern} {:axiom} Sample(center:seq<nat>, cap:nat, varianceNum:nat, varianceDen:nat)
      returns (output:seq<real>)
      requires varianceNum > 0 && varianceDen > 0
      requires forall i:int :: 0<=i<|center| ==> center[i]<=9223372036854775807
      ensures |output| == |center|
  }
  

  import opened DataModel
  import opened MarginalSpec
  import opened FlatGrouping
  import opened FlatInput
  import opened PrivacyCost
  import NB = NumericBoundary
  import Backend = GaussianBackend
  import opened RationalSemantics

  export provides FlatGrouping, FlatInput, PrivacyCost, RationalSemantics,
    Request, ValidRequest, Build, CheckedBuild, Cost, Dimension,
    Budget.Valid, Budget.Used, Budget.Limit, Budget.Release, NewBudget
    reveals Budget, BuildResult

  // Hidden constructor; ghost source is erased in generated Python.
  datatype Request = Request(ghost source:seq<Flat>, center:seq<nat>,
    cap:nat, a:nat,b:nat, varianceNum:nat, varianceDen:nat)
  datatype BuildResult = Rejected | Ready(request:Request)

  ghost opaque predicate CertifiedFamily(cap:nat,a:nat,b:nat) {
    forall rs:seq<Flat>, u:nat :: ValidFlat(rs,a,b) ==>
      FlatQuery(rs,cap,a,b) == VecAdd(FlatQuery(Without(rs,u),cap,a,b),
        Histogram(ClipRows(Select(rs,u),cap),a,b)) &&
      SumSquares(Histogram(ClipRows(Select(rs,u),cap),a,b)) <= cap*cap &&
      NB.DistanceSquared(NB.Clamped(FlatQuery(rs,cap,a,b),NB.I64Max),
        NB.Clamped(FlatQuery(Without(rs,u),cap,a,b),NB.I64Max))<=cap*cap
  }

  lemma CertifyFamily(cap:nat,a:nat,b:nat)
    ensures CertifiedFamily(cap,a,b)
  {
    reveal CertifiedFamily();
    forall rs:seq<Flat>, u:nat | ValidFlat(rs,a,b)
      ensures FlatQuery(rs,cap,a,b) == VecAdd(FlatQuery(Without(rs,u),cap,a,b),
        Histogram(ClipRows(Select(rs,u),cap),a,b)) &&
        SumSquares(Histogram(ClipRows(Select(rs,u),cap),a,b)) <= cap*cap &&
      NB.DistanceSquared(NB.Clamped(FlatQuery(rs,cap,a,b),NB.I64Max),
        NB.Clamped(FlatQuery(Without(rs,u),cap,a,b),NB.I64Max))<=cap*cap
    {
      FlatUserSensitivity(rs,u,cap,a,b);
      NB.SaturatedDeltaBound(FlatQuery(Without(rs,u),cap,a,b),
        Histogram(ClipRows(Select(rs,u),cap),a,b),NB.I64Max);
    }
  }

  ghost predicate ValidRequest(r:Request) {
    r.a>0 && r.b>0 && r.varianceNum>0 && r.varianceDen>0 &&
    ValidFlat(r.source,r.a,r.b) &&
    r.center == FlatQuery(r.source,r.cap,r.a,r.b) &&
    CertifiedFamily(r.cap,r.a,r.b)
  }

  function Cost(r:Request):Rat {
    Rat(r.cap*r.cap*r.varianceDen,2*r.varianceNum)
  }

  function Dimension(r:Request):nat { r.a*r.b }

  method Build(rs:seq<Flat>,cap:nat,a:nat,b:nat,vn:nat,vd:nat)
    returns (r:Request)
    requires a>0 && b>0 && vn>0 && vd>0
    requires ValidFlat(rs,a,b)
    ensures ValidRequest(r)
    ensures Dimension(r)==a*b
    ensures Cost(r) == Rat(cap*cap*vd,2*vn)
    ensures Value(Cost(r)) == (cap as real)*(cap as real)/(2.0*((vn as real)/(vd as real)))
  {
    var h := FlatMarginal(rs,cap,a,b);
    CertifyFamily(cap,a,b);
    GaussianCalibration(cap,vn,vd);
    r := Request(rs,h[..],cap,a,b,vn,vd);
  }

  // Signed public parameters and signed input records are checked in compiled code.
  method CheckedBuild(raw:seq<RawRecord>,cap:int,a:int,b:int,vn:int,vd:int)
    returns (result:BuildResult)
    ensures result.Ready? <==> (cap>=0 && a>0 && b>0 && vn>0 && vd>0 && RawValid(raw,a,b))
    ensures result.Ready? ==> Dimension(result.request)==a*b
    ensures result.Ready? ==> cap>=0 && a>0 && b>0 && vn>0 && vd>0
    ensures result.Ready? ==> ValidRequest(result.request)
    ensures result.Ready? ==> Cost(result.request) == Rat(cap*cap*vd,2*vn)
  {
    if cap<0 || a<=0 || b<=0 || vn<=0 || vd<=0 {
      result := Rejected;
      return;
    }
    var ok, rs := Convert(raw,a,b);
    if !ok { result := Rejected; return; }
    var r := Build(rs,cap,a,b,vn,vd);
    result := Ready(r);
  }

  class Budget {
    var used:Rat
    const limit:Rat

    ghost predicate Valid() reads this {
      ValidRat(used) && ValidRat(limit) && LeRat(used,limit)
    }
    function Used():Rat reads this { used }
    function Limit():Rat reads this { limit }

    constructor (budget:Rat)
      requires ValidRat(budget)
      ensures Valid() && Used()==ZeroRat() && Limit()==budget
    {
      limit := budget;
      used := ZeroRat();
    }

    // Both request constructor and budget fields are hidden from Dafny clients.
    // Each success calls the trusted backend exactly once; rejection calls it zero times.
    method Release(r:Request) returns (ok:bool,output:seq<real>)
      requires Valid() && ValidRequest(r)
      modifies this
      ensures Valid()
      ensures Limit()==old(Limit())
      ensures Value(Used()) <= Value(Limit())
      ensures ok ==> Value(Used())==Value(old(Used()))+Value(Cost(r))
      ensures ok <==> old(LeRat(AddRat(Used(),Cost(r)),Limit()))
      ensures ok ==> Used()==AddRat(old(Used()),Cost(r))
      ensures !ok ==> Used()==old(Used()) && output==[]
      ensures ok ==> |output|==Dimension(r)
    {
      AddCorrect(used,Cost(r));
      var next := AddRat(used,Cost(r));
      CompareCorrect(used,limit);
      CompareCorrect(next,limit);
      ok := LeRat(next,limit);
      if !ok { output := []; return; }
      used := next;
      var safeCenter := NB.Saturate(r.center);
      output := Backend.Sample(safeCenter,r.cap,r.varianceNum,r.varianceDen);
    }
  }

  method NewBudget(budget:Rat) returns (session:Budget)
    requires ValidRat(budget)
    ensures fresh(session) && session.Valid()
    ensures session.Used()==ZeroRat() && session.Limit()==budget
  {
    session := new Budget(budget);
  }
}
