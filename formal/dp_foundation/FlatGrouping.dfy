include "FoundationPilot.dfy"

module FlatGrouping {
  import opened DataModel
  import opened MarginalSpec
  import opened MarginalImpl

  datatype Flat = Flat(uid: nat, cell: Cell)

  predicate ValidFlat(rs: seq<Flat>, a: nat, b: nat)
    decreases |rs|
  {
    |rs| == 0 || (ValidFlat(rs[..|rs|-1], a, b) &&
      ValidCell(rs[|rs|-1].cell, a, b))
  }

  function Select(rs: seq<Flat>, u: nat): seq<Cell>
    decreases |rs|
  {
    if |rs| == 0 then [] else
      Select(rs[..|rs|-1], u) +
        (if rs[|rs|-1].uid == u then [rs[|rs|-1].cell] else [])
  }

  function Without(rs: seq<Flat>, u: nat): seq<Flat>
    decreases |rs|
  {
    if |rs| == 0 then [] else
      Without(rs[..|rs|-1], u) +
        (if rs[|rs|-1].uid == u then [] else [rs[|rs|-1]])
  }

  function Ids(rs: seq<Flat>): seq<nat>
    decreases |rs|
  {
    if |rs| == 0 then [] else
      var p := Ids(rs[..|rs|-1]);
      var u := rs[|rs|-1].uid;
      if u in p then p else p + [u]
  }

  function RemoveId(ids: seq<nat>, u: nat): seq<nat>
    decreases |ids|
  {
    if |ids| == 0 then [] else
      RemoveId(ids[..|ids|-1], u) +
        (if ids[|ids|-1] == u then [] else [ids[|ids|-1]])
  }

  predicate UniqueIds(ids: seq<nat>)
    decreases |ids|
  {
    |ids| == 0 || (UniqueIds(ids[..|ids|-1]) &&
      ids[|ids|-1] !in ids[..|ids|-1])
  }

  lemma SelectAppend(p:seq<Flat>, r:Flat, u:nat)
    ensures Select(p+[r],u) == Select(p,u)+(if r.uid==u then [r.cell] else [])
  { assert (p+[r])[..|p|] == p; assert (p+[r])[|p|] == r; }
  lemma WithoutAppend(p:seq<Flat>, r:Flat, u:nat)
    ensures Without(p+[r],u) == Without(p,u)+(if r.uid==u then [] else [r])
  { assert (p+[r])[..|p|] == p; assert (p+[r])[|p|] == r; }
  lemma IdsAppend(p:seq<Flat>, r:Flat)
    ensures Ids(p+[r]) == (if r.uid in Ids(p) then Ids(p) else Ids(p)+[r.uid])
  { assert (p+[r])[..|p|] == p; assert (p+[r])[|p|] == r; }
  lemma RemoveIdAppend(p:seq<nat>, v:nat, u:nat)
    ensures RemoveId(p+[v],u) == RemoveId(p,u)+(if v==u then [] else [v])
  { assert (p+[v])[..|p|] == p; assert (p+[v])[|p|] == v; }

  lemma IdFacts(rs: seq<Flat>, u: nat)
    ensures UniqueIds(Ids(rs))
    ensures (u in Ids(rs)) <==> (|Select(rs,u)| > 0)
    decreases |rs|
  {
    if |rs| > 0 {
      IdFacts(rs[..|rs|-1], u);
    }
  }

  lemma RemoveMembership(ids: seq<nat>, u: nat, v: nat)
    ensures (v in RemoveId(ids,u)) <==> (v in ids && v != u)
    decreases |ids|
  {
    if |ids| > 0 { RemoveMembership(ids[..|ids|-1],u,v); }
  }

  lemma SelectWithout(rs: seq<Flat>, u: nat, v: nat)
    ensures Select(Without(rs,u),v) ==
      (if u == v then [] else Select(rs,v))
    decreases |rs|
  {
    if |rs| > 0 {
      var p := rs[..|rs|-1];
      var r := rs[|rs|-1];
      assert rs == p+[r];
      SelectWithout(p,u,v);
      WithoutAppend(p,r,u);
      SelectAppend(p,r,v);
      if r.uid != u {
        SelectAppend(Without(p,u),r,v);
        assert Without(rs,u) == Without(p,u)+[r];
        assert Select(Without(rs,u),v) == Select(Without(p,u),v)+(if r.uid==v then [r.cell] else []);
      } else {
        assert Without(rs,u) == Without(p,u);
      }
      if u == v { assert Select(Without(rs,u),v) == []; }
      else { assert Select(Without(rs,u),v) == Select(rs,v); }
      if r.uid != u {
        assert (Without(p,u)+[r])[..|Without(p,u)|] == Without(p,u);
      }
    }
  }

  lemma IdsWithout(rs: seq<Flat>, u: nat)
    ensures Ids(Without(rs,u)) == RemoveId(Ids(rs),u)
    decreases |rs|
  {
    if |rs| > 0 {
      var p := rs[..|rs|-1];
      var r := rs[|rs|-1];
      assert rs == p+[r];
      IdsWithout(p,u);
      RemoveMembership(Ids(p),u,r.uid);
      WithoutAppend(p,r,u);
      IdsAppend(p,r);
      if r.uid != u { IdsAppend(Without(p,u),r); }
      if r.uid !in Ids(p) { RemoveIdAppend(Ids(p),r.uid,u); }
      if r.uid==u {
        assert Without(rs,u) == Without(p,u);
        assert Ids(Without(rs,u)) == Ids(Without(p,u));
        assert RemoveId(Ids(rs),u) == RemoveId(Ids(p),u);
      } else {
        assert Without(rs,u) == Without(p,u)+[r];
        assert Ids(Without(rs,u)) == (if r.uid in Ids(Without(p,u)) then Ids(Without(p,u)) else Ids(Without(p,u))+[r.uid]);
        assert (r.uid in Ids(Without(p,u))) <==> (r.uid in Ids(p));
        if r.uid in Ids(p) {
          assert Ids(rs) == Ids(p);
        } else {
          assert Ids(rs) == Ids(p)+[r.uid];
          assert RemoveId(Ids(rs),u) == RemoveId(Ids(p),u)+[r.uid];
        }
      }
      assert Ids(Without(rs,u)) == RemoveId(Ids(rs),u);
      RemoveMembership(Ids(p),u,r.uid);
      if r.uid != u {
        assert (Without(p,u)+[r])[..|Without(p,u)|] == Without(p,u);
      }
      if r.uid !in Ids(p) {
        assert (Ids(p)+[r.uid])[..|Ids(p)|] == Ids(p);
      }
    }
  }

  lemma SelectValid(rs: seq<Flat>, u: nat, a: nat, b: nat)
    requires ValidFlat(rs,a,b)
    ensures ValidRows(Select(rs,u),a,b)
    ensures ValidFlat(Without(rs,u),a,b)
    decreases |rs|
  {
    if |rs| > 0 {
      var p := rs[..|rs|-1];
      var r := rs[|rs|-1];
      assert rs == p+[r];
      SelectValid(p,u,a,b);
      SelectAppend(p,r,u);
      WithoutAppend(p,r,u);
      if r.uid == u {
        assert Without(rs,u) == Without(p,u);
        assert ValidFlat(Without(rs,u),a,b);
        assert (Select(p,u)+[r.cell])[..|Select(p,u)|] == Select(p,u);
      } else {
        assert Select(rs,u)==Select(p,u);
        assert ValidRows(Select(rs,u),a,b);
        assert (Without(p,u)+[r])[..|Without(p,u)|] == Without(p,u);
      }
    }
  }

  function Blocks(rs: seq<Flat>, ids: seq<nat>): seq<UserBlock>
    decreases |ids|
  {
    if |ids| == 0 then [] else
      Blocks(rs,ids[..|ids|-1]) +
        [UserBlock(ids[|ids|-1], Select(rs,ids[|ids|-1]))]
  }

  function BlockIds(db: seq<UserBlock>): seq<nat>
    decreases |db|
  {
    if |db| == 0 then [] else BlockIds(db[..|db|-1])+[db[|db|-1].uid]
  }

  function Lookup(db: seq<UserBlock>, u: nat): seq<Cell>
    decreases |db|
  {
    if |db| == 0 then [] else
      if db[|db|-1].uid == u then db[|db|-1].rows
      else Lookup(db[..|db|-1],u)
  }

  function Erase(db: seq<UserBlock>, u: nat): seq<UserBlock>
    decreases |db|
  {
    if |db| == 0 then [] else (Erase(db[..|db|-1],u) +
      (if db[|db|-1].uid == u then [] else [db[|db|-1]]))
  }

  lemma BlocksAppend(rs:seq<Flat>,ids:seq<nat>,v:nat)
    ensures Blocks(rs,ids+[v]) == Blocks(rs,ids)+[UserBlock(v,Select(rs,v))]
  { assert (ids+[v])[..|ids|]==ids; assert (ids+[v])[|ids|]==v; }
  lemma BlockIdsAppend(db:seq<UserBlock>, x:UserBlock)
    ensures BlockIds(db+[x]) == BlockIds(db)+[x.uid]
  { assert (db+[x])[..|db|]==db; assert (db+[x])[|db|]==x; }
  lemma LookupAppend(db:seq<UserBlock>,x:UserBlock,u:nat)
    ensures Lookup(db+[x],u) == (if x.uid==u then x.rows else Lookup(db,u))
  { assert (db+[x])[..|db|]==db; assert (db+[x])[|db|]==x; }
  lemma EraseAppend(db:seq<UserBlock>,x:UserBlock,u:nat)
    ensures Erase(db+[x],u) == Erase(db,u)+(if x.uid==u then [] else [x])
  { assert (db+[x])[..|db|]==db; assert (db+[x])[|db|]==x; }

  lemma BlocksFacts(rs: seq<Flat>, ids: seq<nat>, u: nat, a: nat, b: nat)
    requires ValidFlat(rs,a,b)
    ensures BlockIds(Blocks(rs,ids)) == ids
    ensures ValidDatabase(Blocks(rs,ids),a,b)
    ensures Lookup(Blocks(rs,ids),u) == (if u in ids then Select(rs,u) else [])
    decreases |ids|
  {
    if |ids| > 0 {
      var p := ids[..|ids|-1];
      var v := ids[|ids|-1];
      assert ids==p+[v];
      BlocksFacts(rs,p,u,a,b);
      BlocksAppend(rs,p,v);
      BlockIdsAppend(Blocks(rs,p),UserBlock(v,Select(rs,v)));
      LookupAppend(Blocks(rs,p),UserBlock(v,Select(rs,v)),u);
      SelectValid(rs,v,a,b);
      assert (Blocks(rs,p)+[UserBlock(v,Select(rs,v))])[..|Blocks(rs,p)|] == Blocks(rs,p);
    }
  }

  lemma BlocksWithout(rs: seq<Flat>, ids: seq<nat>, u: nat)
    ensures Blocks(Without(rs,u),RemoveId(ids,u)) == Erase(Blocks(rs,ids),u)
    decreases |ids|
  {
    if |ids| > 0 {
      var p := ids[..|ids|-1];
      var v := ids[|ids|-1];
      assert ids==p+[v];
      BlocksWithout(rs,p,u);
      BlocksAppend(rs,p,v);
      EraseAppend(Blocks(rs,p),UserBlock(v,Select(rs,v)),u);
      RemoveIdAppend(p,v,u);
      if v!=u { BlocksAppend(Without(rs,u),RemoveId(p,u),v); }
      SelectWithout(rs,u,v);
      if v==u {
        assert RemoveId(ids,u)==RemoveId(p,u);
        assert Erase(Blocks(rs,ids),u)==Erase(Blocks(rs,p),u);
      } else {
        assert Blocks(Without(rs,u),RemoveId(ids,u)) == Blocks(Without(rs,u),RemoveId(p,u))+[UserBlock(v,Select(rs,v))];
      }
      assert Blocks(Without(rs,u),RemoveId(ids,u))==Erase(Blocks(rs,ids),u);
      assert (Blocks(rs,p)+[UserBlock(v,Select(rs,v))])[..|Blocks(rs,p)|] == Blocks(rs,p);
      if v != u {
        assert (RemoveId(p,u)+[v])[..|RemoveId(p,u)|] == RemoveId(p,u);
      }
    }
  }

  function Group(rs: seq<Flat>): seq<UserBlock> { Blocks(rs,Ids(rs)) }

  lemma GroupFacts(rs: seq<Flat>, u: nat, a: nat, b: nat)
    requires ValidFlat(rs,a,b)
    ensures UniqueIds(BlockIds(Group(rs)))
    ensures ValidDatabase(Group(rs),a,b)
    ensures Lookup(Group(rs),u) == Select(rs,u)
    ensures Group(Without(rs,u)) == Erase(Group(rs),u)
  {
    IdFacts(rs,u);
    BlocksFacts(rs,Ids(rs),u,a,b);
    IdsWithout(rs,u);
    BlocksWithout(rs,Ids(rs),u);
  }

  method CollectIds(rs:seq<Flat>) returns (ids:seq<nat>)
    ensures ids==Ids(rs)
  {
    ids:=[];
    var i:nat:=0;
    while i<|rs|
      invariant i<=|rs|
      invariant ids==Ids(rs[..i])
      decreases |rs|-i
    {
      IdsAppend(rs[..i],rs[i]);
      assert rs[..i]+[rs[i]]==rs[..i+1];
      if rs[i].uid !in ids { ids:=ids+[rs[i].uid]; }
      i:=i+1;
    }
    assert rs[..i]==rs;
  }

  method CollectRows(rs:seq<Flat>,u:nat) returns (rows:seq<Cell>)
    ensures rows==Select(rs,u)
  {
    rows:=[];
    var i:nat:=0;
    while i<|rs|
      invariant i<=|rs|
      invariant rows==Select(rs[..i],u)
      decreases |rs|-i
    {
      SelectAppend(rs[..i],rs[i],u);
      assert rs[..i]+[rs[i]]==rs[..i+1];
      if rs[i].uid==u { rows:=rows+[rs[i].cell]; }
      i:=i+1;
    }
    assert rs[..i]==rs;
  }

  method GroupRecords(rs: seq<Flat>, a: nat, b: nat) returns (db: seq<UserBlock>)
    requires ValidFlat(rs,a,b)
    ensures db == Group(rs)
    ensures UniqueIds(BlockIds(db))
    ensures ValidDatabase(db,a,b)
  {
    var ids := CollectIds(rs);
    db := [];
    var i: nat := 0;
    while i < |ids|
      invariant i <= |ids|
      invariant db == Blocks(rs,ids[..i])
      decreases |ids|-i
    {
      var selected := CollectRows(rs,ids[i]);
      db := db + [UserBlock(ids[i],selected)];
      assert ids[..i+1][..i] == ids[..i];
      i := i+1;
    }
    assert ids[..i] == ids;
    GroupFacts(rs,0,a,b);
  }

  function Q(db: seq<UserBlock>, cap: nat, a: nat, b: nat): seq<nat> {
    Histogram(FlattenBounded(db,cap),a,b)
  }

  lemma QAppend(db: seq<UserBlock>, x: UserBlock, cap: nat, a: nat, b: nat)
    ensures Q(db+[x],cap,a,b) == VecAdd(Q(db,cap,a,b),Histogram(ClipRows(x.rows,cap),a,b))
  {
    FlattenBoundedAppend(db,x,cap);
    HistogramConcat(FlattenBounded(db,cap),ClipRows(x.rows,cap),a,b);
  }

  lemma VecSwap(x: seq<nat>, y: seq<nat>, z: seq<nat>)
    requires |x| == |y| == |z|
    ensures VecAdd(VecAdd(x,y),z) == VecAdd(VecAdd(x,z),y)
  {
    forall i:nat | i < |x|
      ensures VecAdd(VecAdd(x,y),z)[i] == VecAdd(VecAdd(x,z),y)[i]
    {}
  }

  lemma Absent(db: seq<UserBlock>, u: nat)
    requires u !in BlockIds(db)
    ensures Erase(db,u) == db
    ensures Lookup(db,u) == []
    decreases |db|
  {
    if |db| > 0 { Absent(db[..|db|-1],u); }
  }

  lemma BlockDecomposition(db: seq<UserBlock>,u:nat,cap:nat,a:nat,b:nat)
    requires UniqueIds(BlockIds(db))
    ensures Q(db,cap,a,b) == VecAdd(Q(Erase(db,u),cap,a,b),Histogram(ClipRows(Lookup(db,u),cap),a,b))
    decreases |db|
  {
    if |db| == 0 {
      VecAddZeroRight(Q(db,cap,a,b));
    } else {
      var p := db[..|db|-1];
      var x := db[|db|-1];
      assert db == p+[x];
      assert BlockIds(db) == BlockIds(p)+[x.uid];
      assert (BlockIds(p)+[x.uid])[..|BlockIds(p)|] == BlockIds(p);
      QAppend(p,x,cap,a,b);
      EraseAppend(p,x,u);
      LookupAppend(p,x,u);
      if x.uid == u {
        Absent(p,u);
        assert Erase(db,u)==p;
        assert Lookup(db,u)==x.rows;
        assert Q(db,cap,a,b) == VecAdd(Q(p,cap,a,b),Histogram(ClipRows(x.rows,cap),a,b));
      } else {
        BlockDecomposition(p,u,cap,a,b);
        QAppend(Erase(p,u),x,cap,a,b);
        VecSwap(Q(Erase(p,u),cap,a,b),Histogram(ClipRows(Lookup(p,u),cap),a,b),Histogram(ClipRows(x.rows,cap),a,b));
      }
    }
  }

  function FlatQuery(rs:seq<Flat>,cap:nat,a:nat,b:nat):seq<nat> { Q(Group(rs),cap,a,b) }

  // Removing ALL records of one UID, from arbitrary positions, preserves other users' order.
  lemma FlatUserSensitivity(rs:seq<Flat>,u:nat,cap:nat,a:nat,b:nat)
    requires ValidFlat(rs,a,b)
    ensures FlatQuery(rs,cap,a,b) ==
      VecAdd(FlatQuery(Without(rs,u),cap,a,b),Histogram(ClipRows(Select(rs,u),cap),a,b))
    ensures Sum(Histogram(ClipRows(Select(rs,u),cap),a,b)) <= cap
    ensures SumSquares(Histogram(ClipRows(Select(rs,u),cap),a,b)) <= cap*cap
  {
    GroupFacts(rs,u,a,b);
    BlockDecomposition(Group(rs),u,cap,a,b);
    SelectValid(rs,u,a,b);
    ClipRowsValid(Select(rs,u),cap,a,b);
    ClipRowsBound(Select(rs,u),cap);
    HistogramMass(ClipRows(Select(rs,u),cap),a,b);
    HistogramL2SquaredBound(ClipRows(Select(rs,u),cap),a,b);
    SquareMonotone(|ClipRows(Select(rs,u),cap)|,cap);
  }

  method FlatMarginal(rs:seq<Flat>,cap:nat,a:nat,b:nat) returns (hist:array<nat>)
    requires ValidFlat(rs,a,b)
    ensures hist.Length == a*b
    ensures hist[..] == FlatQuery(rs,cap,a,b)
  {
    var db := GroupRecords(rs,a,b);
    var rows:seq<Cell>:=[];
    var i:nat:=0;
    while i<|db|
      invariant i<=|db|
      invariant rows==FlattenBounded(db[..i],cap)
      decreases |db|-i
    {
      FlattenBoundedAppend(db[..i],db[i],cap);
      assert db[..i]+[db[i]]==db[..i+1];
      rows:=rows+ClipRows(db[i].rows,cap);
      i:=i+1;
    }
    assert db[..i]==db;
    FlattenBoundedValid(db,cap,a,b);
    hist := ArrayHistogram(rows,a,b);
    assert forall j:nat :: j < hist.Length ==> hist[j] == FlatQuery(rs,cap,a,b)[j];
  }
}
