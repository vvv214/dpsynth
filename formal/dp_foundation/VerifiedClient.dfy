// Public client checked independently through exported contracts.
include "GaussianGate.dfy"

module VerifiedClient {
  import G = GaussianGate
  import FI = FlatInput
  import PC = PrivacyCost

  lemma {:isolate_assertions} DemoArithmetic()
    ensures PC.AddRat(PC.Rat(0,1),PC.Rat(4,8))==PC.Rat(4,8)
    ensures PC.LeRat(PC.Rat(4,8),PC.Rat(3,4))
    ensures !PC.LeRat(PC.AddRat(PC.Rat(4,8),PC.Rat(4,8)),PC.Rat(3,4))
  { reveal PC.AddRat(); reveal PC.LeRat(); }

  // Positive external client: relies only on the exported gate interface.
  method {:isolate_assertions} TwoCalls(raw:seq<FI.RawRecord>)
    requires FI.RawValid(raw,2,2)
  {
    DemoArithmetic();
    var session := G.NewBudget(PC.Rat(3,4));
    var built := G.CheckedBuild(raw,2,2,2,4,1);
    assert built.Ready?;
    assert G.Cost(built.request)==PC.Rat(4,8);
    assert session.Used()==PC.Rat(0,1);
    assert session.Limit()==PC.Rat(3,4);
    ghost var before1 := session.Used();
    ghost var charge := G.Cost(built.request);
    ghost var allowed1 := PC.LeRat(PC.AddRat(before1,charge),session.Limit());
    assert allowed1;
    var first, output1 := session.Release(built.request);
    assert first==allowed1;
    assert session.Used()==PC.AddRat(before1,charge);
    assert first;
    assert |output1|==4;
    assert session.Used()==PC.Rat(4,8);
    ghost var before2 := session.Used();
    ghost var allowed2 := PC.LeRat(PC.AddRat(before2,charge),session.Limit());
    assert !allowed2;
    var second, output2 := session.Release(built.request);
    assert second==allowed2;
    assert !second;
    assert output2==[];
    assert session.Used()==PC.Rat(4,8);
  }
}
