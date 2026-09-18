// NOT VERIFIED: solver timeouts in the stronger external-client example.
include "../GaussianGate.dfy"

module VerifiedClient {
  import G = GaussianGate
  import FI = FlatInput
  import PC = PrivacyCost

  lemma DemoArithmetic()
    ensures PC.AddRat(PC.Rat(0,1),PC.Rat(4,8))==PC.Rat(4,8)
    ensures PC.LeRat(PC.Rat(4,8),PC.Rat(3,4))
    ensures !PC.LeRat(PC.AddRat(PC.Rat(4,8),PC.Rat(4,8)),PC.Rat(3,4))
  { reveal PC.AddRat(); reveal PC.LeRat(); }

  // Positive external client: relies only on the exported gate interface.
  method TwoCalls(raw:seq<FI.RawRecord>)
    requires FI.RawValid(raw,2,2)
  {
    DemoArithmetic();
    var session := G.NewBudget(PC.Rat(3,4));
    var built := G.CheckedBuild(raw,2,2,2,4,1);
    assert built.Ready?;
    assert G.Cost(built.request)==PC.Rat(4,8);
    var first, output1 := session.Release(built.request);
    assert first;
    assert |output1|==4;
    assert session.Used()==PC.Rat(4,8);
    var second, output2 := session.Release(built.request);
    assert !second;
    assert output2==[];
    assert session.Used()==PC.Rat(4,8);
  }
}
