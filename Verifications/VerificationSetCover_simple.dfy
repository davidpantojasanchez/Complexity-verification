include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method VerifySetCover_simple(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (accepted:bool, ghost counter:nat)
  requires SetCoverValidInstance(U, S)
  requires |I| <= |S|
  requires (forall s | s in I :: |s| <= |U|)
  ensures accepted == SetCoverCertificate(U, S, k, I)
  ensures accepted ==> SetCover(U, S, k)
  ensures counter <= PolyVerifySetCover_simple(U, S, k)
{
  assert forall i | i in I :: |i| <= |U|;
  counter := 0;
  var U' := U; counter := counter + |U|;
  accepted:= true;
  counter := counter + 1;
  if (k < |I|) {
    return false, counter;
  }
  var I_seq_S:bool;
  I_seq_S, counter := IsSubset(U, I, S, counter);

  if (!I_seq_S) {
    assert counter <= |U| + 1 + PolyIsSubset_simple(U, I, S);
    PolyVerifySetCoverSpecialCaseBound_simple(U, S, k, I);
    assert counter <= PolyVerifySetCover_simple(U, S, k);
    return false, counter;
  }
  while (U' != {} && accepted)
    decreases |U'|
    invariant U' <= U 
    invariant accepted == IsCover(U-U',I)
    invariant counter <= |U| + PolyIsSubset_simple(U, I, S) + 1 + (|U| - |U'|)*(PolyCheckUniverseElement_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    accepted, U', counter := CheckUniverseElement_simple(U, S, k, I, U', counter);
  }
  counter := counter + 1;
  assert counter <= |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*(PolyCheckUniverseElement_simple(U, S, k) + 1);
  PolyVerifySetCoverBound_simple(U, S, k, I);
  assert accepted ==> U-U' == U;
  assert accepted ==> SetCoverCertificate(U, S, k, I);
}


method IsSubset(U:set<int>, S1:set<set<int>>, S2:set<set<int>>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  requires forall s |s in S2 :: s <= U
  ensures b == (S1 <= S2)
  ensures counter <= counter_in + PolyIsSubset_simple(U, S1, S2)
{
  counter := counter_in;
  b := true;
  var S1':= S1; counter := counter + |U|*|S1|;
  while (S1' != {})
    decreases |S1'|
    invariant S1' <= S1
    invariant b == ((S1 - S1') <= S2)
    invariant counter <= counter_in + |S1|*|U| + 1 + (|S1| - |S1'|)*(PolyIsSubsetStep_simple(U, S1, S2) + 1)
  {
    counter := counter + 1;
    S1', b, counter := IsSubsetStep_simple(U, S1, S2, S1', counter, b);
  }
  counter := counter + 1;
}


method IsSubsetStep_simple(U:set<int>, S1:set<set<int>>, S2:set<set<int>>, S1':set<set<int>>, ghost counter_in:nat, b:bool) returns (S1'':set<set<int>>, b':bool, ghost counter:nat)
  requires S1' != {}
  requires S1' <= S1
  requires b == ((S1 - S1') <= S2)
  ensures |S1''| == |S1'| - 1
  ensures S1'' <= S1
  ensures b' == ((S1 - S1'') <= S2)
  ensures counter <= counter_in + PolyIsSubsetStep_simple(U, S1, S2)
{
  counter := counter_in;
  SubsetCardinalityBound(S1', S1);
  var s:set<int> :| s in S1'; counter := counter + |U|;
  b' := b && s in S2; counter := counter + |S2|*|U|;
  S1'' := S1' - {s}; counter := counter + |S1|*|U|;
}


method CheckUniverseElement_simple(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>, ghost counter_in:nat) returns (b1:bool, U'':set<int>, ghost counter:nat)
  requires U' != {}
  requires U' <= U
  requires |I| <= |S|
  requires IsCover(U - U', I)
  ensures |U''| == |U'| - 1
  ensures U'' <= U
  ensures b1 == IsCover(U - U'', I)
  ensures counter <= counter_in + PolyCheckUniverseElement_simple(U, S, k)
{
  counter := counter_in;
  var u :| u in U'; counter := counter + 1;
  U'' := U' - {u}; counter := counter + |U|;

  var I' := I; counter := counter + |S|*|U|;
  b1:= false;
  while (I' != {} && !b1)
    decreases |I'|
    invariant I' <= I
    invariant b1 == (exists i' | i' in I - I' :: u in i')
    invariant counter <= counter_in + |S|*|U| + |U| + 1 + (|I|-|I'|)*(PolyCheckCoverSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    b1, I', counter := CheckCoverSet_simple(U, S, k, I, I', u, counter);
  }
  counter := counter + 1;
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|I|-|I'|)*(PolyCheckCoverSet_simple(U, S, k) + 1);
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|S|)*(PolyCheckCoverSet_simple(U, S, k) + 1);
  assert U - U'' == U - U' + {u};
}


method CheckCoverSet_simple(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, I':set<set<int>>, u:int, ghost counter_in:nat) returns (b2:bool, I'':set<set<int>>, ghost counter:nat)
  requires I' != {}
  requires I' <= I
  requires !(exists i' | i' in I - I' :: u in i')
  ensures |I''| == |I'| - 1
  ensures I'' <= I
  ensures b2 == (exists i' | i' in I - I'' :: u in i')
  ensures counter == counter_in + PolyCheckCoverSet_simple(U, S, k)
{
  counter := counter_in;
  var i :| i in I'; counter := counter + |U|;
  b2 := u in i; counter := counter + |U|;
  I'' := I' - {i}; counter := counter + |S|*|U|;
}


ghost function PolyIsSubsetStep_simple(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|U| + |S2|*|U| + |U|
}
ghost function PolyIsSubset_simple(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|S1|*|U| + |S1|*|S2|*|U| + 2*|S1|*|U| + |S1| + 2
}
ghost function PolyCheckCoverSet_simple(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  |S|*|U| + 2*|U|
}
ghost function PolyCheckUniverseElement_simple(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  ensures |S|*|U| + |U| + 2 + |S|*(PolyCheckCoverSet_simple(U, S, k) + 1) == o
{
  |U|*|S|*|S| + 3*|U|*|S| + |U| + |S| + 2
}


ghost function PolyVerifySetCover_simple(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  //ensures PolyIsSubset_simple(U, I, S) + |U| + 1 <= o
  //ensures |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*(PolyCheckUniverseElement_simple(U, S, k, I) + 1) <= o
{
  /*
  calc <= {
    PolyIsSubset_simple(U, I, S) + |U| + 1;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + |U| + 3;
    4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4;
    5*|S|*|S|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + |S| + 4;
  }
  
  calc <= {
    |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*(PolyCheckUniverseElement_simple(U, S, k, I) + 1);
    |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*PolyCheckUniverseElement_simple(U, S, k, I) + |U|;
    |U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 4 + |U|*PolyCheckUniverseElement_simple(U, S, k, I) + |U|;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*PolyCheckUniverseElement_simple(U, S, k, I);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*(3*|I|*|I| + 2*|I| + |U| + 2);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + 3*|I|*|I|*|U| + 2*|I|*|U| + |U|*|U| + 2*|U|;
    4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4;
    5*|S|*|S|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + |S| + 4;
  }*/
  
  // 4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4
  |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4
}


lemma PolyVerifySetCoverBound_simple(U: set<int>, S: set<set<int>>, k: nat, I: set<set<int>>)
  requires |I| <= |S|
  ensures |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*(PolyCheckUniverseElement_simple(U, S, k) + 1) <= PolyVerifySetCover_simple(U, S, k)
{
  calc <= {
    |U| + PolyIsSubset_simple(U, I, S) + 2 + |U|*(PolyCheckUniverseElement_simple(U, S, k) + 1);
    |U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + |U|*(PolyCheckUniverseElement_simple(U, S, k) + 1) + 4;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*PolyCheckUniverseElement_simple(U, S, k);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + (|S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + 2*|U|);
    assert 2*|I|*|U| <= 2*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, 2*|U|, |S|, 2*|U|);
    }
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |I|*|I|*|U| <= |I|*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, |I|*|U|, |S|, |I|*|U|);
      assert |I|*|I|*|U| <= |S|*|I|*|U|;
      assert |S|*|I|*|U| <= |I|*|S|*|U|;
    }
    |I|*|S|*|U| + |I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    2*|I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, |S|*|U|, |S|, |S|*|U|);
    }
    2*|S|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4;
  }
}

lemma PolyVerifySetCoverSpecialCaseBound_simple(U: set<int>, S: set<set<int>>, k: nat, I: set<set<int>>)
  requires |I| <= |S|
  ensures |U| + 1 + PolyIsSubset_simple(U, I, S) <= PolyVerifySetCover_simple(U, S, k)
{
  calc <= {
    |U| + 1 + PolyIsSubset_simple(U, I, S);
    |U| + 1 + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |U| + |I| + 3;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, |U|*|S|, |S|, |U|*|S|);
    }
    |I|*|I|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    assert |I|*|I|*|U| <= |I|*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, |I|*|U|, |S|, |I|*|U|);
    }
    |I|*|S|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      MultiplicationPreservesOrder(|I|, |S|*|U|, |S|, |S|*|U|);
    }
    |S|*|S|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    2*|S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4;
    PolyVerifySetCover_simple(U, S, k);
  }
}
