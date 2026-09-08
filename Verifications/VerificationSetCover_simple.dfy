include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (accepted:bool, ghost counter:nat)   
  requires SetCoverValidInstance(U, S)
  requires SetCoverAdmissibleCertificate(U, I)
  ensures accepted == SetCoverCertificate(U, S, k, I)
  ensures accepted ==> SetCover(U, S, k)
  ensures counter <= poly(U, S, k)
{
  assert forall i | i in I :: |i| <= |U|;
  counter := 0;
  var U' := U; counter := counter + |U|;
  accepted:= true;
  counter := counter + 1;
  if (k < |I| || |S| < |I|) {
    if I <= S {
      if_smaller_then_less_cardinality(I, S);
    }
    return false, counter;
  }
  var I_seq_S:bool;
  I_seq_S, counter := isSubset(U, I, S, counter);

  if (!I_seq_S) {
    assert counter <= |U| + 1 + poly_isSubset(U, I, S);
    counter_simplification_special_case(U, S, k, I);
    assert counter <= poly(U, S, k);
    return false, counter;
  }
  while (U' != {} && accepted)
    decreases |U'|
    invariant U' <= U 
    invariant accepted == isCover(U-U',I)
    invariant counter <= |U| + poly_isSubset(U, I, S) + 1 + (|U| - |U'|)*(poly_outer_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    accepted, U', counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  counter := counter + 1;
  assert counter <= |U| + poly_isSubset(U, I, S) + 2 + |U|*(poly_outer_loop(U, S, k) + 1);
  counter_simplification(U, S, k, I);
  assert accepted ==> U-U' == U;
  assert accepted ==> SetCoverCertificate(U, S, k, I);
}


method isSubset(U:set<int>, S1:set<set<int>>, S2:set<set<int>>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  requires forall s |s in S2 :: s <= U
  ensures b == (S1 <= S2)
  ensures counter <= counter_in + poly_isSubset(U, S1, S2)
{
  counter := counter_in;
  b := true;
  var S1':= S1; counter := counter + |U|*|S1|;
  while (S1' != {})
    // Termination
    decreases |S1'|
    // Regular invariants
    invariant b == ((S1 - S1') <= S2)
    invariant S1' <= S1
    // Counter
    invariant counter <= counter_in + |S1|*|U| + 1 + (|S1| - |S1'|)*(poly_isSubset_loop(U, S1, S2) + 1)
  {
    counter := counter + 1;
    S1', b, counter := isSubset_loop(U, S1, S2, S1', counter, b);
  }
  counter := counter + 1;
}


method isSubset_loop(U:set<int>, S1:set<set<int>>, S2:set<set<int>>, S1':set<set<int>>, ghost counter_in:nat, b:bool) returns (S1'':set<set<int>>, b':bool, ghost counter:nat)
  // Termination in
  requires S1' != {}
  // Invariant in
  requires b == ((S1 - S1') <= S2)
  requires S1' <= S1
  // Termination out
  ensures |S1''| == |S1'| - 1
  // Invariant out
  ensures b' == ((S1 - S1'') <= S2)
  ensures S1'' <= S1
  // Counter
  ensures counter <= counter_in + poly_isSubset_loop(U, S1, S2)
{
  counter := counter_in;
  if_smaller_then_less_cardinality(S1', S1);
  var s:set<int> :| s in S1'; counter := counter + |U|;
  b' := b && s in S2; counter := counter + |S2|*|U|;
  S1'' := S1' - {s}; counter := counter + |S1|*|U|;
}


method verifySetCover_outer_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>, ghost counter_in:nat) returns (b1:bool, U'':set<int>, ghost counter:nat)
  // Termination in
  requires U' != {}
  // Invariant in
  requires U' <= U
  requires isCover(U - U', I)
  requires |I| <= |S|
  // Termination out
  ensures |U''| == |U'| - 1
  // Invariant out
  ensures U'' <= U
  ensures b1 == isCover(U - U'', I)
  // Counter
  ensures counter <= counter_in + poly_outer_loop(U, S, k)
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
    invariant counter <= counter_in + |S|*|U| + |U| + 1 + (|I|-|I'|)*(poly_inner_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    b1, I', counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  counter := counter + 1;
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|I|-|I'|)*(poly_inner_loop(U, S, k) + 1);
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|S|)*(poly_inner_loop(U, S, k) + 1);
  assert U - U'' == U - U' + {u};
}


method verifySetCover_inner_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, I':set<set<int>>, u:int, ghost counter_in:nat) returns (b2:bool, I'':set<set<int>>, ghost counter:nat)
  // Termination in
  requires I' != {}
  // Invariant in
  requires I' <= I
  requires !(exists i' | i' in I - I' :: u in i')
  // Termination out
  ensures |I''| == |I'| - 1
  // Invariant out
  ensures I'' <= I
  ensures b2 == (exists i' | i' in I - I'' :: u in i')
  // Counter
  ensures counter == counter_in + poly_inner_loop(U, S, k)
{
  counter := counter_in;
  var i :| i in I'; counter := counter + |U|;
  b2 := u in i; counter := counter + |U|;
  I'' := I' - {i}; counter := counter + |S|*|U|;
}


ghost function poly_isSubset_loop(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|U| + |S2|*|U| + |U|
}
ghost function poly_isSubset(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|S1|*|U| + |S1|*|S2|*|U| + 2*|S1|*|U| + |S1| + 2
}
ghost function poly_inner_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  |S|*|U| + 2*|U|
}
ghost function poly_outer_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  ensures |S|*|U| + |U| + 2 + |S|*(poly_inner_loop(U, S, k) + 1) == o
{
  |U|*|S|*|S| + 3*|U|*|S| + |U| + |S| + 2
}


ghost function poly(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  //ensures poly_isSubset(U, I, S) + |U| + 1 <= o 
  //ensures |U| + poly_isSubset(U, I, S) + 2 + |U|*(poly_outer_loop(U, S, k, I) + 1) <= o
{
  /*
  calc <= {
    poly_isSubset(U, I, S) + |U| + 1;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + |U| + 3;
    4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4;
    5*|S|*|S|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + |S| + 4;
  }
  
  calc <= {
    |U| + poly_isSubset(U, I, S) + 2 + |U|*(poly_outer_loop(U, S, k, I) + 1);
    |U| + poly_isSubset(U, I, S) + 2 + |U|*poly_outer_loop(U, S, k, I) + |U|;
    |U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 4 + |U|*poly_outer_loop(U, S, k, I) + |U|;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*poly_outer_loop(U, S, k, I);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*(3*|I|*|I| + 2*|I| + |U| + 2);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + 3*|I|*|I|*|U| + 2*|I|*|U| + |U|*|U| + 2*|U|;
    4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4;
    5*|S|*|S|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + |S| + 4;
  }*/
  
  // 4*|I|*|I|*|U| + |I|*|S|*|U| + 4*|I|*|U| + |U|*|U| + |I| + 4*|U| + 4
  |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4
}


lemma counter_simplification(U: set<int>, S: set<set<int>>, k: nat, I: set<set<int>>)
  requires |I| <= |S|
  ensures |U| + poly_isSubset(U, I, S) + 2 + |U|*(poly_outer_loop(U, S, k) + 1) <= poly(U, S, k)
{
  calc <= {
    |U| + poly_isSubset(U, I, S) + 2 + |U|*(poly_outer_loop(U, S, k) + 1);
    |U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + |U|*(poly_outer_loop(U, S, k) + 1) + 4;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + |U|*poly_outer_loop(U, S, k);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 4 + (|S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + 2*|U|);
    assert 2*|I|*|U| <= 2*|S|*|U| by {
      mult_preserves_order(|I|, 2*|U|, |S|, 2*|U|);
    }
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |I|*|I|*|U| <= |I|*|S|*|U| by {
      mult_preserves_order(|I|, |I|*|U|, |S|, |I|*|U|);
      assert |I|*|I|*|U| <= |S|*|I|*|U|;
      assert |S|*|I|*|U| <= |I|*|S|*|U|;
    }
    |I|*|S|*|U| + |I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    2*|I|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      mult_preserves_order(|I|, |S|*|U|, |S|, |S|*|U|);
    }
    2*|S|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4;
  }
}

lemma counter_simplification_special_case(U: set<int>, S: set<set<int>>, k: nat, I: set<set<int>>)
  requires |I| <= |S|
  ensures |U| + 1 + poly_isSubset(U, I, S) <= poly(U, S, k)
{
  calc <= {
    |U| + 1 + poly_isSubset(U, I, S);
    |U| + 1 + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |U| + |I| + 3;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      mult_preserves_order(|I|, |U|*|S|, |S|, |U|*|S|);
    }
    |I|*|I|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    assert |I|*|I|*|U| <= |I|*|S|*|U| by {
      mult_preserves_order(|I|, |I|*|U|, |S|, |I|*|U|);
    }
    |I|*|S|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    assert |I|*|S|*|U| <= |S|*|S|*|U| by {
      mult_preserves_order(|I|, |S|*|U|, |S|, |S|*|U|);
    }
    |S|*|S|*|U| + |S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    2*|S|*|S|*|U| + 2*|S|*|U| + |U| + |S| + 3;
    |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4;
    poly(U, S, k);
  }
}
