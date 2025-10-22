include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (b:bool, ghost counter:nat)   
requires forall s | s in S :: s <= U 
requires forall s | s in I :: s <= U                  // ???
ensures b == (I <= S && isCover(U, I) && |I| <= k)
ensures counter <= poly(U, S, k, I)
{
  counter := 0;
  var U' := U;
  counter := counter + |U|;
  b:= true;
  var I_seq_S:bool;
  I_seq_S, counter := isSubset(U, I, S, counter);
  
  counter := counter + 1;
  if (!(I_seq_S && |I| <= k)) {
    return false, counter;
  }

  while (U' != {} && b)
    decreases |U'|
    invariant U' <= U 
    invariant b == isCover(U-U',I)
    invariant counter <= |U| + poly_isSubset(U, I, S) + 1 + (|U| - |U'|)*(poly_outer_loop(U, S, k, I) + 1)
  {
    counter := counter + 1;
    b, U', counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  counter := counter + 1;
  counter_simplification(U, S, k, I, U');
  assert b ==> U-U' == U;
}

method isSubset(U:set<int>, S1:set<set<int>>, S2:set<set<int>>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
requires forall s |s in S1 :: s <= U
requires forall s |s in S2 :: s <= U
ensures b == (S1 <= S2)
ensures counter <= counter_in + poly_isSubset(U, S1, S2)
{
  counter := counter_in;
  b := true;
  var S1':= S1;
  counter := counter + |U|*|S1|;
  while (S1' != {})
  // Termination
  decreases |S1'|
  // Regular invariants
  invariant b == ((S1 - S1') <= S2)
  invariant S1' <= S1
  // Counter
  invariant counter <= counter_in + |S1|*|U| + constant + (|S1| - |S1'|)*(poly_isSubset_loop(U, S1, S2) + 1)
  {
    S1', b, counter := isSubset_loop(U, S1, S2, S1', counter, b);
    counter := counter + 1;
  }
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
  if_smaller_then_less_cardinality(S1', S1);
  counter := counter_in;
  var s:set<int> :| s in S1';
  counter := counter + |U|;
  b' := b && s in S2;
  counter := counter + |S2|*|U|;
  S1'' := S1' - {s};
  counter := counter + |S1|*|U|;
}


method verifySetCover_outer_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>, ghost counter_in:nat) returns (b1:bool, U'':set<int>, ghost counter:nat)
// Termination in
requires U' != {}
// Invariant in
requires U' <= U
requires isCover(U - U', I)
// Termination out
ensures |U''| == |U'| - 1
// Invariant out
ensures U'' <= U
ensures b1 == isCover(U - U'', I)
// Counter
ensures counter <= counter_in + poly_outer_loop(U, S, k, I)
{
  counter := counter_in;
  var u :| u in U';
  counter := counter + 1;
  U'' := U' - {u};
  counter := counter + |U|;

  var I' := I; var b2:= false;
  counter := counter + |S|*|U|;
  while (I' != {} && !b2)
    decreases |I'|
    invariant I' <= I
    invariant b2 == (exists i' | i' in I - I' :: u in i')
    invariant counter == counter_in + |S|*|U| + |U| + 1 + (|I|-|I'|)*(poly_inner_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    b2, I', counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  counter := counter + 1;
  b1 := b2;
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
  var i :| i in I';
  counter := counter + |U|;
  b2 := u in i;
  counter := counter + |U|;
  I'' := I' - {i};
  counter := counter + |S|*|U|;
}

lemma counter_simplification(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>)
requires forall s | s in S :: s <= U
requires |I| <= k
requires U' <= U
ensures |U| + poly_isSubset(U, I, S) + 2 + (|U| - |U'|)*(poly_outer_loop(U, S, k, I) + 1) <= poly(U, S, k, I)
{
  calc <= {
    |U| + poly_isSubset(U, I, S) + 2 + (|U| - |U'|)*(poly_outer_loop(U, S, k, I) + 1);
    |U| + poly_isSubset(U, I, S) + 2 + |U|*poly_outer_loop(U, S, k, I) + |U|;
    |U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + constant + 2 + |U|*poly_outer_loop(U, S, k, I) + |U|;
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 3 + |U|*poly_outer_loop(U, S, k, I);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 3 + |U|*(|I|*|S|*|U| + 2*|I|*|U| + |S|*|U| + |I| + |U| + 2);
    |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U| + |I| + 2*|U| + 3 + |I|*|S|*|U|*|U| + 2*|I|*|U|*|U| + |S|*|U|*|U| + |I|*|U| + |U|*|U| + 2*|U|;
    |I|*|S|*|U|*|U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U|*|U| + |S|*|U|*|U| + 3*|I|*|U| + |U|*|U| + |I| + 4*|U| + 3;
  }
}

ghost function poly_isSubset_loop(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|U| + |S2|*|U| + |U|
}
ghost function poly_isSubset(U: set<int>, S1:set<set<int>>, S2:set<set<int>>) : (o:nat)
{
  |S1|*|S1|*|U| + |S1|*|S2|*|U| + 2*|S1|*|U| + |S1| + 1
}
ghost function poly_inner_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  |S|*|U| + 2*|U|
}
ghost function poly_outer_loop(U: set<int>, S: set<set<int>>, k: nat, I:set<set<int>>) : (o:nat)
ensures |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1) == o
{
  |I|*|S|*|U| + 2*|I|*|U| + |S|*|U| + |I| + |U| + 2
}

ghost function poly(U: set<int>, S: set<set<int>>, k: nat, I:set<set<int>>) : (o:nat) {
  |I|*|S|*|U|*|U| + |I|*|I|*|U| + |I|*|S|*|U| + 2*|I|*|U|*|U| + |S|*|U|*|U| + 3*|I|*|U| + |U|*|U| + |I| + 4*|U| + 3
}
