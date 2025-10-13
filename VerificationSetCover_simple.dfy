include "SetCover.dfy"
include "Lemmas.dfy"


method verifySetCover<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool, ghost counter:nat)   
requires forall s | s in S :: s <= U
ensures b == (I <= S && isCover(U, I) && |I| <= k)
ensures counter <= |U| + 2 + |U| + |S|*|U|*|U| + |U|*|U| + 2*|U| + |I|*|U|*|S|*|U| + |I|*|U|*2*|U| + |I|*|U|*1
{
  counter := 0;
  var U' := U;
  counter := counter + |U|;
  var b1:= true;
  
  counter := counter + 1;
  if (k < |I|) {              // ?
    return false, counter;
  }

  while (U' != {} && b1)
    decreases |U'|
    invariant U' <= U 
    invariant b1 == isCover(U-U',I)
    invariant counter <= |U| + 1 + (|U| - |U'|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1))
  {
    counter := counter + 1;
    b1, U', counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  counter := counter + 1;
  assert counter <= |U| + 2 + |U| + |S|*|U|*|U| + |U|*|U| + 2*|U| + |I|*|U|*(|S|*|U| + 2*|U| + 1) by {
    assert counter <= |U| + 2 + (|U| - |U'|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1));
    assert counter <= |U| + 2 + (|U|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1));
  }

  assert b1 ==> U-U' == U;
  b := b1 && I <= S && |I| <= k;
}


method verifySetCover_outer_loop<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>, U':set<T>, ghost counter_in:nat) returns (b1:bool, U'':set<T>, ghost counter:nat)
// Termination
requires U' != {}
// Invariant in
requires U' <= U
requires isCover(U - U', I)
// Decreases
ensures |U''| == |U'| - 1
// Invariant out
ensures U'' <= U
ensures b1 == isCover(U - U'', I)
// Counter
ensures counter <= counter_in + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1)
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
    invariant counter == counter_in + |S|*|U| + |U| + 1 + (|I|-|I'|)*(|S|*|U| + 2*|U| + 1)
  {
    counter := counter + 1;
    b2, I', counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  counter := counter + 1;
  b1 := b2;
  assert U - U'' == U - U' + {u};
}


method verifySetCover_inner_loop<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>, I':set<set<T>>, u:T, ghost counter_in:nat) returns (b2:bool, I'':set<set<T>>, ghost counter:nat)
// Termination
requires I' != {}
// Invariant in
requires I' <= I
requires !(exists i' | i' in I - I' :: u in i')
// Decreases
ensures |I''| == |I'| - 1
// Invariant out
ensures I'' <= I
ensures b2 == (exists i' | i' in I - I'' :: u in i')
// Counter
ensures counter == counter_in + |S|*|U| + 2*|U|
{
  counter := counter_in;
  var i :| i in I';
  counter := counter + |U|;
  b2 := u in i;
  counter := counter + |U|;
  I'' := I' - {i};
  counter := counter + |S|*|U|;
}

