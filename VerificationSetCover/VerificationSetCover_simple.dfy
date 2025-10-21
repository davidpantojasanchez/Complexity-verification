include "../Problems/SetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (b:bool, ghost counter:nat)   
requires forall s | s in S :: s <= U
ensures b == (I <= S && isCover(U, I) && |I| <= k)
ensures counter <= poly(U, S, k)
{
  counter := 0;
  var U' := U;
  counter := counter + |U|;
  b:= true;
  
  counter := counter + 1;
  if (!(I <= S && |I| <= k)) {
    return false, counter;
  }

  while (U' != {} && b)
    decreases |U'|
    invariant U' <= U 
    invariant b == isCover(U-U',I)
    invariant counter <= |U| + 1 + (|U| - |U'|)*(poly_outer_loop(U, S, k, I) + 1)
  {
    counter := counter + 1;
    b, U', counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  counter := counter + 1;
  counter_simplification(U, S, k, I, U');
  assert b ==> U-U' == U;
  b := b;
}

method verifySetCover_outer_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>, ghost counter_in:nat) returns (b1:bool, U'':set<int>, ghost counter:nat)
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
ensures |U| + 2 + (|U| - |U'|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1)) <=
        (k + 1)*|S|*|U|*|U| + (2*k + 1)*|U|*|U| + (4 + k)*|U| + 2
{
  assert (1 + k)*|S|*|U|*|U| == (k + 1)*|S|*|U|*|U|;
  assert |I|*|U|*(|S|*|U| + 2*|U| + 1) <= k*|U|*(|S|*|U| + 2*|U| + 1) by {
    assert |I|*|U| <= k*|U|;
  }
  calc <= {
    |U| + 2 + (|U| - |U'|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1));
    |U| + 2 + (|U|)*(1 + |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1));
    |U| + 2 + |U| + |S|*|U|*|U| + |U|*|U| + 2*|U| + |I|*|U|*(|S|*|U| + 2*|U| + 1);
    4*|U| + |S|*|U|*|U| + |U|*|U| + |I|*|U|*(|S|*|U| + 2*|U| + 1) + 2;
    4*|U| + |S|*|U|*|U| + |U|*|U| + k*|U|*(|S|*|U| + 2*|U| + 1) + 2;
    4*|U| + |S|*|U|*|U| + |U|*|U| + (k*|U|*|S|*|U| + k*|U|*2*|U| + k*|U|*1) + 2;
    4*|U| + |S|*|U|*|U| + |U|*|U| + k*|S|*|U|*|U| + 2*k*|U|*|U| + k*|U| + 2;
    (k + 1)*|S|*|U|*|U| + (2*k + 1)*|U|*|U| + (4 + k)*|U| + 2;
  }
}

ghost function poly_inner_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  |S|*|U| + 2*|U|
}

ghost function poly_outer_loop(U: set<int>, S: set<set<int>>, k: nat, I:set<set<int>>) : (o:nat)
{
  |S|*|U| + |U| + 2 + |I|*(|S|*|U| + 2*|U| + 1)
}

ghost function poly(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  (k + 1)*|S|*|U|*|U| + (2*k + 1)*|U|*|U| + (4 + k)*|U| + 2
}
