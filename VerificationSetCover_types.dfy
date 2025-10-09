include "SetCover.dfy"


method verifySetCover<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool)   
requires forall s | s in S :: s <= U
ensures b == (I <= S && isCover(U, I) && |I| <= k)
{
  var U' := U;
  var b1:= true;

  while (U' != {} && b1)
    decreases |U'|
    invariant U' <= U 
    invariant b1 == isCover(U-U',I)
  {
    b1, U' := verifySetCover_outer_loop(U, S, k, I, U');
  }
  assert b1 ==> U-U' == U;
  b := b1 && I <= S && |I| <= k ;
}


method verifySetCover_outer_loop<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>, U':set<T>) returns (b1:bool, U'':set<T>)
// Termination
requires U' != {}
// Invariant in
requires U' <= U
requires isCover(U - U', I)
// Decreases
ensures |U''| < |U'|
// Invariant out
ensures U'' <= U
ensures b1 == isCover(U - U'', I)
{
  var u :| u in U'; 
  U'' := U' - {u};  

  var I' := I; var b2:= false;
  while (I' != {} && !b2)
    decreases |I'|
    invariant I' <= I
    invariant b2 == (exists i' | i' in I - I' :: u in i')
  {
    b2, I' := verifySetCover_inner_loop(U, S, k, I, I', u);
  }
  b1 := b2;
  assert U - U'' == U - U' + {u};
}


method verifySetCover_inner_loop<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>, I':set<set<T>>, u:T) returns (b2:bool, I'':set<set<T>>)
// Termination
requires I' != {}
// Invariant in
requires I' <= I
requires !(exists i' | i' in I - I' :: u in i')
// Decreases
ensures |I''| < |I'|
// Invariant out
ensures I'' <= I
ensures b2 == (exists i' | i' in I - I'' :: u in i')
{
  var i :| i in I';
  b2 := u in i;
  I'' := I' - {i};
}

