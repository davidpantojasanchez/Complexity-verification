include "../Problems/SetCover.dfy"


method verifySetCover(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (accepted:bool)   
  requires SetCoverValidInstance(U, S)
  requires SetCoverAdmissibleCertificate(U, I)
  ensures accepted == SetCoverCertificate(U, S, k, I)
  ensures accepted ==> SetCover(U, S, k)
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
  accepted := b1 && I <= S && |I| <= k ;
}


method verifySetCover_outer_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>) returns (b2:bool, U'':set<int>)
  // Termination in
  requires U' != {}
  // Invariant in
  requires U' <= U
  requires isCover(U - U', I)
  // Termination out
  ensures |U''| < |U'|
  // Invariant out
  ensures U'' <= U
  ensures b2 == isCover(U - U'', I)
{
  var u :| u in U'; 
  U'' := U' - {u};  

  var I' := I; b2:= false;
  while (I' != {} && !b2)
    decreases |I'|
    invariant I' <= I
    invariant b2 == (exists i' | i' in I - I' :: u in i')
  {
    b2, I' := verifySetCover_inner_loop(U, S, k, I, I', u);
  }
  assert U - U'' == U - U' + {u};
}


method verifySetCover_inner_loop(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, I':set<set<int>>, u:int) returns (b2:bool, I'':set<set<int>>)
  // Termination in
  requires I' != {}
  // Invariant in
  requires I' <= I
  requires !(exists i' | i' in I - I' :: u in i')
  // Termination out
  ensures |I''| < |I'|
  // Invariant out
  ensures I'' <= I
  ensures b2 == (exists i' | i' in I - I'' :: u in i')
{
  var i :| i in I';
  b2 := u in i;
  I'' := I' - {i};
}
