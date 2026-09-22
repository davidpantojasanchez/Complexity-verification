include "../Problems/SetCover.dfy"


method VerifySetCover_base(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>) returns (accepted:bool)
  requires SetCoverValidInstance(U, S)
  requires |I| <= |S|
  requires forall s | s in I :: |s| <= |U|
  ensures accepted == SetCoverCertificate(U, S, k, I)
  ensures accepted ==> SetCover(U, S, k)
{
  if (k < |I|) { return false; }
  if (!(I <= S)) { return false; }
  var U' := U;
  var b1:= true;

  while (U' != {} && b1)
    decreases |U'|
    invariant U' <= U 
    invariant b1 == IsCover(U-U',I)
  {
    b1, U' := CheckUniverseElement_base(U, S, k, I, U');
  }
  assert b1 ==> U-U' == U;
  accepted := b1;
}


method CheckUniverseElement_base(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, U':set<int>) returns (b2:bool, U'':set<int>)
  requires U' != {}
  requires U' <= U
  requires IsCover(U - U', I)
  ensures |U''| < |U'|
  ensures U'' <= U
  ensures b2 == IsCover(U - U'', I)
{
  var u :| u in U'; 
  U'' := U' - {u};  

  var I' := I; b2:= false;
  while (I' != {} && !b2)
    decreases |I'|
    invariant I' <= I
    invariant b2 == (exists i' | i' in I - I' :: u in i')
  {
    b2, I' := CheckCoverSet_base(U, S, k, I, I', u);
  }
  assert U - U'' == U - U' + {u};
}


method CheckCoverSet_base(U:set<int>, S:set<set<int>>, k:nat, I:set<set<int>>, I':set<set<int>>, u:int) returns (b2:bool, I'':set<set<int>>)
  requires I' != {}
  requires I' <= I
  requires !(exists i' | i' in I - I' :: u in i')
  ensures |I''| < |I'|
  ensures I'' <= I
  ensures b2 == (exists i' | i' in I - I'' :: u in i')
{
  var i :| i in I';
  b2 := u in i;
  I'' := I' - {i};
}
