include "../Problems/SetCover.dfy"


// Native variant of the admissible-certificate core.
method VerifySetCoverCore_base(U:set<int>, S:set<set<int>>, k:nat, certificate:set<set<int>>) returns (accepted:bool)
  requires SetCoverValidInstance(U, S)
  requires |certificate| <= |S|
  requires forall s | s in certificate :: |s| <= |U|
  ensures accepted == SetCoverCertificate(U, S, k, certificate)
  ensures accepted ==> SetCover(U, S, k)
{
  if (k < |certificate|) { return false; }
  if (!(certificate <= S)) { return false; }
  var remainingUniverse := U;
  var covered:= true;

  while (remainingUniverse != {} && covered)
    decreases |remainingUniverse|
    invariant remainingUniverse <= U 
    invariant covered == IsCover(U-remainingUniverse,certificate)
  {
    covered, remainingUniverse := CheckUniverseElement_base(U, S, k, certificate, remainingUniverse);
  }
  assert covered ==> U-remainingUniverse == U;
  accepted := covered;
}


method CheckUniverseElement_base(U:set<int>, S:set<set<int>>, k:nat, certificate:set<set<int>>, remainingUniverse:set<int>) returns (elementCovered:bool, remainingUniverseOut:set<int>)
  requires remainingUniverse != {}
  requires remainingUniverse <= U
  requires IsCover(U - remainingUniverse, certificate)
  ensures |remainingUniverseOut| < |remainingUniverse|
  ensures remainingUniverseOut <= U
  ensures elementCovered == IsCover(U - remainingUniverseOut, certificate)
{
  var u :| u in remainingUniverse; 
  remainingUniverseOut := remainingUniverse - {u};  

  var remainingCertificate := certificate; elementCovered:= false;
  while (remainingCertificate != {} && !elementCovered)
    decreases |remainingCertificate|
    invariant remainingCertificate <= certificate
    invariant elementCovered == (exists i' | i' in certificate - remainingCertificate :: u in i')
  {
    elementCovered, remainingCertificate := CheckCoverSet_base(U, S, k, certificate, remainingCertificate, u);
  }
  assert U - remainingUniverseOut == U - remainingUniverse + {u};
}


method CheckCoverSet_base(U:set<int>, S:set<set<int>>, k:nat, certificate:set<set<int>>, remainingCertificate:set<set<int>>, u:int) returns (elementCovered:bool, remainingCertificateOut:set<set<int>>)
  requires remainingCertificate != {}
  requires remainingCertificate <= certificate
  requires !(exists i' | i' in certificate - remainingCertificate :: u in i')
  ensures |remainingCertificateOut| < |remainingCertificate|
  ensures remainingCertificateOut <= certificate
  ensures elementCovered == (exists i' | i' in certificate - remainingCertificateOut :: u in i')
{
  var i :| i in remainingCertificate;
  elementCovered := u in i;
  remainingCertificateOut := remainingCertificate - {i};
}
