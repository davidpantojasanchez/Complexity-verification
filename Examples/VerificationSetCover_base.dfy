include "../Problems/SetCover.dfy"


// Native variant of the admissible-certificate core.
method VerifySetCoverCore_base<T(==)>(instance:SetCoverModel<T>, certificate:set<set<T>>) returns (accepted:bool)
  requires SetCoverValidInstance(instance)
  requires |certificate| <= |instance.sets|
  requires forall s | s in certificate :: |s| <= |instance.universe|
  ensures accepted == SetCoverCertificate(instance, certificate)
  ensures accepted ==> SetCover(instance)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
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


method CheckUniverseElement_base<T(==)>(U:set<T>, S:set<set<T>>, k:nat, certificate:set<set<T>>, remainingUniverse:set<T>)
    returns (elementCovered:bool, remainingUniverseOut:set<T>)
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


method CheckCoverSet_base<T(==)>(U:set<T>, S:set<set<T>>, k:nat, certificate:set<set<T>>, remainingCertificate:set<set<T>>, u:T)
    returns (elementCovered:bool, remainingCertificateOut:set<set<T>>)
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
