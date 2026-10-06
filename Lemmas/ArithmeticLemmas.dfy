
lemma NatMultiplicationMonotonic(factor:nat, lower:nat, upper:nat)
  requires lower <= upper
  ensures factor*lower <= factor*upper
{}

lemma QuotientUpperBound(factor:nat, value:nat, bound:nat)
  requires 0 < factor
  requires factor*value <= bound
  ensures value <= bound/factor
{
  if bound/factor < value {
    assert bound/factor + 1 <= value;
    NatMultiplicationMonotonic(factor, bound/factor + 1, value);
    assert factor*(bound/factor + 1) == factor*(bound/factor) + factor;
    assert bound == factor*(bound/factor) + bound%factor;
    assert bound%factor < factor;
  }
}

lemma MultiplicationPreservesOrder(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{}

lemma MultiplicationAssociative(a:int, b:int, c:int)
  ensures (a*b)*c == a*(b*c)
{}

lemma SubtractionIdentity<T>(S:set<T>, E:set<T>)
  requires E == {}
  ensures S - E == S
{}

lemma SubsetCardinalityBound<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if (A == {}) {
  }
  else {
    var a :| a in A && a in B;
    SubsetCardinalityBound(A - {a}, B - {a});
  }
}

lemma FamilySubsetCardinalityBound<T>(A':set<set<T>>, B:set<T>)
  requires forall A | A in A' :: A <= B
  ensures forall A | A in A' :: |A| <= |B|
{
  if (A' == {}) {
  }
  else {
    var A :| A in A';
    SubsetCardinalityBound(A, B);
    FamilySubsetCardinalityBound(A' - {A}, B);
  }
}

