include "Set.dfy"


lemma set_subset_cardinality<T>(smaller:set<T>, larger:set<T>)
  requires smaller <= larger
  ensures |smaller| <= |larger|
  decreases smaller
{
  if smaller != {} {
    var element :| element in smaller;
    set_subset_cardinality(smaller - {element}, larger - {element});
  }
}

lemma nat_mult_mono(factor:nat, lower:nat, upper:nat)
  requires lower <= upper
  ensures factor*lower <= factor*upper
{}

lemma quotient_upper_bound(factor:nat, value:nat, bound:nat)
  requires 0 < factor
  requires factor*value <= bound
  ensures value <= bound/factor
{
  if bound/factor < value {
    assert bound/factor + 1 <= value;
    nat_mult_mono(factor, bound/factor + 1, value);
    assert factor*(bound/factor + 1) == factor*(bound/factor) + factor;
    assert bound == factor*(bound/factor) + bound%factor;
    assert bound%factor < factor;
  }
}


lemma mult_preserves_order(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{}

lemma associativity(a:int, b:int, c:int)
  ensures (a*b)*c == a*(b*c)
{}

lemma identity_substraction_lemma<T>(S:set<T>, E:set<T>)
requires E == {}
ensures S - E == S
{}

lemma if_smaller_then_less_cardinality<T>(A:set<T>, B:set<T>)
requires A <= B
ensures |A| <= |B|
{
  if (A == {}) {
  }
  else {
    var a :| a in A && a in B;
    if_smaller_then_less_cardinality(A - {a}, B - {a});
  }
}

lemma for_all_if_smaller_then_less_cardinality<T>(A':set<set<T>>, B:set<T>)
requires forall A | A in A' :: A <= B
ensures forall A | A in A' :: |A| <= |B|
{
  if (A' == {}) {
  }
  else {
    var A :| A in A';
    if_smaller_then_less_cardinality(A, B);
    for_all_if_smaller_then_less_cardinality(A' - {A}, B);
  }
}


lemma in_universe_lemma_Set(S:Set, U:Set)
requires in_universe_Set(S, U)
ensures S.UBSize0() <= U.UBSize0()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
}

lemma in_universe_lemma_SetSet(S:SetSet, U:SetSet)
requires in_universe_SetSet(S, U)
ensures S.UBSize0() <= U.UBSize0()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{ 
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
}

lemma in_universe_lemma_SetSetSet(S:SetSetSet, U:SetSetSet)
requires in_universe_SetSetSet(S, U)
ensures S.UBSize0() <= U.UBSize0()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
}
