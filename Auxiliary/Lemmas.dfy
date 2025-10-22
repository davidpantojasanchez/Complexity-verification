include "Set.dfy"


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


lemma in_universe_lemma_Set(S:Set, U:Set)
requires in_universe_Set(S, U)
ensures S.Size() <= U.Size()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
}
lemma in_universe_lemma_SetSet(S:SetSet, U:SetSet)
requires in_universe_SetSet(S, U)
ensures S.Size() <= U.Size()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
}
/*
lemma in_universe_lemma_SetSetSet(S:SetSetSet, U:SetSetSet)
requires in_universe_SetSetSet(S, U)
ensures S.Size() <= U.Size()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
}
*/
