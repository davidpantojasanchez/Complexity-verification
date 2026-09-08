include "../Problems/CDPC.dfy"
include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "Set.dfy"
include "Map.dfy"

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
ensures S.Size0() <= U.Size0()
ensures S.UBSize0() <= U.UBSize0()
ensures S.UBCardinality() <= U.UBCardinality()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
}

lemma in_universe_lemma_SetSet(S:SetSet, U:SetSet)
requires in_universe_SetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.UBSize0() <= U.UBSize0()
ensures S.UBCardinality() <= U.UBCardinality()
ensures S.UBCardinality() * S.UBSize1() <= U.UBCardinality() * U.UBSize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{ 
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
  mult_preserves_order(S.UBCardinality(),S.UBSize1(),U.UBCardinality(), U.UBSize1());
}

lemma in_universe_lemma_SetSetSet(S:SetSetSet, U:SetSetSet)
requires in_universe_SetSetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.UBSize0() <= U.UBSize0()
ensures S.UBCardinality() <= U.UBCardinality()
ensures S.UBCardinality() * S.UBSize1() <= U.UBCardinality() * U.UBSize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
  mult_preserves_order(S.UBCardinality(),S.UBSize1(),U.UBCardinality(), U.UBSize1());
}

lemma in_universe_lemma_Map(M:Map, U:Map)
  requires in_universe_Map(M, U)
  ensures M.Size() <= U.Size()
  ensures M.UBSize() <= U.UBSize()
  ensures M.UBCardinality() <= U.UBCardinality()
  ensures M.Cardinality() <= U.Cardinality()
{
  reveal M.Valid();
  reveal U.Valid();
  if_smaller_then_less_cardinality(M.Model().Keys, M.Universe().Keys);
  if_smaller_then_less_cardinality(M.Universe().Keys, U.Model().Keys);
  if_smaller_then_less_cardinality(U.Model().Keys, U.Universe().Keys);
}

lemma in_universe_lemma_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
  requires in_universe_Map_Map_T(M, U)
  ensures M.Size() <= U.Size()
  ensures M.UBSize() <= U.UBSize()
  ensures M.UBSize_Keys() <= U.UBSize_Keys()
  ensures M.UBCardinality() <= U.UBCardinality()
  ensures M.Cardinality() <= U.Cardinality()
{
  reveal M.Valid();
  reveal U.Valid();
  if_smaller_then_less_cardinality(M.Model().Keys, M.Universe().Keys);
  if_smaller_then_less_cardinality(M.Universe().Keys, U.Model().Keys);
  if_smaller_then_less_cardinality(U.Model().Keys, U.Universe().Keys);
  mult_preserves_order(
    M.Cardinality(), M.UBSize_Keys(),
    U.Cardinality(), U.UBSize_Keys());
  mult_preserves_order(
    M.UBCardinality(), M.UBSize_Keys(),
    U.UBCardinality(), U.UBSize_Keys());
}

lemma in_universe_transitive_Map_Map_T(
    M:Map_Map_T, middle:Map_Map_T, U:Map_Map_T)
  requires in_universe_Map_Map_T(M, middle)
  requires in_universe_Map_Map_T(middle, U)
  ensures in_universe_Map_Map_T(M, U)
{
  reveal middle.Valid();
  assert M.Universe().Keys <= U.Model().Keys;
  forall key | key in M.Universe().Keys
    ensures M.Universe()[key] == U.Model()[key]
  {
    assert key in middle.Model().Keys;
    assert key in middle.Universe().Keys;
  }
}

lemma SetCoverCertificateIsAdmissible<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(universe, sets)
  requires SetCoverCertificate(universe, sets, cardinality, cover)
  ensures SetCoverAdmissibleCertificate(universe, cover)
{
  forall s | s in cover
    ensures |s| <= |universe|
  {
    set_subset_cardinality(s, universe);
  }
}

lemma SetCoverAdmissibleWitnesses<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires SetCoverValidInstance(universe, sets)
  ensures SetCover(universe, sets, cardinality) <==>
    (exists cover:set<set<T>> | cover <= sets ::
      SetCoverAdmissibleCertificate(universe, cover) &&
      SetCoverCertificate(universe, sets, cardinality, cover))
{
  if SetCover(universe, sets, cardinality) {
    var cover :| cover <= sets && SetCoverCertificate(universe, sets, cardinality, cover);
    SetCoverCertificateIsAdmissible(universe, sets, cardinality, cover);
  }
}


lemma HittingSetCertificateIsAdmissible<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
  requires HittingSetCertificate(universe, sets, cardinality, hittingSet)
  ensures HittingSetAdmissibleCertificate(universe, hittingSet)
{
  set_subset_cardinality(hittingSet, universe);
}

lemma HittingSetAdmissibleWitnesses<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires HittingSetValidInstance(universe, sets)
  ensures HittingSet(universe, sets, cardinality) <==>
    (exists hittingSet:set<T> | hittingSet <= universe ::
      HittingSetAdmissibleCertificate(universe, hittingSet) &&
      HittingSetCertificate(universe, sets, cardinality, hittingSet))
{
  if HittingSet(universe, sets, cardinality) {
    var hittingSet :| hittingSet <= universe && HittingSetCertificate(universe, sets, cardinality, hittingSet);
    HittingSetCertificateIsAdmissible(universe, sets, cardinality, hittingSet);
  }
}


lemma CDPCCorrectCertificateIsAdmissible<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, interview:InterviewModel<Q>)
  requires CDPCValidInstance(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires CDPCCorrectCertificate(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, interview)
  ensures CDPCAdmissibleCertificate(CDPCQuestions(fitness.Keys), interview)
{
  InterviewQuestionsBound(interview, CDPCQuestions(fitness.Keys));
}

lemma CDPCAdmissibleWitnesses<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real)
  requires CDPCValidInstance(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures CDPC(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper) <==>
    (exists interview:InterviewModel<Q> ::
      CDPCAdmissibleCertificate(CDPCQuestions(fitness.Keys), interview) &&
      CDPCCorrectCertificate(fitness, multiplicity, privateQuestions,
        privateLower, privateUpper, fitnessLower, fitnessUpper, interview))
{
  if CDPC(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper) {
    var interview :| InterviewFits(interview, CDPCQuestions(fitness.Keys)) &&
      CDPCCertificate(fitness, multiplicity, privateQuestions,
        privateLower, privateUpper, fitnessLower, fitnessUpper, fitness.Keys, interview);
    CDPCCorrectCertificateIsAdmissible(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, interview);
  }
}
