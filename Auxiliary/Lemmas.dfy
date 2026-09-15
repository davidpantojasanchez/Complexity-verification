include "../Problems/CDPC.dfy"
include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "Set.dfy"
include "Map.dfy"

lemma nat_mult_mono(factor:nat, lower:nat, upper:nat)
  requires lower <= upper
  ensures factor*lower <= factor*upper
{}

lemma SetModelSizeBound<T>(S:Set<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{}

lemma SetSetModelSizeBound<T>(S:SetSet<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{
  nat_mult_mono(S.UBSize1(), S.Cardinality(), S.UBCardinality());
}

lemma SetSetSetModelSizeBound<T>(S:SetSetSet<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{
  nat_mult_mono(S.UBSize1(), S.Cardinality(), S.UBCardinality());
}


lemma MapModelSizeBound<K, V>(M:Map<K, V>)
  requires M.Valid()
  ensures M.Size() <= M.UBSize()
{}

lemma MaxMapCardinalityProperties<K, V>(maps:set<map<K, V>>)
  ensures forall m | m in maps :: |m| <= MaxMapCardinality(maps)
  ensures maps != {} ==> exists m | m in maps :: MaxMapCardinality(maps) == |m|
  decreases |maps|
{
  forall m | m in maps
    ensures forall k | k in maps - {m} :: |k| <= MaxMapCardinality(maps - {m})
    ensures maps - {m} != {} ==>
      exists k | k in maps - {m} :: MaxMapCardinality(maps - {m}) == |k|
  {
    MaxMapCardinalityProperties(maps - {m});
  }
  reveal MaxMapCardinality();
}

lemma MaxMapCardinalityMember<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  requires key in maps
  ensures |key| <= MaxMapCardinality(maps)
{
  MaxMapCardinalityProperties(maps);
}

lemma MaxMapCardinalityInsert<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  ensures MaxMapCardinality(maps + {key}) ==
    (if |key| <= MaxMapCardinality(maps) then MaxMapCardinality(maps) else |key|)
{
  MaxMapCardinalityProperties(maps);
  MaxMapCardinalityProperties(maps + {key});
}

lemma MaxMapCardinalityBound<K, V>(maps:set<map<K, V>>, bound:nat)
  requires forall m | m in maps :: |m| <= bound
  ensures MaxMapCardinality(maps) <= bound
{ MaxMapCardinalityProperties(maps); }

lemma MaxMapCardinalityMonotonic<K, V>(smaller:set<map<K, V>>, larger:set<map<K, V>>)
  requires smaller <= larger
  ensures MaxMapCardinality(smaller) <= MaxMapCardinality(larger)
{
  MaxMapCardinalityProperties(smaller);
  MaxMapCardinalityProperties(larger);
}

lemma MapMapTUniverseKeySizeBound<K, V, R>(M:Map_Map_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.UBSize_Keys() <= bound
{
  reveal M.UBSize_Keys();
  MaxMapCardinalityBound(M.Universe().Keys, bound);
}

lemma MapMapTModelSizeBound<K, V, R>(M:Map_Map_T<K, V, R>)
  requires M.Valid()
  ensures M.Size_Keys() <= M.UBSize_Keys()
  ensures M.Size() <= M.UBSize()
{
  reveal M.UBSize_Keys();
  MaxMapCardinalityMonotonic(M.Model().Keys, M.Universe().Keys);
  mult_preserves_order(M.Cardinality(), M.Size_Keys(), M.UBCardinality(), M.UBSize_Keys());
}

// Bound a family's universe size from independent family and member bounds.
lemma SetSetUniverseSizeBound<T>(S:SetSet<T>, count:nat, member:nat)
  requires S.Valid()
  requires S.UBCardinality() <= count && S.UBSize1() <= member
  ensures S.UBSize0() <= count*member
{
  mult_preserves_order(S.UBCardinality(), S.UBSize1(), count, member);
}

// Bound a set-keyed map's universe size without exposing its representation to callers.
lemma MapSetTUniverseSizeBound<K, V>(M:Map_Set_T<K, V>, count:nat, key:nat)
  requires M.Valid()
  requires M.UBCardinality() <= count && M.UBSize_Keys() <= key
  ensures M.Cardinality() <= M.UBCardinality()
  ensures M.UBSize() <= count*key
{
  reveal M.Valid();
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), count, key);
}

// Bound a population's universe size, charging both levels of its nested keys.
lemma MapMapSetTUniverseSizeBound<K, V, R>(M:Map_MapSet_T<K, V, R>, count:nat, keys:nat, elements:nat)
  requires M.Valid()
  requires M.UBCardinality() <= count && M.UBSize_Keys() <= keys
  requires M.UBSize_Keys_Keys() <= elements
  ensures M.UBSize() <= count*keys*elements
{
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), count, keys);
  mult_preserves_order(M.UBCardinality()*M.UBSize_Keys(), M.UBSize_Keys_Keys(), count*keys, elements);
}

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
ensures S.UBCardinality() <= U.Cardinality()
ensures S.UBSize0() <= U.Size0()
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  if_smaller_then_less_cardinality(S.Universe(), U.Model());
}

lemma in_universe_lemma_SetSet(S:SetSet, U:SetSet)
requires in_universe_SetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.UBSize0() <= U.UBSize0()
ensures S.UBCardinality() <= U.UBCardinality()
ensures S.UBCardinality() * S.UBSize1() <= U.UBCardinality() * U.UBSize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UBCardinality() <= U.Cardinality()
ensures S.UBSize0() <= U.Size0()
{ 
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
  mult_preserves_order(S.UBCardinality(),S.UBSize1(),U.UBCardinality(), U.UBSize1());
  if_smaller_then_less_cardinality(S.Universe(), U.Model());
  mult_preserves_order(S.UBCardinality(), S.UBSize1(), U.Cardinality(), U.UBSize1());
}

lemma in_universe_lemma_SetSetSet(S:SetSetSet, U:SetSetSet)
requires in_universe_SetSetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.UBSize0() <= U.UBSize0()
ensures S.UBCardinality() <= U.UBCardinality()
ensures S.UBCardinality() * S.UBSize1() <= U.UBCardinality() * U.UBSize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UBCardinality() <= U.Cardinality()
ensures S.UBSize0() <= U.Size0()
{
  if_smaller_then_less_cardinality(S.Model(), U.Model());
  if_smaller_then_less_cardinality(S.Universe(), U.Universe());
  mult_preserves_order(S.Cardinality(),S.UBSize1(),U.Cardinality(), U.UBSize1());
  mult_preserves_order(S.UBCardinality(),S.UBSize1(),U.UBCardinality(), U.UBSize1());
  if_smaller_then_less_cardinality(S.Universe(), U.Model());
  mult_preserves_order(S.UBCardinality(), S.UBSize1(), U.Cardinality(), U.UBSize1());
}

lemma in_universe_lemma_Map(M:Map, U:Map)
  requires in_universe_Map(M, U)
  ensures M.Size() <= U.Size()
  ensures M.UBSize() <= U.UBSize()
  ensures M.UBCardinality() <= U.UBCardinality()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UBCardinality() <= U.Cardinality()
  ensures M.UBSize() <= U.Size()
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
  ensures M.UBCardinality() <= U.Cardinality()
  ensures M.UBSize() <= U.Size()
{
  reveal M.Valid();
  reveal U.Valid();
  if_smaller_then_less_cardinality(M.Model().Keys, M.Universe().Keys);
  if_smaller_then_less_cardinality(M.Universe().Keys, U.Model().Keys);
  if_smaller_then_less_cardinality(U.Model().Keys, U.Universe().Keys);
  reveal M.UBSize_Keys(), U.UBSize_Keys();
  MaxMapCardinalityMonotonic(M.Model().Keys, U.Model().Keys);
  MaxMapCardinalityMonotonic(M.Universe().Keys, U.Model().Keys);
  MaxMapCardinalityMonotonic(U.Model().Keys, U.Universe().Keys);
  mult_preserves_order(M.Cardinality(), M.Size_Keys(), U.Cardinality(), U.Size_Keys());
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), U.UBCardinality(), U.UBSize_Keys());
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), U.Cardinality(), U.Size_Keys());
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

lemma SetCoverCertificateSizeBound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(universe, sets)
  requires SetCoverCertificate(universe, sets, cardinality, cover)
  ensures |cover| <= |sets|
  ensures forall s | s in cover :: |s| <= |universe|
{
  if_smaller_then_less_cardinality(cover, sets);
  forall s | s in cover ensures |s| <= |universe| {
    if_smaller_then_less_cardinality(s, universe);
  }
}

lemma HittingSetCertificateSizeBound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
  requires HittingSetCertificate(universe, sets, cardinality, hittingSet)
  ensures |hittingSet| <= |universe|
{
  if_smaller_then_less_cardinality(hittingSet, universe);
}

// Each remaining question can be asked at most once for each candidate.
// Empty branches terminate immediately, including their End node in the bound.
lemma {:isolate_assertions} CDPCSubtreeSizeBound<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, candidates:set<Candidate<Q>>,
    remaining:set<Q>, tree:InterviewModel<Q>)
  decreases tree
  requires candidates <= fitness.Keys && candidates <= multiplicity.Keys
  requires forall c | c in candidates :: remaining <= c.Keys
  requires InterviewFits(tree, remaining)
  requires if candidates == {} then tree.End? else
    CDPCInterviewSemantics(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, candidates, tree)
  ensures InterviewNodes(tree) <= 2*|candidates|*|remaining| + 1
{
  reveal InterviewNodes(), InterviewFits(), CDPCInterviewSemantics(), CDPCBranch();
  if tree.Ask? {
    var q := tree.question;
    var left := FilterCandidates(candidates, q, true);
    var right := FilterCandidates(candidates, q, false);
    assert left + right == candidates;
    assert left * right == {};
    assert |left| + |right| == |candidates|;
    CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      left, remaining - {q}, tree.trueBranch);
    CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      right, remaining - {q}, tree.falseBranch);
    assert |remaining - {q}| == |remaining| - 1;
    CDPCNodeBudget(|left|, |right|, |candidates|, |remaining|,
      InterviewNodes(tree.trueBranch), InterviewNodes(tree.falseBranch));
  }
}

lemma CDPCNodeBudget(left:nat, right:nat, population:nat, questions:nat, a:nat, b:nat)
  requires a <= 2*left*(questions-1)+1
  requires b <= 2*right*(questions-1)+1
  requires left + right == population && population > 0 && questions > 0
  ensures 1+a+b <= 2*population*questions+1
{
  assert 2*left*(questions-1)+2*right*(questions-1) == 2*population*(questions-1);
  assert 2*population*(questions-1) == 2*population*questions-2*population;
}

lemma CDPCCertificateSizeBound<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, tree:InterviewModel<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires CDPCCertificate(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree)
  ensures InterviewNodes(tree) <= 2*|fitness.Keys|*|questions|+1
{
  CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    fitness.Keys, questions, tree);
}


// Bound the model's nested size by its universe's nested size.
lemma MapSetTModelSizeBound<K, V>(M:Map_Set_T<K, V>)
  requires M.Valid()
  ensures M.Size() <= M.UBSize()
{
  reveal M.Valid();
  nat_mult_mono(M.UBSize_Keys(), M.Cardinality(), M.UBCardinality());
}

// Bound the model's nested size by its universe's nested size.
lemma MapMapSetTModelSizeBound<K, V, R>(M:Map_MapSet_T<K, V, R>)
  requires M.Valid()
  ensures M.Size() <= M.UBSize()
{
  reveal M.Valid();
  nat_mult_mono(M.UBSize_Keys(), M.Cardinality(), M.UBCardinality());
  nat_mult_mono(M.UBSize_Keys_Keys(), M.Cardinality()*M.UBSize_Keys(), M.UBCardinality()*M.UBSize_Keys());
}

// Shared affine loop budget: setup plus processed iterations times their symbolic cost.
ghost function {:opaque} LinearLoopBudget(
    base:nat, step:nat, processed:nat):nat
{
  base + processed * step
}

// Initialize an affine budget before the first iteration.
lemma LinearLoopBudgetZero(base:nat, step:nat)
  ensures LinearLoopBudget(base, step, 0) == base
{
  reveal LinearLoopBudget();
}

// Bound an accumulated budget by a maximum iteration count.
lemma LinearLoopBudgetBound(
    base:nat, step:nat, processed:nat, bound:nat)
  requires processed <= bound
  ensures LinearLoopBudget(base, step, processed) <=
          base + bound * step
{
  reveal LinearLoopBudget();
  mult_preserves_order(processed, step, bound, step);
}

// Expose exactly one iteration of an otherwise opaque budget.
lemma LinearLoopBudgetStep(base:nat, step:nat, processed:nat)
  ensures LinearLoopBudget(base, step, processed + 1) ==
    LinearLoopBudget(base, step, processed) + step
{ reveal LinearLoopBudget(); }

// Transfer an upper budget, including tail costs, to the observed counter.
lemma LinearLoopBudgetTransfer(spent:nat, budget:nat, upper:nat, tail:nat, total:nat)
  requires spent <= budget <= upper
  requires upper + tail <= total
  ensures budget + tail <= total
  ensures spent + tail <= total
{}

// Updating the same binding preserves a map's agreement with its enclosing universe.
lemma MapUpdatePreservesUniverse<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
    returns (updatedModel:map<K, V>, updatedUniverse:map<K, V>)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures updatedModel.Keys <= updatedUniverse.Keys
  ensures updatedModel == model[key := value] && updatedUniverse == universe[key := value]
  ensures forall entry | entry in updatedModel.Keys :: updatedModel[entry] == updatedUniverse[entry]
{
  updatedModel := model[key := value];
  updatedUniverse := universe[key := value];
}


// Transfer cardinality, nested-size and operation-cost bounds through a reference universe.
lemma in_universe_lemma_Map_Set_T(M:Map_Set_T, U:Map_Set_T)
  requires in_universe_Map_Set_T(M, U)
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UBCardinality() <= U.Cardinality()
  ensures M.UBCardinality() <= U.UBCardinality()
  ensures M.UBSize_Keys() <= U.UBSize_Keys()
  ensures M.Size() <= U.Size()
  ensures M.UBSize() <= U.Size()
  ensures M.UBSize() <= U.UBSize()
  ensures cost_MapSetTGetUniverse(M) <= cost_MapSetTGet(U)
  ensures cost_MapSetTContainsKeyUniverse(M) <= cost_MapSetTContainsKey(U)
  ensures cost_MapSetTInsertUniverse(M) <= cost_MapSetTInsert(U)
{
  reveal M.Valid(), U.Valid();
  MapSetTModelSizeBound(M);
  MapSetTModelSizeBound(U);
  if_smaller_then_less_cardinality(M.Universe().Keys, U.Model().Keys);
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), U.Cardinality(), U.UBSize_Keys());
}

// Compose two reference-universe relations without losing binding agreement or child bounds.
lemma in_universe_transitive_Map_Set_T(M:Map_Set_T, middle:Map_Set_T, U:Map_Set_T)
  requires in_universe_Map_Set_T(M, middle)
  requires in_universe_Map_Set_T(middle, U)
  ensures in_universe_Map_Set_T(M, U)
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

// Transfer cardinality, nested-size and operation-cost bounds through a reference universe.
lemma in_universe_lemma_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires in_universe_Map_MapSet_T(M, U)
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UBCardinality() <= U.Cardinality()
  ensures M.UBCardinality() <= U.UBCardinality()
  ensures M.UBSize_Keys() <= U.UBSize_Keys()
  ensures M.UBSize_Keys_Keys() <= U.UBSize_Keys_Keys()
  ensures M.Size() <= U.Size()
  ensures M.UBSize() <= U.Size()
  ensures M.UBSize() <= U.UBSize()
  ensures cost_MapMapSetTGetUniverse(M) <= cost_MapMapSetTGet(U)
  ensures cost_MapMapSetTContainsKeyUniverse(M) <= cost_MapMapSetTContainsKey(U)
  ensures cost_MapMapSetTInsertUniverse(M) <= cost_MapMapSetTInsert(U)
{
  MapMapSetTModelSizeBound(M);
  MapMapSetTModelSizeBound(U);
  assert M.Cardinality() <= M.UBCardinality() && U.Cardinality() <= U.UBCardinality() by {
    reveal M.Valid(), U.Valid();
  }
  assert M.UBCardinality() <= U.Cardinality() by {
    if_smaller_then_less_cardinality(M.Universe().Keys, U.Model().Keys);
  }
  mult_preserves_order(M.UBCardinality(), M.UBSize_Keys(), U.Cardinality(), U.UBSize_Keys());
  mult_preserves_order(M.UBCardinality()*M.UBSize_Keys(), M.UBSize_Keys_Keys(),
    U.Cardinality()*U.UBSize_Keys(), U.UBSize_Keys_Keys());
}

// Compose two reference-universe relations without losing binding agreement or child bounds.
lemma in_universe_transitive_Map_MapSet_T(M:Map_MapSet_T, middle:Map_MapSet_T, U:Map_MapSet_T)
  requires in_universe_Map_MapSet_T(M, middle)
  requires in_universe_Map_MapSet_T(middle, U)
  ensures in_universe_Map_MapSet_T(M, U)
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
