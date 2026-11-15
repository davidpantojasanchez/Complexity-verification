include "CollectionMeasures.dfy"

// An injective relabeling preserves the number of distinct objects.
ghost function Image_set<T(!new), R(!new)>(items:set<T>, encode:T -> R):set<R>
{ set item | item in items :: encode(item) }

lemma injective_image_cardinality_set<T(!new), R(!new)>(items:set<T>, encode:T -> R)
  requires forall first, second | first in items && second in items :: encode(first) == encode(second) ==> first == second
  ensures |Image_set(items,encode)| == |items|
  decreases |items|
{
  if items != {} {
    var item :| item in items;
    var remaining := items-{item};
    injective_image_cardinality_set(remaining,encode);
    assert Image_set(remaining,encode) == (set other | other in remaining :: encode(other));
    var image := set other | other in remaining :: encode(other);
    assert encode(item) !in image;
    assert (set other | other in items :: encode(other)) == image+{encode(item)};
  } else {
    assert (set item | item in items :: encode(item)) == {};
  }
}

// Native set difference and cardinality bounds, including sets of subsets.

lemma difference_empty_set<T>(S:set<T>, E:set<T>)
  requires E == {}
  ensures S - E == S
{}

lemma subset_cardinality_bound_set<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if (A == {}) {
  }
  else {
    var a :| a in A && a in B;
    subset_cardinality_bound_set(A - {a}, B - {a});
  }
}

lemma subset_cardinality_bound_setset<T>(A':set<set<T>>, B:set<T>)
  requires forall A | A in A' :: A <= B
  ensures forall A | A in A' :: |A| <= |B|
{
  if (A' == {}) {
  }
  else {
    var A :| A in A';
    subset_cardinality_bound_set(A, B);
    subset_cardinality_bound_setset(A' - {A}, B);
  }
}

// Cancel a common multiplicity component independently of enumeration order.
lemma cancellation_multiset<T>(common:multiset<T>, first:multiset<T>, second:multiset<T>)
  requires common + first == common + second
  ensures first == second
{
  forall element
    ensures first[element] == second[element]
  {
    assert (common + first)[element] == common[element] + first[element];
    assert (common + second)[element] == common[element] + second[element];
  }
}

// Native map inclusion: recover keys and bindings from Items inclusion.

lemma items_inclusion_map<K, V>(actual:map<K, V>, reference:map<K, V>)
  requires actual.Items <= reference.Items
  ensures actual.Keys <= reference.Keys
  ensures forall key | key in actual.Keys :: actual[key] == reference[key]
{
  forall key | key in actual.Keys
    ensures key in reference.Keys && actual[key] == reference[key]
  {
    assert (key, actual[key]) in actual.Items;
    assert (key, actual[key]) in reference.Items;
  }
}

// Native updates: preserve inclusion and value agreement after a common update.
lemma update_preserves_universe_map<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
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

lemma update_agreement_map<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures model[key := value].Keys <= universe[key := value].Keys
  ensures forall entry {:trigger model[key := value][entry]} |
    entry in model[key := value].Keys ::
    model[key := value][entry] == universe[key := value][entry]
{
  ghost var updatedModel, updatedUniverse :=
    update_preserves_universe_map(model, universe, key, value);
}
