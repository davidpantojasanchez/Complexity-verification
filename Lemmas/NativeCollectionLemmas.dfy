include "NativeCollectionMeasures.dfy"

// Native map inclusion: recover keys and bindings from Items inclusion.

lemma map_items_inclusion<K, V>(actual:map<K, V>, reference:map<K, V>)
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
lemma map_update_preserves_universe<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
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

lemma map_update_agreement<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures model[key := value].Keys <= universe[key := value].Keys
  ensures forall entry {:trigger model[key := value][entry]} |
    entry in model[key := value].Keys ::
    model[key := value][entry] == universe[key := value][entry]
{
  ghost var updatedModel, updatedUniverse :=
    map_update_preserves_universe(model, universe, key, value);
}

// Native set difference and cardinality bounds, including families of subsets.

lemma set_difference_empty<T>(S:set<T>, E:set<T>)
  requires E == {}
  ensures S - E == S
{}

lemma subset_cardinality_bound<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if (A == {}) {
  }
  else {
    var a :| a in A && a in B;
    subset_cardinality_bound(A - {a}, B - {a});
  }
}

lemma family_subset_cardinality_bound<T>(A':set<set<T>>, B:set<T>)
  requires forall A | A in A' :: A <= B
  ensures forall A | A in A' :: |A| <= |B|
{
  if (A' == {}) {
  }
  else {
    var A :| A in A';
    subset_cardinality_bound(A, B);
    family_subset_cardinality_bound(A' - {A}, B);
  }
}
