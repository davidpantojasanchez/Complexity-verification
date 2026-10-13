include "NativeCollectionMeasures.dfy"

// Native map inclusion: recover keys and bindings from Items inclusion.

lemma MapItemsInclusion<K, V>(actual:map<K, V>, reference:map<K, V>)
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

lemma MapUpdateAgreement<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures model[key := value].Keys <= universe[key := value].Keys
  ensures forall entry {:trigger model[key := value][entry]} |
    entry in model[key := value].Keys ::
    model[key := value][entry] == universe[key := value][entry]
{
  ghost var updatedModel, updatedUniverse :=
    MapUpdatePreservesUniverse(model, universe, key, value);
}
