include "../Collections/Set.dfy"
include "../Collections/Map.dfy"

// These lemmas are internal implementation helpers; the lemmas intended to be used in verification are directly in the traits

lemma add_universe_measures_set_set<T>(before:SetSet<T>, result:SetSet<T>, element:Set<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.UCardinality1() ==
    (if element.Size() <= before.UCardinality1() then before.UCardinality1() else element.Size())
{
  reveal before.UCardinality1(), result.UCardinality1();
  max_by_insert(before.Universe(), element.Model(), item => |item|);
}

lemma add_universe_measures_set_set_set<T>(before:SetSetSet<T>, result:SetSetSet<T>, element:SetSet<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.UCardinality1() ==
    (if element.Cardinality() <= before.UCardinality1() then before.UCardinality1() else element.Cardinality())
  ensures result.UCardinality2() ==
    (if element.Cardinality1() <= before.UCardinality2() then before.UCardinality2() else element.Cardinality1())
{
  reveal before.UCardinality1(), result.UCardinality1();
  reveal before.UCardinality2(), result.UCardinality2();
  max_by_insert(before.Universe(), element.Model(), item => |item|);
  max_by_insert(before.Universe(), element.Model(), item => MaxCardinality_set(item));
}

lemma insert_universe_measures_map_map_t<K, V, R>(
    before:Map_Map_T<K, V, R>, result:Map_Map_T<K, V, R>, key:Map<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Size() <= before.UCardinalityKeys() then before.UCardinalityKeys() else key.Size())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  max_by_insert(before.Universe().Keys, key.Model(), item => |item|);
}

lemma insert_universe_measures_map_set_t<K, V>(
    before:Map_Set_T<K, V>, result:Map_Set_T<K, V>, key:Set<K>, value:V)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Size() <= before.UCardinalityKeys() then before.UCardinalityKeys() else key.Size())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  max_by_insert(before.Universe().Keys, key.Model(), item => |item|);
}

lemma insert_universe_measures_map_map_set_t<K, V, R>(
    before:Map_MapSet_T<K, V, R>, result:Map_MapSet_T<K, V, R>,
    key:Map_Set_T<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Cardinality() <= before.UCardinalityKeys()
      then before.UCardinalityKeys() else key.Cardinality())
  ensures result.UCardinalityKeysKeys() ==
    (if key.CardinalityKeys() <= before.UCardinalityKeysKeys()
      then before.UCardinalityKeysKeys() else key.CardinalityKeys())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys();
  reveal before.UCardinalityKeysKeys(), result.UCardinalityKeysKeys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  max_by_insert(before.Universe().Keys, key.Model(), item => |item|);
  max_by_insert(before.Universe().Keys, key.Model(), SetKeyCardinality);
}

// Update agreement.
// Lift native update agreement to wrapper models and universes during construction.

lemma update_agreement_map_map_set_t<K, V, R>(
    M:Map_MapSet_T<K, V, R>, key:map<set<K>, V>, value:R)
  requires M.Valid()
  ensures M.Model()[key := value].Keys <= M.Universe()[key := value].Keys
  ensures forall entry {:trigger M.Model()[key := value][entry]} |
    entry in M.Model()[key := value].Keys ::
    M.Model()[key := value][entry] == M.Universe()[key := value][entry]
{
  reveal M.Valid();
  map_update_agreement(M.Model(), M.Universe(), key, value);
}
