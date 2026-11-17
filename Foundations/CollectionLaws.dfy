
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
  forall A | A in A'
    ensures |A| <= |B|
  { subset_cardinality_bound_set(A, B); }
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

// Native updates: preserve inclusion and value agreement after a common update.
lemma update_agreement_map<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures model[key := value].Keys <= universe[key := value].Keys
  ensures forall entry {:trigger model[key := value][entry]} |
    entry in model[key := value].Keys ::
    model[key := value][entry] == universe[key := value][entry]
{}
