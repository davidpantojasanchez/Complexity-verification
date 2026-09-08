include "../Problems/SetCover.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) returns (accepted:bool, ghost counter:nat)   
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires SetCoverAdmissibleCertificate(U.Model(), I.Model())

  requires init_Set(U)
  requires init_SetSet(S)
  requires init_SetSet(I)
  requires S.UBSize1() <= U.UBSize0()
  requires I.UBSize1() <= U.UBSize0()

  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, I.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  ensures counter <= poly(U, S, k, I)
{
  counter := 0;
  var I_cardinality:int;
  I_cardinality, counter := I.nElements(counter);
  if (k < I_cardinality) {
    return false, counter;
  }
  var S_cardinality:int;
  S_cardinality, counter := S.nElements(counter);
  if (S_cardinality < I_cardinality) {
    if I.Model() <= S.Model() {
      if_smaller_then_less_cardinality(I.Model(), S.Model());
    }
    return false, counter;
  }
  var I_seq_S:bool;
  I_seq_S, counter := isSubset(I, S, counter);
  if (!I_seq_S) {
    counter_simplification_special_case(U, S, k, I);
    return false, counter;
  }
  assert I.Model() <= S.Model();
  if_smaller_then_less_cardinality(I.Model(), S.Model());
  assert I.Cardinality() <= S.Cardinality();

  var U':Set<int>;
  U', counter := U.Copy(counter);
  accepted := true;
  var U'_empty:bool;
  U'_empty, counter := U'.Empty(counter);
  
  while (!U'_empty && accepted)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant in_universe_Set(U', U)
    invariant I.Valid()
    invariant S.Valid()
    invariant I.Model() <= S.Model()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.UBSize1() <= U.UBSize0()
    invariant U'.Valid()
    // Regular invariants
    invariant accepted == isCover(U.Model() - U'.Model() , I.Model())
    // Counter
    invariant counter <= cost_SetSetNElements(I) + cost_SetSetNElements(S) + poly_isSubset(I, S) +
                         cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
                         (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k, I)
  {
    accepted, U', U'_empty, counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  assert accepted ==> U.Model() - U'.Model() == U.Model();
  counter_simplification(U, S, k, I, U');
}


method isSubset(S1:SetSet<int>, S2:SetSet<int>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  requires S1.Valid()
  requires S2.Valid()
  ensures b == (S1.Model() <= S2.Model())
  ensures counter <= counter_in + poly_isSubset(S1, S2)
{
  counter := counter_in;
  b := true;
  var S1';
  S1', counter := S1.Copy(counter);
  var S1'_empty:bool;
  S1'_empty, counter := S1'.Empty(counter);
  
  while (!S1'_empty)
  // Termination
  decreases S1'.Cardinality()
  invariant S1'_empty == (S1'.Model() == {})
  // Types
  invariant S1'.Valid()
  invariant in_universe_SetSet(S1', S1)
  // Regular invariants
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Counter
  invariant counter <= counter_in + cost_SetSetCopyUniverse(S1) + cost_SetSetEmpty(S1) +
                       (S1.Cardinality() - S1'.Cardinality())*poly_isSubset_loop(S1, S2)
  {
    S1', S1'_empty, b, counter := isSubset_loop(S1, S2, S1', counter, b);
  }
}


method isSubset_loop(S1:SetSet<int>, S2:SetSet<int>, S1':SetSet<int>, ghost counter_in:nat, b:bool) returns (S1'':SetSet<int>, S1'_empty:bool, b':bool, ghost counter:nat)
  // Termination in
  requires S1'.Model() != {}
  // Types in
  requires in_universe_SetSet(S1', S1)
  requires S2.Valid()
  // Invariant in
  requires b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Termination out
  ensures S1''.Cardinality() == S1'.Cardinality() - 1
  ensures S1'_empty == (S1''.Model() == {})
  // Types out
  ensures S1''.Valid()
  ensures in_universe_SetSet(S1'', S1)
  // Invariant out
  ensures b' == ((S1.Model() - S1''.Model()) <= S2.Model())
  // Counter
  ensures counter <= counter_in + poly_isSubset_loop(S1, S2)
{
  in_universe_lemma_SetSet(S1', S1);

  counter := counter_in;
  var s:Set<int>;
  s, counter := S1'.Pick(counter);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter);
  S1'_empty, counter := S1''.Empty(counter);
}


method verifySetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>, ghost counter_in:nat) returns (b1:bool, U'':Set<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires U.Valid()
  requires U'.Valid()
  requires S.Valid()
  requires I.Valid()
  requires in_universe_Set(U', U)
  requires I.Model() <= S.Model()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  // Invariant in
  requires isCover(U.Model() - U'.Model(), I.Model())
  // Termination out
  ensures U''.Cardinality() == U'.Cardinality() - 1
  ensures U''_empty == (U''.Model() == {})
  // Types out
  ensures U''.Valid()
  ensures in_universe_Set(U'', U)
  // Invariant out
  ensures b1 == isCover(U.Model() - U''.Model(), I.Model())
  // Counter
  ensures counter <= counter_in + poly_outer_loop(U, S, k, I)
{
  in_universe_lemma_Set(U', U);
  counter := counter_in;
  var u:int;
  u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var I':SetSet<int>;
  I', counter := I.Copy(counter);

  var b2:bool := false;
  var I'_empty:bool;
  I'_empty, counter := I'.Empty(counter);
  assert counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                               cost_SetSetCopyUniverse(I) + cost_SetSetEmpty(I);
  
  while (!I'_empty && !b2)
    // Termination
    decreases I'.Cardinality()
    invariant I'_empty == (I'.Model() == {})
    // Types
    invariant I'.Valid()
    invariant in_universe_SetSet(I', I)
    invariant I.Valid()
    invariant S.Valid()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.UBSize1() <= U.UBSize0()
    // Regular invariants
    invariant b2 == (exists i' | i' in I.Model() - I'.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                         cost_SetSetCopyUniverse(I) + cost_SetSetEmpty(I) +
                         (I.Cardinality()-I'.Cardinality())*
                           (poly_inner_loop(U, S, k, I) + cost_SetSetEmpty(I))
  {
    b2, I', I'_empty, counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  b1 := b2;

  U''_empty, counter := U''.Empty(counter);

  assert U.Model() - U''.Model() == U.Model() - U'.Model() + {u};
  assert counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                       cost_SetSetCopyUniverse(I) + cost_SetSetEmpty(I) +
                       I.Cardinality()*(poly_inner_loop(U, S, k, I) + cost_SetSetEmpty(I)) +
                       cost_SetEmpty(U);
  mult_preserves_order(I.Cardinality(),
                       poly_inner_loop(U, S, k, I) + cost_SetSetEmpty(I),
                       I.UBCardinality(),
                       poly_inner_loop(U, S, k, I) + cost_SetSetEmpty(I));
}


method verifySetCover_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, I':SetSet<int>, u:int, ghost counter_in:nat) returns (b2:bool, I'':SetSet<int>, I''_empty:bool, ghost counter:nat)
  // Termination in
  requires I'.Model() != {}
  // Types in
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires in_universe_SetSet(I', I)
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  // Invariant in
  requires !(exists i' | i' in I.Model() - I'.Model() :: u in i')
  // Termination out
  ensures I''.Cardinality() == I'.Cardinality() - 1
  ensures I''_empty == (I''.Model() == {})
  // Types out
  ensures I''.Valid()
  ensures in_universe_SetSet(I'', I)
  // Invariant out
  ensures b2 == (exists i' | i' in I.Model() - I''.Model() :: u in i')
  // Counter
  ensures counter <= counter_in + poly_inner_loop(U, S, k, I)
{
  in_universe_lemma_SetSet(I', I);
  counter := counter_in;
  var i:Set<int>;
  i, counter := I'.Pick(counter);
  b2, counter := i.Contains(u, counter);
  I'', counter := I'.Remove(i, counter);
  I''_empty, counter := I''.Empty(counter);
}


lemma counter_simplification(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>)
  requires in_universe_Set(U', U)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  ensures cost_SetSetNElements(I) + cost_SetSetNElements(S) + poly_isSubset(I, S) +
          cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
          (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k, I) <=
          poly(U, S, k, I)
{
  in_universe_lemma_Set(U', U);
  mult_preserves_order(U.Cardinality() - U'.Cardinality(), poly_outer_loop(U, S, k, I),
                       U.Cardinality(), poly_outer_loop(U, S, k, I));
}
lemma counter_simplification_special_case(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  ensures cost_SetSetNElements(I) + cost_SetSetNElements(S) + poly_isSubset(I, S) <= poly(U, S, k, I)
{}


ghost function poly_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  cost_SetSetPickUniverse(I) +
  cost_SetContainsUniverse(U) +
  cost_SetSetRemoveUniverse(I) +
  cost_SetSetEmpty(I)
}
ghost function poly_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  cost_SetPick(U) + cost_SetRemoveUniverse(U) +
  cost_SetSetCopyUniverse(I) + cost_SetSetEmpty(I) +
  I.UBCardinality()*(poly_inner_loop(U, S, k, I) + cost_SetSetEmpty(I)) +
  cost_SetEmpty(U)
}
ghost function poly_isSubset_loop(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  cost_SetSetPickUniverse(S1) + cost_SetSetContainsUniverse(S2) +
  cost_SetSetRemoveUniverse(S1) + cost_SetSetEmpty(S1)
}
ghost function {:opaque} poly_isSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
  ensures o == cost_SetSetCopyUniverse(S1) + cost_SetSetEmpty(S1) +
               S1.UBCardinality()*poly_isSubset_loop(S1, S2)
{
  cost_SetSetCopyUniverse(S1) + cost_SetSetEmpty(S1) +
  S1.UBCardinality()*poly_isSubset_loop(S1, S2)
}


ghost function poly(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  ensures 1 <= o
{
  cost_SetSetNElements(I) + cost_SetSetNElements(S) + poly_isSubset(I, S) +
  cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
  U.UBCardinality()*poly_outer_loop(U, S, k, I)
}
