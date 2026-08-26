include "../Problems/SetCover.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) returns (b:bool, ghost counter:nat)   
  requires forall s | s in S.Model() :: s <= U.Model()
  requires k <= S.Cardinality()

  requires init_Set(U)
  requires init_SetSet(S)
  requires init_SetSet(I)
  requires S.UBSize1() <= U.Cardinality()
  requires I.UBSize1() <= U.Cardinality()

  ensures b == (I.Model() <= S.Model() && isCover(U.Model(), I.Model()) && I.Cardinality() <= k)
  ensures counter <= poly(U, S, k)
{
  counter := 0;
  var I_cardinality:int;
  I_cardinality, counter := I.nElements(counter);
  if (k < I_cardinality) {
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
  b := true;
  var U'_empty:bool;
  U'_empty, counter := U'.Empty(counter);
  
  while (!U'_empty && b)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant in_universe_Set(U', U)
    invariant I.Valid()
    invariant S.Valid()
    invariant I.Model() <= S.Model()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.UBSize1() <= U.Cardinality()
    invariant U'.Valid()
    // Regular invariants
    invariant b == isCover(U.Model() - U'.Model() , I.Model())
    // Counter
    invariant counter <= cost_nElements() + poly_isSubset(I, S) + cost_Copy(U.UBSize0()) + cost_Empty() +
                         (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k)
  {
    b, U', U'_empty, counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  assert b ==> U.Model() - U'.Model() == U.Model();
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
  invariant counter <= counter_in + cost_Copy(S1.UBSize0()) + cost_Empty() +
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
  requires I.UBSize1() <= U.Cardinality()
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
  ensures counter <= counter_in + poly_outer_loop(U, S, k)
{
  in_universe_lemma_Set(U', U);
  mult_preserves_order(I.Cardinality(), I.UBSize1(), S.Cardinality(), U.Cardinality());
  assert I.UBSize0() <= S.Cardinality()*U.Cardinality();

  counter := counter_in;
  var u:int;
  u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var I':SetSet<int>;
  I', counter := I.Copy(counter);

  var b2:bool := false;
  var I'_empty:bool;
  I'_empty, counter := I'.Empty(counter);
  assert counter <= counter_in + cost_Pick(0) + cost_Remove(U.UBSize0()) +
                               cost_Copy(S.Cardinality()*U.Cardinality()) + cost_Empty();
  
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
    invariant I.UBSize1() <= U.Cardinality()
    // Regular invariants
    invariant b2 == (exists i' | i' in I.Model() - I'.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + cost_Pick(0) + cost_Remove(U.UBSize0()) +
                         cost_Copy(S.Cardinality()*U.Cardinality()) + cost_Empty() +
                         (I.Cardinality()-I'.Cardinality())*(poly_inner_loop(U, S, k) + cost_Empty())
  {
    b2, I', I'_empty, counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  b1 := b2;

  U''_empty, counter := U''.Empty(counter);

  assert U.Model() - U''.Model() == U.Model() - U'.Model() + {u};
  assert counter <= counter_in + cost_Pick(0) + cost_Remove(U.UBSize0()) + cost_Copy(S.Cardinality()*U.Cardinality()) + 2*cost_Empty() + S.Cardinality()*(poly_inner_loop(U, S, k) + cost_Empty()) by {
    assert counter <= counter_in + cost_Pick(0) + cost_Remove(U.UBSize0()) + cost_Copy(S.Cardinality()*U.Cardinality()) + 2*cost_Empty() + I.Cardinality()*(poly_inner_loop(U, S, k) + cost_Empty());
    mult_preserves_order(I.Cardinality(), (poly_inner_loop(U, S, k) + cost_Empty()), S.Cardinality(), (poly_inner_loop(U, S, k) + cost_Empty()));
  }
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
  requires I.UBSize1() <= U.Cardinality()
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
  ensures counter <= counter_in + poly_inner_loop(U, S, k)
{
  in_universe_lemma_SetSet(I', I);
  mult_preserves_order(I.Cardinality(), I.UBSize1(), S.Cardinality(), U.Cardinality());
  assert I.UBSize0() <= S.Cardinality()*U.Cardinality();

  counter := counter_in;
  var i:Set<int>;
  i, counter := I'.Pick(counter);
  b2, counter := i.Contains(u, counter);
  I'', counter := I'.Remove(i, counter);
  I''_empty, counter := I''.Empty(counter);
}


lemma poly_isSubset_bound(U:Set<int>, S:SetSet<int>, I:SetSet<int>)
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.Cardinality()
  ensures poly_isSubset(I, S) <= poly_isSubset_upper_bound(U, S)
{
  mult_preserves_order(I.Cardinality(), I.UBSize1(), S.Cardinality(), U.Cardinality());
  assert I.UBSize0() <= S.Cardinality()*U.Cardinality();
  mult_preserves_order(I.Cardinality() + 1, I.UBSize0(), S.Cardinality() + 1, S.Cardinality()*U.Cardinality());
  mult_preserves_order(I.Cardinality(), S.UBSize0(), S.Cardinality(), S.UBSize0());
}

lemma counter_simplification(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>)
  requires in_universe_Set(U', U)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.Cardinality()
  ensures cost_nElements() + poly_isSubset(I, S) + cost_Copy(U.UBSize0()) + cost_Empty() +
          (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k) <= poly(U, S, k)
{
  in_universe_lemma_Set(U', U);
  poly_isSubset_bound(U, S, I);
  mult_preserves_order(U.Cardinality() - U'.Cardinality(), poly_outer_loop(U, S, k), U.Cardinality(), poly_outer_loop(U, S, k));
}
lemma counter_simplification_special_case(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.Cardinality()
  ensures cost_nElements() + poly_isSubset(I, S) <= poly(U, S, k)
{
  poly_isSubset_bound(U, S, I);
}


ghost function poly_inner_loop(U:Set<int>, S:SetSet<int>, k:nat) : (o:nat)
{
  cost_Pick(U.Cardinality()) +
  cost_Contains(U.Cardinality()) +
  cost_Remove(S.Cardinality()*U.Cardinality()) +
  cost_Empty()
}
ghost function poly_outer_loop(U:Set<int>, S:SetSet<int>, k:nat) : (o:nat)
{
  cost_Pick(0) + cost_Remove(U.UBSize0()) +
  cost_Copy(S.Cardinality()*U.Cardinality()) + 2*cost_Empty() +
  S.Cardinality()*(poly_inner_loop(U, S, k) + cost_Empty())
}
ghost function poly_isSubset_loop(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  cost_Pick(S1.UBSize1()) + cost_Contains(S2.UBSize0()) +
  cost_Remove(S1.UBSize0()) + cost_Empty()
}
ghost function {:opaque} poly_isSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
  ensures o == (S1.Cardinality() + 1)*S1.UBSize0() +
               S1.Cardinality()*S2.UBSize0() +
               S1.Cardinality()*S1.UBSize1() +
               4*S1.Cardinality() + 2
{
  cost_Copy(S1.UBSize0()) + cost_Empty() +
  S1.Cardinality()*poly_isSubset_loop(S1, S2)
}
ghost function {:opaque} poly_isSubset_upper_bound(U:Set<int>, S:SetSet<int>) : (o:nat)
  ensures o == (S.Cardinality() + 1)*(S.Cardinality()*U.Cardinality()) +
               S.Cardinality()*S.UBSize0() +
               S.Cardinality()*U.Cardinality() +
               4*S.Cardinality() + 2
{
  cost_Copy(S.Cardinality()*U.Cardinality()) + cost_Empty() +
  S.Cardinality()*(cost_Pick(U.Cardinality()) + cost_Contains(S.UBSize0()) +
                   cost_Remove(S.Cardinality()*U.Cardinality()) + cost_Empty())
}


ghost function poly(U:Set<int>, S:SetSet<int>, k:nat) : (o:nat)
  requires U.Valid()
  requires S.Valid()
  ensures 1 <= o
{
  cost_nElements() + poly_isSubset_upper_bound(U, S) +
  cost_Copy(U.UBSize0()) + cost_Empty() +
  U.Cardinality()*poly_outer_loop(U, S, k)
}
