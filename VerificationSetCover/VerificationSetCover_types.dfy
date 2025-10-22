include "../Problems/SetCover.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) returns (b:bool, ghost counter:nat)   
requires forall s | s in S.Model() :: s <= U.Model()

requires init_Set(U)
requires init_SetSet(S)
requires init_SetSet(I)
requires S.maximumSizeElements() <= |U.Model()|
requires I.maximumSizeElements() <= |U.Model()|         // ????

ensures b == (I.Model() <= S.Model() && isCover(U.Model(), I.Model()) && |I.Model()| <= k)
ensures counter <= poly(U, S, k, I)
{
  counter := 0;

  var I_cardinality:int;
  I_cardinality, counter := I.Cardinality(counter);
  var I_seq_S:bool;
  I_seq_S, counter := isSubset(I, S, counter);

  if (!(I_seq_S && I_cardinality <= k)) {
    assert counter <= poly_isSubset(I, S) + constant;
    return false, counter;
  }

  var U':Set<int>;
  U', counter := U.Copy(counter);
  b := true;
  var U'_empty:bool;
  U'_empty, counter := U'.Empty(counter);

  assert counter <= poly_isSubset(I, S) + U.Size() + 2*constant;
  while (!U'_empty && b)
    // Termination
    decreases |U'.Model()|
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant in_universe_Set(U', U)
    invariant in_universe_SetSet(I, S)
    invariant U'.Valid()
    // Regular invariants
    invariant b == isCover(U.Model() - U'.Model() , I.Model())
    // Counter
    invariant counter <= poly_isSubset(I, S) + U.Size() + 2*constant + (|U.Model()| - |U'.Model()|)*poly_outer_loop(U, S, k)
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
  decreases |S1'.Model()|
  invariant S1'_empty == (S1'.Model() == {})
  // Types
  invariant S1'.Valid()
  invariant in_universe_SetSet(S1', S1)
  // Regular invariants
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Counter
  invariant counter <= counter_in + S1.Size() + constant + (|S1.Model()| - |S1'.Model()|)*(poly_isSubset_loop(S1, S2))
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
ensures |S1''.Model()| == |S1'.Model()| - 1
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
requires in_universe_SetSet(I, S)
// Invariant in
requires isCover(U.Model() - U'.Model(), I.Model())
// Termination out
ensures |U''.Model()| == |U'.Model()| - 1
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
  in_universe_lemma_SetSet(I, S);

  counter := counter_in;
  var u:int;
  u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var I':SetSet<int>;
  I', counter := I.Copy(counter);

  var b2:bool := false;
  var I'_empty:bool;
  I'_empty, counter := I'.Empty(counter);
  assert counter <= counter_in + 2*constant + U.Size() + S.Size();
  
  while (!I'_empty && !b2)
    // Termination
    decreases |I'.Model()|
    invariant I'_empty == (I'.Model() == {})
    // Types
    invariant I'.Valid()
    invariant in_universe_SetSet(I, S)
    invariant in_universe_SetSet(I', I)
    // Regular invariants
    invariant b2 == (exists i' | i' in I.Model() - I'.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + 2*constant + U.Size() + S.Size() + (|I.Model()|-|I'.Model()|)*(poly_inner_loop(U, S, k) + constant)
  {
    b2, I', I'_empty, counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  b1 := b2;

  U''_empty, counter := U''.Empty(counter);

  assert U.Model() - U''.Model() == U.Model() - U'.Model() + {u};
  assert counter <= counter_in + 3*constant + U.Size() + S.Size() + (|S.Model()|)*(poly_inner_loop(U, S, k) + constant) by {
    assert counter <= counter_in + 3*constant + U.Size() + S.Size() + (|I.Model()|)*(poly_inner_loop(U, S, k) + constant);
    assert in_universe_SetSet(I, S);
  }
  assert counter <= counter_in + poly_outer_loop(U, S, k);
}



method verifySetCover_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, I':SetSet<int>, u:int, ghost counter_in:nat) returns (b2:bool, I'':SetSet<int>, I''_empty:bool, ghost counter:nat)
// Termination in
requires I'.Model() != {}
// Types in
requires U.Valid()
requires in_universe_SetSet(I, S)
requires in_universe_SetSet(I', I)
// Invariant in
requires !(exists i' | i' in I.Model() - I'.Model() :: u in i')
// Termination out
ensures |I''.Model()| == |I'.Model()| - 1
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
  in_universe_lemma_SetSet(I, S);

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
ensures poly_isSubset(I, S) + U.Size() + 2*constant + (|U.Model()| - |U'.Model()|)*poly_outer_loop(U, S, k) <= poly(U, S, k, I)
{
  counter_simplification_aux_1(U, S, k, I, U');
  assert  poly_isSubset(I, S) + U.Size() + 2*constant + (|U.Model()| - |U'.Model()|)*poly_outer_loop(U, S, k)
          <=
          I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
          2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
  counter_simplification_aux_2(U, S, k, I);
  assert  I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
          2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant
          <=
          poly(U, S, k, I);
}
lemma counter_simplification_aux_1(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>)
requires in_universe_Set(U', U)
requires U.Valid()
requires S.Valid()
requires I.Valid()
ensures poly_isSubset(I, S) + U.Size() + 2*constant + (|U.Model()| - |U'.Model()|)*poly_outer_loop(U, S, k)
        <=
        I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
        2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant
{
  if_smaller_then_less_cardinality(U'.Model(), U.Model());
  mult_preserves_order((|U.Model()| - |U'.Model()|), poly_outer_loop(U, S, k), |U.Model()|, poly_outer_loop(U, S, k));
  
  assert poly_outer_loop(U, S, k) == (3*constant + U.Size() + S.Size() + |S.Model()|*poly_inner_loop(U, S, k) + constant*|S.Model()|);
  assert poly_inner_loop(U, S, k) == S.Size() + 2*S.maximumSizeElements() + constant;
  assert poly_isSubset(I, S) == (|I.Model()| + constant)*I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + constant;
  
  calc <= {
    poly_isSubset(I, S) + U.Size() + 2*constant + |U.Model()|*poly_outer_loop(U, S, k);
    poly_isSubset(I, S) + U.Size() + 2*constant + |U.Model()|*(3*constant + U.Size() + S.Size() + |S.Model()|*poly_inner_loop(U, S, k) + constant*|S.Model()|);
    poly_isSubset(I, S) + U.Size() + 2 + 3*|U.Model()| + |U.Model()|*U.Size() + |U.Model()|*S.Size() + |U.Model()|*|S.Model()|*poly_inner_loop(U, S, k) + |U.Model()|*|S.Model()|;
    poly_isSubset(I, S) + U.Size() + 2 + 3*|U.Model()| + |U.Model()|*U.Size() + |U.Model()|*S.Size() + |U.Model()|*|S.Model()|*(S.Size() + 2*S.maximumSizeElements() + constant) + |U.Model()|*|S.Model()|;
    poly_isSubset(I, S) + U.Size() + 2 + 3*|U.Model()| + |U.Model()|*U.Size() + |U.Model()|*S.Size() + |U.Model()|*|S.Model()|*S.Size() + 2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*|S.Model()| + |U.Model()|*|S.Model()|;
    poly_isSubset(I, S) + |U.Model()|*|S.Model()|*S.Size() + 2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 2*constant;
    (|I.Model()| + constant)*I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
    
    I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
  }
}
lemma counter_simplification_aux_2(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>)
requires U.Valid()
requires S.Valid()
requires I.Valid()
ensures I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant
    <=
    poly(U, S, k, I)
{
  mult_preserves_order(|I.Model()|, I.maximumSizeElements(), |I.Universe()|, I.maximumSizeElements());
  mult_preserves_order(|S.Model()|, S.maximumSizeElements(), |S.Universe()|, S.maximumSizeElements());
  mult_preserves_order(2*|U.Model()|, |S.Model()|*S.maximumSizeElements(), 2*|U.Model()|, S.Size());
  associativity(2*|U.Model()|, |S.Model()|, S.maximumSizeElements());
  calc <= {
    
    I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + |I.Model()|*I.maximumSizeElements() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
    
    I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + I.Size() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*(|S.Model()|*S.maximumSizeElements()) + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
    
    I.Size()*|I.Model()| + I.Size() + |I.Model()|*S.Size() + I.Size() + |I.Model()| + |U.Model()|*|S.Model()|*S.Size() +
    2*|U.Model()|*S.Size() + |U.Model()|*U.Size() + |U.Model()|*S.Size() + 2*|U.Model()|*|S.Model()| + U.Size() + 3*|U.Model()| + 3*constant;
    
    S.Size()*|U.Model()|*|S.Model()| + I.Size()*|I.Model()| + S.Size()*|I.Model()| + 3*S.Size()*|U.Model()| + U.Size()*|U.Model()| + 2*|U.Model()|*|S.Model()| + 2*I.Size() + U.Size() + |I.Model()| + 3*|U.Model()| + 3*constant;
  }
}


ghost function poly_inner_loop(U:Set<int>, S:SetSet<int>, k:nat) : (o:nat)
{
  S.Size() + 2*S.maximumSizeElements() + constant
}
ghost function poly_outer_loop(U:Set<int>, S:SetSet<int>, k:nat) : (o:nat)
{
  3*constant + U.Size() + S.Size() + |S.Model()|*poly_inner_loop(U, S, k) + constant*|S.Model()|
}
ghost function poly_isSubset_loop(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  S1.Size() + S2.Size() + S1.maximumSizeElements() + constant
}
ghost function poly_isSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  (|S1.Model()| + constant)*S1.Size() + |S1.Model()|*S2.Size() + |S1.Model()|*S1.maximumSizeElements() + |S1.Model()| + constant
}

ghost function poly(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
requires U.Valid()
requires S.Valid()
requires I.Valid()
{
  S.Size()*|U.Model()|*|S.Model()| + I.Size()*|I.Model()| + S.Size()*|I.Model()| + 3*S.Size()*|U.Model()| + U.Size()*|U.Model()| + 2*|U.Model()|*|S.Model()| + 2*I.Size() + U.Size() + |I.Model()| + 3*|U.Model()| + 3*constant
}
