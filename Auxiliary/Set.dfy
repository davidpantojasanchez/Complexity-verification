
const constant:nat := 1


type Set< T(==) > {
  
  ghost function Model():set<T>         // Estado actual

  ghost function Universe():set<T>      // Upper bound del estado actual

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function Size():nat
  { Cardinality()*constant }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  method {:axiom} Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + constant
  
  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + constant
  
  method {:axiom} nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + constant
  
  method {:axiom} Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures  b == (e in Model()) 
    ensures counter_out == counter_in + Size()
  
  method {:axiom} Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures if e in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() + 1
    ensures counter_out == counter_in + Size()

  method {:axiom} Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures  R.Model() == Model() - {e}
    ensures if e !in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() - 1
    ensures counter_out == counter_in + Size()
  
  method {:axiom} Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + Size()

}



type SetSet< T(==) > {

  ghost function Model():set<set<T>>

  ghost function Universe():set<set<T>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function {:axiom} maximumSizeElements():nat
    ensures forall s | s in Universe() :: maximumSizeElements() >= |s|*constant
    ensures exists s :: s in Universe() && maximumSizeElements() == |s|*constant

  ghost function Size():nat
  { Cardinality()*maximumSizeElements() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  method {:axiom} Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures e.Valid()
    requires Model() != {}
    ensures e.Size() <= maximumSizeElements()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + maximumSizeElements()

  method {:axiom} Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + constant
  
  method {:axiom} nElements(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + constant
  
  method {:axiom} Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model()) 
    ensures counter_out == counter_in + Size()
  
  method {:axiom} Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() + constant
    ensures counter_out == counter_in + Size()

  method {:axiom} Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() - 1
    ensures counter_out == counter_in + Size()

  method {:axiom} Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures counter_out == counter_in + Size()
}



type SetSetSet< T(==) > {

  ghost function Model():set<set<set<T>>>

  ghost function Universe():set<set<set<T>>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function {:axiom} maximumSizeElements():nat
    ensures forall s | s in Universe() :: maximumSizeElements() >= |s|*maximumSizeElements'()
    ensures exists s :: s in Universe() && maximumSizeElements() == |s|*maximumSizeElements'()

  ghost function {:axiom} maximumSizeElements'():nat
    ensures forall s | s in Universe() :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*constant)
    ensures exists s | s in Universe() :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*constant)


  ghost function Size():nat
  { Cardinality()*maximumSizeElements() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  method {:axiom} Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures e.Valid()
    requires Model() != {}
    ensures e.maximumSizeElements() == maximumSizeElements'()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + maximumSizeElements()

  method {:axiom} Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + constant
  
  method {:axiom} nElements(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    requires Valid()
    ensures  size == Cardinality()
    ensures counter_out == counter_in + constant
  
  method {:axiom} Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures  b == (e.Model() in Model()) 
    ensures counter_out == counter_in + Size()
  
  method {:axiom} Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() + constant
    ensures if e.Model() in Universe() then |R.Universe()| == |Universe()|
            else |R.Universe()| == |Universe()| + constant
    ensures counter_out == counter_in + Size()

  method {:axiom} Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == Cardinality()
            else |R.Model()| == Cardinality() - 1
    ensures counter_out == counter_in + Size()

  method {:axiom} Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures R.maximumSizeElements'() == maximumSizeElements'()
    ensures counter_out == counter_in + Size()

}



method {:axiom} NewSet<T(==)>(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
method {:axiom} NewSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
method {:axiom} NewSetSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}

method {:axiom} NewSet_params<T(==)>(ghost U:set<T>, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
method {:axiom} NewSetSet_params<T(==)>(ghost U:set<set<T>>, ghost maximumSizeElements:nat, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.maximumSizeElements() == maximumSizeElements
method {:axiom} NewSetSetSet_params<T(==)>(ghost U:set<set<set<T>>>, ghost maximumSizeElements:nat, ghost maximumSizeElements':nat, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.maximumSizeElements() == maximumSizeElements
  ensures R.maximumSizeElements'() == maximumSizeElements'



ghost predicate init_Set(S:Set) {
    (S.Model() == S.Universe())
}
ghost predicate init_SetSet(S:SetSet) {
    (S.Model() == S.Universe())
}
ghost predicate init_SetSetSet(S:SetSetSet) {
    (S.Model() == S.Universe())
}

ghost predicate in_universe_Set(S:Set, U:Set)
{
  S.Valid() &&
  U.Valid() &&
  (S.Universe() <= U.Model())
}
ghost predicate in_universe_SetSet(S:SetSet, U:SetSet) {
  S.Valid() &&
  U.Valid() &&
  (S.Universe() <= U.Model()) &&
  (S.maximumSizeElements() <= U.maximumSizeElements())
}
ghost predicate in_universe_SetSetSet(S:SetSetSet, U:SetSetSet) {
  S.Valid() &&
  U.Valid() &&
  (S.Universe() <= U.Model()) &&
  (S.maximumSizeElements() <= U.maximumSizeElements()) &&
  (S.maximumSizeElements'() <= U.maximumSizeElements'())
}

