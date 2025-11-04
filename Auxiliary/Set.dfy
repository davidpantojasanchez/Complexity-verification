include "../Auxiliary/Lemmas.dfy"


// Upper bound of the size of the basic type T
const constant:nat := 1


/*
Basic set (its elements have constant size)
It encapsulates the Dafny set
Contains ghost functions to assist in the verification of the properties of the set and on the computational cost of its operations
Has the typical set operations
*/
type Set< T(==) > {

  // Current state of the set
  ghost function Model():set<T>

  /*
  Upper bound of the state of the set
  Useful when we need to calculate the cost of methods that operate on changing sets
  * When an element is added, it is added to the universe (if it wasn't already there)
  * When an element is removed, the universe does not change
  * When a set is copied, the model of the original set becomes the universe of the new set
  If we are not adding elements outside the universe, we can express an upper bound of the computational cost of set operations as a
  function of the universe without requiring unnecessary calculations to ensure that the universe is an upper bound of the changing sets
  */
  ghost function Universe():set<T>

  // Function that returns if the set's universe is greater than the universe
  // It will appear frequently in preconditions and invariants to ensure that we are dealing with valid sets
  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  // Size of the set
  // Cardinality multiplied by the maximum size of the elements of the set, which in simple sets is constant
  ghost function Size():nat
  { Cardinality()*constant }

  // Cardinality of the set (of the set's model, not universe)
  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  // Returns an arbitrary element of the set
  // The counter increases by an upper bound of the cost of the operation, which in this case is constant
  method {:axiom} Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + constant
  
  // Checks if the set is empty
  method {:axiom} Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + constant
  
  // Returns the number of elements of the set
  method {:axiom} nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + constant
  
  // Checks in the set contains a given element
  method {:axiom} Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures  b == (e in Model()) 
    ensures counter_out == counter_in + Size()
  
  // Adds an element to the set
  // Ensures that the universe updates accordingly
  // Also ensures that the effect of the operation in the set's cardinality is correct, which is redundant but helps the verifier
  method {:axiom} Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + Size()

  // Removes an element from the set
  method {:axiom} Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures  R.Model() == Model() - {e}
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + Size()
  
  // Copies the set
  // Note that the new set's universe is initialized as the model of the original set, not the universe
  // We have chosen to initialize the universe this way because we find it simpler in the verifications, but both options are valid
  method {:axiom} Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + Size()

}


// Set of basic sets
type SetSet< T(==) > {

  ghost function Model():set<set<T>>

  ghost function Universe():set<set<T>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  // Upper limit of the size of the elements of the set (which are basic sets)
  ghost function {:axiom} maximumSizeElements():nat
    ensures forall s | s in Universe() :: maximumSizeElements() >= |s|*constant
    ensures exists s :: s in Universe() && maximumSizeElements() == |s|*constant

  ghost function Size():nat
  { Cardinality()*maximumSizeElements() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  // The returned basic set has at most size maximumSizeElements()
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
  
  // If the basic set to be added is larger than maximumSizeElements(), it updates its value
  // the postcondition (R.maximumSizeElements() == maximumSizeElements()) || (R.maximumSizeElements() == e.Size()) is redundant but useful for the verifier
  method {:axiom} Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model()
            then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + constant
    ensures if e.Size() <= maximumSizeElements()
            then R.maximumSizeElements() == maximumSizeElements()
            else R.maximumSizeElements() == e.Size()
    ensures (R.maximumSizeElements() == maximumSizeElements()) || (R.maximumSizeElements() == e.Size())
    ensures counter_out == counter_in + Size()

  method {:axiom} Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + Size()

  // The value of maximumSizeElements() is also passed to the copy
  method {:axiom} Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures counter_out == counter_in + Size()
}


// Set of sets of basic sets
type SetSetSet< T(==) > {

  ghost function Model():set<set<set<T>>>

  ghost function Universe():set<set<set<T>>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  // Upper bound of the size of the elements of the set (which are sets of basic sets)
  ghost function {:axiom} maximumSizeElements():nat
    ensures forall s | s in Universe() :: maximumSizeElements() >= |s|*maximumSizeElements'()
    ensures exists s :: s in Universe() && maximumSizeElements() == |s|*maximumSizeElements'()

  // Upper bound of the size of the elements of the elements of the set (which are basic sets)
  ghost function {:axiom} maximumSizeElements'():nat
    ensures forall s | s in Universe() :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*constant)
    ensures exists s | s in Universe() :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*constant)


  ghost function Size():nat
  { Cardinality()*maximumSizeElements() }

  ghost function Cardinality():(c:nat)
  ensures 0 <= c
  { |Model()| }

  // The returned set of sets will have at most size maximumSizeElements()
  // and its elements will have at most size maximumSizeElements'()
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
  
  // Ensures that maximumSizeElements() and maximumSizeElements'() are updated accordingly
  method {:axiom} Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model()
            then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + constant
    ensures if e.Model() in Universe()
            then |R.Universe()| == |Universe()|
            else |R.Universe()| == |Universe()| + constant
    ensures if e.Size() <= maximumSizeElements()
            then R.maximumSizeElements() == maximumSizeElements()
            else R.maximumSizeElements() == e.Size()
    ensures if e.maximumSizeElements() <= maximumSizeElements'()
            then R.maximumSizeElements'() == maximumSizeElements'()
            else R.maximumSizeElements'() == e.maximumSizeElements()
    ensures ((R.maximumSizeElements() == maximumSizeElements()) || (R.maximumSizeElements() == e.Size())) &&
            ((R.maximumSizeElements'() == maximumSizeElements'()) || (R.maximumSizeElements'() == e.maximumSizeElements()))
    ensures counter_out == counter_in + Size()

  method {:axiom} Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.maximumSizeElements() == maximumSizeElements()
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
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


// Creates an empty set, without specifying information about the universe of the set or the nature of its elements
// As Universe(), maxSizeElement() and maxSizeElement'() (non-compilable functions whose purpouse is to aid the verifier),
// we can leave them undetermined whenever they are not helpful
method {:axiom} New_Set<T(==)>(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
method {:axiom} New_SetSet<T(==)>(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
method {:axiom} New_SetSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}

// Creates an empty set, but specifies information about the universe and the nature of its elements
// This is useful for verifying properties and costs of the new set;
// we can use our human knowledge to indicate the verifier what do we expect the upper limits of the sizes of the set and its nested sets to be
// The set is not constrained by the values we indicate. If we add elements outside the expected limits, these values will change
method {:axiom} New_Set_params<T(==)>(ghost U:set<T>, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
method {:axiom} New_SetSet_params<T(==)>(ghost U:set<set<T>>, ghost maximumSizeElements:nat, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.maximumSizeElements() == maximumSizeElements
method {:axiom} New_SetSetSet_params<T(==)>(ghost U:set<set<set<T>>>, ghost maximumSizeElements:nat, ghost maximumSizeElements':nat, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in +1
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.maximumSizeElements() == maximumSizeElements
  ensures R.maximumSizeElements'() == maximumSizeElements'


// Used as a precondition, to ensure that at initialization the universe equals the model (and implicitly that the set is valid)
// It is not strictly required, but is be useful
ghost predicate init_Set(S:Set) {
    (S.Model() == S.Universe())
}
ghost predicate init_SetSet(S:SetSet) {
    (S.Model() == S.Universe())
}
ghost predicate init_SetSetSet(S:SetSetSet) {
    (S.Model() == S.Universe())
}

// Indicates that the universe of the first set is bounded by the second set
// Especially useful in the common scenario where we copy a set and then traverse the copy, removing elements in the process
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

