include "../Lemmas/NativeCollectionLemmas.dfy"
/*
Traits for sets of different levels of nesting
Concrete implementations are defined in ConcreteSet.dfy.
*/

trait SetFamily<E> {
  ghost function Model():set<E>
  ghost function Universe():set<E>
  ghost predicate Valid()
    ensures Valid() ==> Model() <= Universe()

  ghost predicate Init() {
    Valid() && Model() == Universe()
  }

  ghost predicate UniverseWithin(reference:SetFamily<E>) {
    Valid() && reference.Valid() && Universe() <= reference.Model()
  }

  lemma universe_within_transitive(middle:SetFamily<E>, reference:SetFamily<E>)
    requires UniverseWithin(middle)
    requires middle.UniverseWithin(reference)
    ensures UniverseWithin(reference)
  {}

  ghost function Size():nat
  ghost function USize():nat

  ghost function CostIsEmpty():nat { 1 }
  ghost function CostCount():nat { 1 }
  ghost function CostEqual(other:SetFamily<E>):nat { Size() + other.Size() + 1 }
  ghost function UCostEqual(other:SetFamily<E>):nat { USize() + other.USize() + 1 }
  ghost function CostContains():nat { Size() + 1 }
  ghost function UCostContains():nat { USize() + 1 }
  ghost function CostAdd():nat { Size() + 1 }
  ghost function UCostAdd():nat { USize() + 1 }
  ghost function CostRemove():nat { Size() + 1 }
  ghost function UCostRemove():nat { USize() + 1 }
  ghost function CostCopy():nat { Size() + 1 }
  ghost function UCostCopy():nat { USize() + 1 }
}

trait Set<T(==)> extends SetFamily<T> {
  // Compilable representation view. Intended for concrete implementations only
  function ExecutableModel():set<T>
  // Opaque boundary keeps the compiled representation out of client proofs
  ghost function {:opaque} Model():set<T> { ExecutableModel() }
  // Upper bound of the model. Used for adding simpler computational costs on changing models
  ghost function Universe():set<T>

  // Indicates that the model satisfies the required validity constraints
  // Model-to-universe measure bounds follow from inclusion, but they are added to help the verifier
  ghost predicate Valid()
    ensures Valid() ==> Model() <= Universe()
  {
    Model() <= Universe() &&
    Cardinality() <= UCardinality() &&
    Size() <= USize()
  }

  ghost function Size():nat { Cardinality() }
  ghost function USize():nat { UCardinality() }
  
  ghost function Cardinality():(c:nat) { |Model()| }
  ghost function UCardinality():nat { |Universe()| }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + CostPick()

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method Equal(other:Set<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures counter_out == counter_in + CostAdd()
    ensures counter_out <= counter_in + UCostAdd()

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPick():nat { 1 }
  
  // Complexity bounds

  lemma universe_within_bound(U:Set<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Size() <= USize() <= U.Size() <= U.USize()
  {
    subset_cardinality_bound(Universe(), U.Model());
  }

}


trait SetSet<T(==)> extends SetFamily<set<T>> {
  function ExecutableModel():set<set<T>>
  ghost function {:opaque} Model():set<set<T>> { ExecutableModel() }
  ghost function Universe():set<set<T>>

  ghost predicate Valid()
    ensures Valid() ==> Model() <= Universe()
  {
    Model() <= Universe() &&
    Cardinality() <= UCardinality() &&
    Cardinality1() <= UCardinality1() &&
    Size() <= USize() &&
    Size1() <= USize1()
  }
  
  ghost function Size():nat { Cardinality() * Cardinality1() }
  ghost function USize():nat { UCardinality() * UCardinality1() }
  ghost function Size1():nat { Cardinality1() }
  ghost function USize1():nat { UCardinality1() }

  ghost function Cardinality():(c:nat) { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Size() <= UCardinality1()
    ensures e.USize() <= UCardinality1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick(e)
    ensures counter_out <= counter_in + UCostPick()

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method Equal(other:SetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size() <= UCardinality1() then R.UCardinality1() == UCardinality1()
            else R.UCardinality1() == e.Size()
    ensures (R.UCardinality1() == UCardinality1()) || (R.UCardinality1() == e.Size())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd()
    ensures counter_out <= counter_in + UCostAdd()

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() <= UCardinality1()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality1() <= UCardinality1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPick(e:Set<T>):nat { e.Size() + 1 }
  ghost function UCostPick():nat { UCardinality1() + 1 }

  // Complexity bounds

  lemma universe_within_bound(U:SetSet<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures Size() <= USize() <= U.Size() <= U.USize()
    ensures Size1() <= USize1() <= U.Size1() <= U.USize1()
  {
    reveal UCardinality1();
    subset_cardinality_bound(Universe(), U.Model());
    max_by_monotonic(Universe(), U.Model(), item => |item|);
    nonnegative_product_monotonic(UCardinality(), UCardinality1(), U.Cardinality(), U.Cardinality1());
  }

  lemma u_size_bound(count:nat, member:nat)
    requires Valid()
    requires UCardinality() <= count && UCardinality1() <= member
    ensures USize() <= count*member
  {
    nonnegative_product_monotonic(UCardinality(), UCardinality1(), count, member);
  }

  lemma u_cardinality1_bound(bound:nat)
    requires Valid()
    requires forall s | s in Universe() :: |s| <= bound
    ensures UCardinality1() <= bound
  {
    reveal UCardinality1();
    max_by_bound(Universe(), bound, item => |item|);
  }

}


trait SetSetSet<T(==)> extends SetFamily<set<set<T>>> {
  function ExecutableModel():set<set<set<T>>>
  ghost function {:opaque} Model():set<set<set<T>>> { ExecutableModel() }
  ghost function Universe():set<set<set<T>>>

  ghost predicate Valid()
    ensures Valid() ==> Model() <= Universe()
  {
    Model() <= Universe() &&
    Cardinality() <= UCardinality() &&
    Cardinality1() <= UCardinality1() &&
    Cardinality2() <= UCardinality2() &&
    Size() <= USize() &&
    Size1() <= USize1() &&
    Size2() <= USize2()
  }

  ghost function Size():nat { Cardinality()*Size1() }
  ghost function USize():nat { UCardinality()*USize1() }
  ghost function Size1():nat { Cardinality1() * Cardinality2() }
  ghost function USize1():nat { UCardinality1() * UCardinality2() }
  ghost function Size2():nat { Cardinality2() }
  ghost function USize2():nat { UCardinality2() }

  ghost function Cardinality():(c:nat) { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }
  ghost function Cardinality2():nat { MaxMemberCardinality_setset(Model()) }
  ghost function {:opaque} UCardinality2():nat { MaxMemberCardinality_setset(Universe()) }

  method Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Cardinality() <= UCardinality1() && e.UCardinality() <= UCardinality1()
    ensures e.Cardinality1() <= UCardinality2() && e.UCardinality1() <= UCardinality2()
    ensures e.Size() <= USize1()
    ensures e.USize() <= USize1()
    ensures e.USize1() <= USize2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick(e)
    ensures counter_out <= counter_in + UCostPick()

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  
  method Equal(other:SetSetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.UCardinality1() == (if e.Cardinality() <= UCardinality1() then UCardinality1() else e.Cardinality())
    ensures R.UCardinality2() == (if e.Cardinality1() <= UCardinality2() then UCardinality2() else e.Cardinality1())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd()
    ensures counter_out <= counter_in + UCostAdd()

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == UCardinality1()
    ensures R.UCardinality2() == UCardinality2()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality2() == Cardinality2()
    ensures R.USize1() == Size1()
    ensures R.USize2() == Size2()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPick(e:SetSet<T>):nat { e.Size() + 1 }
  ghost function UCostPick():nat { USize1() + 1 }

  // Complexity bounds

  lemma universe_within_bound(U:SetSetSet<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures Cardinality2() <= UCardinality2() <= U.Cardinality2() <= U.UCardinality2()
    ensures Size() <= USize() <= U.Size() <= U.USize()
    ensures Size1() <= USize1() <= U.Size1() <= U.USize1()
    ensures Size2() <= USize2() <= U.Size2() <= U.USize2()
  {
    reveal UCardinality1(), UCardinality2();
    subset_cardinality_bound(Universe(), U.Model());
    max_by_monotonic(Universe(), U.Model(), item => |item|);
    max_by_monotonic(Universe(), U.Model(), item => MaxCardinality_set(item));
    nonnegative_product_monotonic(UCardinality1(), UCardinality2(), U.Cardinality1(), U.Cardinality2());
    nonnegative_product_monotonic(UCardinality(), USize1(), U.Cardinality(), U.Size1());
  }

  lemma u_size_bound(count:nat, members:nat, leaves:nat)
    requires Valid()
    requires UCardinality() <= count && UCardinality1() <= members
    requires UCardinality2() <= leaves
    ensures USize() <= count*members*leaves
    ensures USize1() <= members*leaves
    ensures USize2() <= leaves
  {
    nonnegative_product_monotonic(UCardinality1(), UCardinality2(), members, leaves);
    nonnegative_product_monotonic(UCardinality(), USize1(), count, members*leaves);
    multiplication_associative(count, members, leaves);
  }

  lemma u_cardinality1_bound(bound:nat)
    requires Valid()
    requires forall child | child in Universe() :: |child| <= bound
    ensures UCardinality1() <= bound
  {
    reveal UCardinality1();
    max_by_bound(Universe(), bound, item => |item|);
  }

  lemma u_cardinality2_bound(bound:nat)
    requires Valid()
    requires forall s | s in Universe() :: MaxCardinality_set(s) <= bound
    ensures UCardinality2() <= bound
  {
    reveal UCardinality2();
    max_by_bound(Universe(), bound, item => MaxCardinality_set(item));
  }

}


// Construction cost for Set, SetSet and SetSetSet, independent of element type
ghost function CostNew_SetFamily():nat { 1 }
