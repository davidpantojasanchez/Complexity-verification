include "../Foundations/Collections.dfy"
include "../Foundations/RepresentationCosts.dfy"
include "../Foundations/CollectionRepresentation.dfy"
/*
Traits for sets of different levels of nesting
Concrete implementations are defined in ConcreteSet.dfy.
*/

// Shared structural model, universe relation and work for all set shapes.
trait SetFamily<E> {
  ghost function Model():set<E>
  ghost function Universe():set<E>

  ghost predicate Valid()
    ensures Valid() ==> Model() <= Universe()

  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }

  ghost function Volume():nat
  ghost function UVolume():nat

  ghost predicate Init() {
    Valid() && Model() == Universe()
  }

  ghost predicate UniverseWithin(reference:SetFamily<E>) {
    Valid() && reference.Valid() && Universe() <= reference.Model()
  }

  // Structural work factors used by the common cost calculation.
  ghost function CombinedTraversalWork(other:SetFamily<E>):nat { Volume() + other.Volume() + 1 }
  ghost function TraversalWork():nat { Volume() + 1 }

  lemma universe_within_transitive(middle:SetFamily<E>, reference:SetFamily<E>)
    requires UniverseWithin(middle)
    requires middle.UniverseWithin(reference)
    ensures UniverseWithin(reference)
  {}
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
    Volume() <= UVolume()
  }
  
  ghost function Volume():nat { Cardinality() }
  ghost function UVolume():nat { UCardinality() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(weight))
    ensures Volume() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(weight)
  {
    representation_subset_set(Model(), Universe(), weight, Valid());
    RepresentationSize_set(Model(), weight)
  }

  ghost function USize(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(weight))
    ensures UVolume() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size
    ensures 1 <= size
  {
    RepresentationSize_set(Universe(), weight)
  }

  // Leaf interpretation is shared by model, retained universe and operands.
  ghost function LeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(weight)
  {
    representation_subset_set(Model(), Universe(), weight, Valid());
    MaxLeafBits_set(Model(), weight)
  }
  ghost function ULeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_set(Universe(), weight) }

  ghost function Cost(work:nat, operandSize:nat, context:SetContext<T>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.weight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method IsEmpty(ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Count(ghost counter_in:nat, ghost context:SetContext<T>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Pick(ghost counter_in:nat, ghost context:SetContext<T>) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e in Model()
    ensures e in Universe()
    ensures context.weight(e) <= Size(context.weight)
    ensures context.weight(e) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Equal(other:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.Size(context.weight), context)

  method Contains(e:T, ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + Cost(TraversalWork(), context.weight(e), context)

  method Add(e:T, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures R.ULeafBits(context.weight) <= MaxLeafWeight(ULeafBits(context.weight), context.weight(e))
    ensures counter_out == counter_in + Cost(TraversalWork(), context.weight(e), context)

  method Remove(e:T, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures R.Size(context.weight) <= Size(context.weight)
    ensures R.USize(context.weight) == USize(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), context.weight(e), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.Size(context.weight) == Size(context.weight) && R.USize(context.weight) == Size(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds


  // Numeric growth bounds are composed once from structural and leaf bounds.
  lemma u_leaf_bits_bound(bits:nat, weight:T -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: weight(item) <= bits
    ensures ULeafBits(weight) <= bits
  {
    max_leaf_bits_bound_set(Universe(), weight, bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, weight:T -> nat)
    requires UVolume() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USize(weight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(weight), volume, bits);
  }


  lemma universe_within_bound(U:Set<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures Size(context.weight) <= USize(context.weight) <= U.Size(context.weight) <= U.USize(context.weight)
    ensures LeafBits(context.weight) <= ULeafBits(context.weight) <= U.LeafBits(context.weight) <= U.ULeafBits(context.weight)
  {
    representation_subset_set(Universe(), U.Model(), context.weight);
    subset_cardinality_bound_set(Universe(), U.Model());
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
    Volume() <= UVolume() &&
    Volume1() <= UVolume1()
  }

  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }

  ghost function Volume():nat { Cardinality() * (1 + Cardinality1()) }
  ghost function UVolume():nat { UCardinality() * (1 + UCardinality1()) }
  ghost function Volume1():nat { Cardinality1() }
  ghost function UVolume1():nat { UCardinality1() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(weight))
    ensures Volume() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size && Cardinality1() <= size
    ensures Volume1() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(weight)
  {
    representation_subset_setset(Model(), Universe(), weight, Valid());
    RepresentationSize_setset(Model(), weight)
  }

  ghost function USize(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(weight))
    ensures UVolume() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size && UCardinality1() <= size
    ensures UVolume1() <= size
    ensures 1 <= size
  {
    reveal UCardinality1();
    RepresentationSize_setset(Universe(), weight)
  }

  ghost function LeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(weight)
  {
    representation_subset_setset(Model(), Universe(), weight, Valid());
    MaxLeafBits_setset(Model(), weight)
  }
  ghost function ULeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_setset(Universe(), weight) }

  ghost function Cost(work:nat, operandSize:nat, context:SetContext<T>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.weight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method IsEmpty(ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Count(ghost counter_in:nat, ghost context:SetContext<T>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Pick(ghost counter_in:nat, ghost context:SetContext<T>) returns (e:Set<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Volume() <= UCardinality1()
    ensures e.UVolume() <= UCardinality1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures e.USize(context.weight) == e.Size(context.weight)
    ensures e.Size(context.weight) <= Size(context.weight)
    ensures e.ULeafBits(context.weight) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(e.TraversalWork(), 0, context)

  method Equal(other:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.Size(context.weight), context)

  method Contains(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Add(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.UCardinality1() == (if e.Cardinality() <= UCardinality1() then UCardinality1() else e.Cardinality())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures R.ULeafBits(context.weight) <= MaxLeafWeight(ULeafBits(context.weight), e.LeafBits(context.weight))
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Remove(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == UCardinality1()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures R.Size(context.weight) <= Size(context.weight)
    ensures R.USize(context.weight) == USize(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality1() <= UCardinality1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.Size(context.weight) == Size(context.weight) && R.USize(context.weight) == Size(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, weight:T -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: (child => MaxLeafBits_set(child, weight))(item) <= bits
    ensures ULeafBits(weight) <= bits
  {
    max_leaf_bits_bound_set(Universe(), child => MaxLeafBits_set(child, weight), bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, weight:T -> nat)
    requires UVolume() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USize(weight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(weight), volume, bits);
  }

  lemma universe_within_bound(U:SetSet<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures Volume1() <= UVolume1() <= U.Volume1() <= U.UVolume1()
    ensures Size(context.weight) <= USize(context.weight) <= U.Size(context.weight) <= U.USize(context.weight)
    ensures LeafBits(context.weight) <= ULeafBits(context.weight) <= U.LeafBits(context.weight) <= U.ULeafBits(context.weight)
  {
    representation_subset_setset(Universe(), U.Model(), context.weight);
    reveal UCardinality1();
    subset_cardinality_bound_set(Universe(), U.Model());
    max_by_monotonic(Universe(), U.Model(), item => |item|);
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinality1(), U.Cardinality(), 1 + U.Cardinality1());
  }

  lemma u_volume_bound(count:nat, member:nat)
    requires UCardinality() <= count && UCardinality1() <= member
    ensures UVolume() <= count*(1+member)
  {
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinality1(), count, 1 + member);
  }

  lemma u_cardinality1_bound(bound:nat)
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
    Volume() <= UVolume() &&
    Volume1() <= UVolume1() &&
    Volume2() <= UVolume2()
  }

  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }
  ghost function Cardinality2():nat { MaxMemberCardinality_setset(Model()) }
  ghost function {:opaque} UCardinality2():nat { MaxMemberCardinality_setset(Universe()) }

  ghost function Volume():nat { Cardinality() * (1 + Volume1()) }
  ghost function UVolume():nat { UCardinality() * (1 + UVolume1()) }
  ghost function Volume1():nat { Cardinality1() * (1 + Cardinality2()) }
  ghost function UVolume1():nat { UCardinality1() * (1 + UCardinality2()) }
  ghost function Volume2():nat { Cardinality2() }
  ghost function UVolume2():nat { UCardinality2() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(weight))
    ensures Volume() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size && Cardinality1() <= size && Cardinality2() <= size
    ensures Volume1() <= size && Volume2() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(weight)
  {
    assert Cardinality2() <= Volume1();
    assert Volume1() <= Volume();
    representation_subset_setsetset(Model(), Universe(), weight, Valid());
    RepresentationSize_setsetset(Model(), weight)
  }

  ghost function USize(weight:T -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(weight))
    ensures UVolume() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size && UCardinality1() <= size && UCardinality2() <= size
    ensures UVolume1() <= size && UVolume2() <= size
    ensures 1 <= size
  {
    reveal UCardinality1(), UCardinality2();
    RepresentationSize_setsetset(Universe(), weight)
  }

  ghost function LeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(weight)
  {
    representation_subset_setsetset(Model(), Universe(), weight, Valid());
    MaxLeafBits_setsetset(Model(), weight)
  }
  ghost function ULeafBits(weight:T -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_setsetset(Universe(), weight) }

  ghost function Cost(work:nat, operandSize:nat, context:SetContext<T>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.weight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method IsEmpty(ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Count(ghost counter_in:nat, ghost context:SetContext<T>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Pick(ghost counter_in:nat, ghost context:SetContext<T>) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Cardinality() <= UCardinality1() && e.UCardinality() <= UCardinality1()
    ensures e.Cardinality1() <= UCardinality2() && e.UCardinality1() <= UCardinality2()
    ensures e.Volume() <= UVolume1()
    ensures e.UVolume() <= UVolume1()
    ensures e.UVolume1() <= UVolume2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures e.USize(context.weight) == e.Size(context.weight)
    ensures e.Size(context.weight) <= Size(context.weight)
    ensures e.ULeafBits(context.weight) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(e.TraversalWork(), 0, context)

  
  method Equal(other:SetSetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.Size(context.weight), context)

  method Contains(e:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Add(e:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.UCardinality1() == (if e.Cardinality() <= UCardinality1() then UCardinality1() else e.Cardinality())
    ensures R.UCardinality2() == (if e.Cardinality1() <= UCardinality2() then UCardinality2() else e.Cardinality1())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures R.ULeafBits(context.weight) <= MaxLeafWeight(ULeafBits(context.weight), e.LeafBits(context.weight))
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Remove(e:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == UCardinality1()
    ensures R.UCardinality2() == UCardinality2()
    ensures R.UVolume1() <= UVolume1()
    ensures R.UVolume2() <= UVolume2()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures R.Size(context.weight) <= Size(context.weight)
    ensures R.USize(context.weight) == USize(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), e.Size(context.weight), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality2() == Cardinality2()
    ensures R.UVolume1() == Volume1()
    ensures R.UVolume2() == Volume2()
    ensures R.UVolume1() <= UVolume1()
    ensures R.UVolume2() <= UVolume2()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.Size(context.weight) == Size(context.weight) && R.USize(context.weight) == Size(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, weight:T -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: (child => MaxLeafBits_setset(child, weight))(item) <= bits
    ensures ULeafBits(weight) <= bits
  {
    max_leaf_bits_bound_set(Universe(), child => MaxLeafBits_setset(child, weight), bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, weight:T -> nat)
    requires UVolume() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USize(weight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(weight), volume, bits);
  }

  lemma universe_within_bound(U:SetSetSet<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures Cardinality2() <= UCardinality2() <= U.Cardinality2() <= U.UCardinality2()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures Volume1() <= UVolume1() <= U.Volume1() <= U.UVolume1()
    ensures Volume2() <= UVolume2() <= U.Volume2() <= U.UVolume2()
    ensures Size(context.weight) <= USize(context.weight) <= U.Size(context.weight) <= U.USize(context.weight)
    ensures LeafBits(context.weight) <= ULeafBits(context.weight) <= U.LeafBits(context.weight) <= U.ULeafBits(context.weight)
  {
    representation_subset_setsetset(Universe(), U.Model(), context.weight);
    reveal UCardinality1(), UCardinality2();
    subset_cardinality_bound_set(Universe(), U.Model());
    max_by_monotonic(Universe(), U.Model(), item => |item|);
    max_by_monotonic(Universe(), U.Model(), item => MaxCardinality_set(item));
    nonnegative_product_monotonic(UCardinality1(), 1 + UCardinality2(), U.Cardinality1(), 1 + U.Cardinality2());
    nonnegative_product_monotonic(UCardinality(), 1 + UVolume1(), U.Cardinality(), 1 + U.Volume1());
  }

  lemma u_volume_bound(count:nat, members:nat, leaves:nat)
    requires UCardinality() <= count && UCardinality1() <= members
    requires UCardinality2() <= leaves
    ensures UVolume() <= count*(1+members*(1+leaves))
    ensures UVolume1() <= members*(1+leaves)
    ensures UVolume2() <= leaves
  {
    nonnegative_product_monotonic(UCardinality1(), 1 + UCardinality2(), members, 1 + leaves);
    nonnegative_product_monotonic(UCardinality(), 1 + UVolume1(), count, 1 + members*(1+leaves));
  }

  lemma u_cardinality1_bound(bound:nat)
    requires forall child | child in Universe() :: |child| <= bound
    ensures UCardinality1() <= bound
  {
    reveal UCardinality1();
    max_by_bound(Universe(), bound, item => |item|);
  }

  lemma u_cardinality2_bound(bound:nat)
    requires forall s | s in Universe() :: MaxCardinality_set(s) <= bound
    ensures UCardinality2() <= bound
  {
    reveal UCardinality2();
    max_by_bound(Universe(), bound, item => MaxCardinality_set(item));
  }

}


// Construction cost for Set, SetSet and SetSetSet, independent of element type
ghost function CostNew_SetFamily():nat
{ CostRepresentation(1, 1, 0) }
