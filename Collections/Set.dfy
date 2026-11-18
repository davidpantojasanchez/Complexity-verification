include "../Foundations/CollectionLaws.dfy"
include "../Foundations/RepresentationCosts.dfy"
include "../Foundations/CollectionRepresentation.dfy"
include "../Foundations/RepresentationBounds.dfy"
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

  ghost function VolumeBound():nat
  ghost function UVolumeBound():nat

  ghost predicate Init() {
    Valid() && Model() == Universe()
  }

  ghost predicate UniverseWithin(reference:SetFamily<E>) {
    Valid() && reference.Valid() && Universe() <= reference.Model()
  }

  // Structural work factors used by the common cost calculation.
  ghost function CombinedTraversalWork(other:SetFamily<E>):nat { VolumeBound() + other.VolumeBound() + 1 }
  ghost function TraversalWork():nat { VolumeBound() + 1 }

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
    VolumeBound() <= UVolumeBound()
  }
  
  ghost function VolumeBound():nat { Cardinality() }
  ghost function UVolumeBound():nat { UCardinality() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures 1+Cardinality() <= size
    ensures LeafBits(weight) <= size
    ensures size <= SizeBound(weight) <= 4*NatPower(size+1, 2)
  {
    representation_bound_set(Model(), weight);
    size_properties_set(Model(), weight);
    Size_set(Model(), weight)
  }

  ghost function SizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(VolumeBound(), LeafBits(weight))
    ensures VolumeBound() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USizeBound(weight)
  {
    representation_bound_set(Model(), weight);
    representation_subset_set(Model(), Universe(), weight, Valid());
    RepresentationSizeBound_set(Model(), weight)
  }

  ghost function USizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(UVolumeBound(), ULeafBits(weight))
    ensures UVolumeBound() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size
    ensures 1 <= size
  {
    RepresentationSizeBound_set(Universe(), weight)
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
      (work <= context.bound+1 && SizeBound(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := SizeBound(context.weight);
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
    ensures context.weight(e) <= SizeBound(context.weight)
    ensures context.weight(e) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Equal(other:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.SizeBound(context.weight), context)

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
    ensures R.SizeBound(context.weight) <= SizeBound(context.weight)
    ensures R.USizeBound(context.weight) == USizeBound(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), context.weight(e), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.SizeBound(context.weight) == SizeBound(context.weight) && R.USizeBound(context.weight) == SizeBound(context.weight)
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
    requires UVolumeBound() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USizeBound(weight) <= RepresentationSizeBound(volume, bits)
  {
    representation_size_bound_monotonic(UVolumeBound(), ULeafBits(weight), volume, bits);
  }


  lemma universe_within_bound(U:Set<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures VolumeBound() <= UVolumeBound() <= U.VolumeBound() <= U.UVolumeBound()
    ensures SizeBound(context.weight) <= USizeBound(context.weight) <= U.SizeBound(context.weight) <= U.USizeBound(context.weight)
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
    VolumeBound() <= UVolumeBound() &&
    VolumeBound1() <= UVolumeBound1()
  }

  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }

  ghost function VolumeBound():nat { Cardinality() * (1 + Cardinality1()) }
  ghost function UVolumeBound():nat { UCardinality() * (1 + UCardinality1()) }
  ghost function VolumeBound1():nat { Cardinality1() }
  ghost function UVolumeBound1():nat { UCardinality1() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures 1+Cardinality() <= size
    ensures LeafBits(weight) <= size
    ensures size <= SizeBound(weight) <= 7*NatPower(size+1, 3)
  {
    var memberSize := (member:set<T>) => Size_set(member, weight);
    representation_bound_setset(Model(), weight);
    size_properties_set(Model(), memberSize);
    Size_set(Model(), memberSize)
  }

  ghost function SizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(VolumeBound(), LeafBits(weight))
    ensures VolumeBound() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size && Cardinality1() <= size
    ensures VolumeBound1() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USizeBound(weight)
  {
    representation_bound_setset(Model(), weight);
    representation_subset_setset(Model(), Universe(), weight, Valid());
    RepresentationSizeBound_setset(Model(), weight)
  }

  ghost function USizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(UVolumeBound(), ULeafBits(weight))
    ensures UVolumeBound() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size && UCardinality1() <= size
    ensures UVolumeBound1() <= size
    ensures 1 <= size
  {
    reveal UCardinality1();
    RepresentationSizeBound_setset(Universe(), weight)
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
      (work <= context.bound+1 && SizeBound(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := SizeBound(context.weight);
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
    ensures e.VolumeBound() <= UCardinality1()
    ensures e.UVolumeBound() <= UCardinality1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures e.USizeBound(context.weight) == e.SizeBound(context.weight)
    ensures e.SizeBound(context.weight) <= SizeBound(context.weight)
    ensures e.ULeafBits(context.weight) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(e.TraversalWork(), 0, context)

  method Equal(other:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.SizeBound(context.weight), context)

  method Contains(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

  method Add(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.UCardinality1() == (if e.Cardinality() <= UCardinality1() then UCardinality1() else e.Cardinality())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures R.ULeafBits(context.weight) <= MaxLeafWeight(ULeafBits(context.weight), e.LeafBits(context.weight))
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

  method Remove(e:Set<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == UCardinality1()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures R.SizeBound(context.weight) <= SizeBound(context.weight)
    ensures R.USizeBound(context.weight) == USizeBound(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality1() <= UCardinality1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.SizeBound(context.weight) == SizeBound(context.weight) && R.USizeBound(context.weight) == SizeBound(context.weight)
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
    requires UVolumeBound() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USizeBound(weight) <= RepresentationSizeBound(volume, bits)
  {
    representation_size_bound_monotonic(UVolumeBound(), ULeafBits(weight), volume, bits);
  }

  lemma universe_within_bound(U:SetSet<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures VolumeBound() <= UVolumeBound() <= U.VolumeBound() <= U.UVolumeBound()
    ensures VolumeBound1() <= UVolumeBound1() <= U.VolumeBound1() <= U.UVolumeBound1()
    ensures SizeBound(context.weight) <= USizeBound(context.weight) <= U.SizeBound(context.weight) <= U.USizeBound(context.weight)
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
    ensures UVolumeBound() <= count*(1+member)
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
    VolumeBound() <= UVolumeBound() &&
    VolumeBound1() <= UVolumeBound1() &&
    VolumeBound2() <= UVolumeBound2()
  }

  ghost function Cardinality1():nat { MaxCardinality_set(Model()) }
  ghost function {:opaque} UCardinality1():nat { MaxCardinality_set(Universe()) }
  ghost function Cardinality2():nat { MaxMemberCardinality_setset(Model()) }
  ghost function {:opaque} UCardinality2():nat { MaxMemberCardinality_setset(Universe()) }

  ghost function VolumeBound():nat { Cardinality() * (1 + VolumeBound1()) }
  ghost function UVolumeBound():nat { UCardinality() * (1 + UVolumeBound1()) }
  ghost function VolumeBound1():nat { Cardinality1() * (1 + Cardinality2()) }
  ghost function UVolumeBound1():nat { UCardinality1() * (1 + UCardinality2()) }
  ghost function VolumeBound2():nat { Cardinality2() }
  ghost function UVolumeBound2():nat { UCardinality2() }

  ghost function Size(weight:T -> nat):(size:nat)
    ensures 1+Cardinality() <= size
    ensures size <= SizeBound(weight) <= 10*NatPower(size+1, 4)
  {
    var memberSize := (sets:set<set<T>>) => Size_set(sets, member => Size_set(member, weight));
    representation_bound_setsetset(Model(), weight);
    size_properties_set(Model(), memberSize);
    Size_set(Model(), memberSize)
  }

  ghost function SizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(VolumeBound(), LeafBits(weight))
    ensures VolumeBound() <= size && LeafBits(weight) <= size
    ensures Cardinality() <= size && Cardinality1() <= size && Cardinality2() <= size
    ensures VolumeBound1() <= size && VolumeBound2() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USizeBound(weight)
  {
    assert Cardinality2() <= VolumeBound1();
    assert VolumeBound1() <= VolumeBound();
    representation_bound_setsetset(Model(), weight);
    representation_subset_setsetset(Model(), Universe(), weight, Valid());
    nat_multiplication_monotonic(3*VolumeBound(), 1, LeafBits(weight));
    RepresentationSizeBound_setsetset(Model(), weight)
  }

  ghost function USizeBound(weight:T -> nat):(size:nat)
    ensures size == RepresentationSizeBound(UVolumeBound(), ULeafBits(weight))
    ensures UVolumeBound() <= size && ULeafBits(weight) <= size
    ensures UCardinality() <= size && UCardinality1() <= size && UCardinality2() <= size
    ensures UVolumeBound1() <= size && UVolumeBound2() <= size
    ensures 1 <= size
  {
    reveal UCardinality1(), UCardinality2();
    RepresentationSizeBound_setsetset(Universe(), weight)
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
      (work <= context.bound+1 && SizeBound(context.weight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := SizeBound(context.weight);
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
    ensures e.VolumeBound() <= UVolumeBound1()
    ensures e.UVolumeBound() <= UVolumeBound1()
    ensures e.UVolumeBound1() <= UVolumeBound2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures e.USizeBound(context.weight) == e.SizeBound(context.weight)
    ensures e.SizeBound(context.weight) <= SizeBound(context.weight)
    ensures e.ULeafBits(context.weight) <= LeafBits(context.weight)
    ensures counter_out == counter_in + Cost(e.TraversalWork(), 0, context)

  
  method Equal(other:SetSetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + Cost(CombinedTraversalWork(other), other.SizeBound(context.weight), context)

  method Contains(e:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

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
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

  method Remove(e:SetSet<T>, ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == UCardinality1()
    ensures R.UCardinality2() == UCardinality2()
    ensures R.UVolumeBound1() <= UVolumeBound1()
    ensures R.UVolumeBound2() <= UVolumeBound2()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures R.SizeBound(context.weight) <= SizeBound(context.weight)
    ensures R.USizeBound(context.weight) == USizeBound(context.weight)
    ensures counter_out == counter_in + Cost(TraversalWork(), e.SizeBound(context.weight), context)

  method Copy(ghost counter_in:nat, ghost context:SetContext<T>) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality2() == Cardinality2()
    ensures R.UVolumeBound1() == VolumeBound1()
    ensures R.UVolumeBound2() == VolumeBound2()
    ensures R.UVolumeBound1() <= UVolumeBound1()
    ensures R.UVolumeBound2() <= UVolumeBound2()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.SizeBound(context.weight) == SizeBound(context.weight) && R.USizeBound(context.weight) == SizeBound(context.weight)
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
    requires UVolumeBound() <= volume && ULeafBits(weight) <= bits && 1 <= bits
    ensures USizeBound(weight) <= RepresentationSizeBound(volume, bits)
  {
    representation_size_bound_monotonic(UVolumeBound(), ULeafBits(weight), volume, bits);
  }

  lemma universe_within_bound(U:SetSetSet<T>, context:SetContext<T>)
    requires UniverseWithin(U)
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Cardinality1() <= UCardinality1() <= U.Cardinality1() <= U.UCardinality1()
    ensures Cardinality2() <= UCardinality2() <= U.Cardinality2() <= U.UCardinality2()
    ensures VolumeBound() <= UVolumeBound() <= U.VolumeBound() <= U.UVolumeBound()
    ensures VolumeBound1() <= UVolumeBound1() <= U.VolumeBound1() <= U.UVolumeBound1()
    ensures VolumeBound2() <= UVolumeBound2() <= U.VolumeBound2() <= U.UVolumeBound2()
    ensures SizeBound(context.weight) <= USizeBound(context.weight) <= U.SizeBound(context.weight) <= U.USizeBound(context.weight)
    ensures LeafBits(context.weight) <= ULeafBits(context.weight) <= U.LeafBits(context.weight) <= U.ULeafBits(context.weight)
  {
    representation_subset_setsetset(Universe(), U.Model(), context.weight);
    reveal UCardinality1(), UCardinality2();
    subset_cardinality_bound_set(Universe(), U.Model());
    max_by_monotonic(Universe(), U.Model(), item => |item|);
    max_by_monotonic(Universe(), U.Model(), item => MaxCardinality_set(item));
    nonnegative_product_monotonic(UCardinality1(), 1 + UCardinality2(), U.Cardinality1(), 1 + U.Cardinality2());
    nonnegative_product_monotonic(UCardinality(), 1 + UVolumeBound1(), U.Cardinality(), 1 + U.VolumeBound1());
  }

  lemma u_volume_bound(count:nat, members:nat, leaves:nat)
    requires UCardinality() <= count && UCardinality1() <= members
    requires UCardinality2() <= leaves
    ensures UVolumeBound() <= count*(1+members*(1+leaves))
    ensures UVolumeBound1() <= members*(1+leaves)
    ensures UVolumeBound2() <= leaves
  {
    nonnegative_product_monotonic(UCardinality1(), 1 + UCardinality2(), members, 1 + leaves);
    nonnegative_product_monotonic(UCardinality(), 1 + UVolumeBound1(), count, 1 + members*(1+leaves));
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
