include "Lemmas.dfy"


class ConcreteSet<T(==)> extends Set<T> {
  const elements:set<T>
  ghost const universe:set<T>

  constructor(elements_in:set<T>, ghost universe_in:set<T>)
    requires elements_in <= universe_in
    ensures Valid()
    ensures Model() == elements_in
    ensures Universe() == universe_in
  {
    elements := elements_in;
    universe := universe_in;
    reveal Model();
    SubsetCardinalityBound(elements_in, universe_in);
  }

  function Repr():set<T> { elements }
  ghost function Universe():set<T> { universe }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + CostPick_Set(this)
  {
    reveal Model();
    e :| e in elements;
    counter_out := counter_in + CostPick_Set(this);
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_Set(this)
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty_Set(this);
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Set(this)
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount_Set(this);
  }

  method Equal(other:Set<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_Set(this, other)
    ensures counter_out <= counter_in + UCostEqual_Set(this, other)
  {
    reveal Model(), other.Model();
    equal := elements == other.Repr();
    counter_out := counter_in + CostEqual_Set(this, other);
  }

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + CostContains_Set(this)
    ensures counter_out <= counter_in + UCostContains_Set(this)
  {
    reveal Model();
    b := e in elements;
    counter_out := counter_in + CostContains_Set(this);
  }

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures counter_out == counter_in + CostAdd_Set(this)
    ensures counter_out <= counter_in + UCostAdd_Set(this)
  {
    reveal Model();
    R := new ConcreteSet(elements + {e}, universe + {e});
    if e in elements {
      assert elements + {e} == elements;
    } else {
      assert |elements + {e}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd_Set(this);
  }

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures counter_out == counter_in + CostRemove_Set(this)
    ensures counter_out <= counter_in + UCostRemove_Set(this)
  {
    reveal Model();
    R := new ConcreteSet(elements - {e}, universe);
    counter_out := counter_in + CostRemove_Set(this);
  }

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Set(this)
    ensures counter_out <= counter_in + UCostCopy_Set(this)
  {
    reveal Model();
    R := new ConcreteSet(elements, elements);
    counter_out := counter_in + CostCopy_Set(this);
  }
}


class ConcreteSetSet<T(==)> extends SetSet<T> {
  const elements:set<set<T>>
  ghost const universe:set<set<T>>

  constructor(elements_in:set<set<T>>, ghost universe_in:set<set<T>>)
    requires elements_in <= universe_in
    ensures Valid()
    ensures Model() == elements_in
    ensures Universe() == universe_in
  {
    elements := elements_in;
    universe := universe_in;
    reveal Model(), USize1();
    MaxCardinalityProperties_set(universe_in);
    SubsetCardinalityBound(elements_in, universe_in);
  }

  function Repr():set<set<T>> { elements }
  ghost function Universe():set<set<T>> { universe }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Size0() <= USize1()
    ensures e.USize0() <= USize1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick_SetSet(this, e)
    ensures counter_out <= counter_in + UCostPick_SetSet(this)
  {
    reveal Model();
    var chosen:set<T> :| chosen in elements;
    e := new ConcreteSet(chosen, chosen);
    counter_out := counter_in + CostPick_SetSet(this, e);
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_SetSet(this)
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty_SetSet(this);
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_SetSet(this)
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount_SetSet(this);
  }

  method Equal(other:SetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_SetSet(this, other)
    ensures counter_out <= counter_in + UCostEqual_SetSet(this, other)
  {
    ModelSizeBound_SetSet(this);
    ModelSizeBound_SetSet(other);
    reveal Model(), other.Model();
    equal := elements == other.Repr();
    counter_out := counter_in + CostEqual_SetSet(this, other);
  }

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains_SetSet(this)
    ensures counter_out <= counter_in + UCostContains_SetSet(this)
  {
    ModelSizeBound_SetSet(this);
    reveal Model();
    reveal e.Model();
    b := e.Repr() in elements;
    counter_out := counter_in + CostContains_SetSet(this);
  }

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= USize1() then R.USize1() == USize1()
            else R.USize1() == e.Size0()
    ensures (R.USize1() == USize1()) || (R.USize1() == e.Size0())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd_SetSet(this)
    ensures counter_out <= counter_in + UCostAdd_SetSet(this)
  {
    ModelSizeBound_SetSet(this);
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSet(elements + {e.Repr()}, universe + {e.Repr()});
    AddUniverseMeasures_SetSet(this, R, e);
    if e.Repr() in elements {
      assert elements + {e.Repr()} == elements;
    } else {
      assert |elements + {e.Repr()}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd_SetSet(this);
  }

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() <= USize1()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove_SetSet(this)
    ensures counter_out <= counter_in + UCostRemove_SetSet(this)
  {
    ModelSizeBound_SetSet(this);
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSet(elements - {e.Repr()}, universe);
    reveal USize1(), R.USize1();
    counter_out := counter_in + CostRemove_SetSet(this);
  }

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() == Size1()
    ensures R.USize1() <= USize1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_SetSet(this)
    ensures counter_out <= counter_in + UCostCopy_SetSet(this)
  {
    ModelSizeBound_SetSet(this);
    reveal Model();
    R := new ConcreteSetSet(elements, elements);
    reveal R.USize1();
    counter_out := counter_in + CostCopy_SetSet(this);
  }
}


class ConcreteSetSetSet<T(==)> extends SetSetSet<T> {
  const elements:set<set<set<T>>>
  ghost const universe:set<set<set<T>>>

  constructor(elements_in:set<set<set<T>>>, ghost universe_in:set<set<set<T>>>)
    requires elements_in <= universe_in
    ensures Valid()
    ensures Model() == elements_in
    ensures Universe() == universe_in
  {
    elements := elements_in;
    universe := universe_in;
    reveal Model(), USize1(), USize2();
    forall s | s in universe_in
      ensures forall inner | inner in s :: |s|*|inner| <= MaxSize_setset(universe_in) && |inner| <= MaxMemberCardinality_setset(universe_in)
    {
      MaxSizeMember_setset(universe_in, s);
      MaxMemberCardinalityMember_setset(universe_in, s);
      forall inner | inner in s
        ensures |s|*|inner| <= MaxSize_setset(universe_in) && |inner| <= MaxMemberCardinality_setset(universe_in)
      {
        MaxCardinalityMember_set(s, inner);
        NatMultiplicationMonotonic(|s|, |inner|, MaxCardinality_set(s));
      }
    }
    SubsetCardinalityBound(elements_in, universe_in);
  }

  function Repr():set<set<set<T>>> { elements }
  ghost function Universe():set<set<set<T>>> { universe }

  method {:isolate_assertions} Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Size0() <= USize1()
    ensures e.USize0() <= USize1()
    ensures e.USize1() <= USize2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick_SetSetSet(this, e)
    ensures counter_out <= counter_in + UCostPick_SetSetSet(this)
  {
    reveal Model();
    var chosen:set<set<T>> :| chosen in elements;
    reveal USize1(), USize2();
    MaxSizeMember_setset(universe, chosen);
    MaxMemberCardinalityMember_setset(universe, chosen);
    e := new ConcreteSetSet(chosen, chosen);
    reveal e.USize1();
    counter_out := counter_in + CostPick_SetSetSet(this, e);
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_SetSetSet(this)
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty_SetSetSet(this);
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_SetSetSet(this)
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount_SetSetSet(this);
  }

  method Equal(other:SetSetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_SetSetSet(this, other)
    ensures counter_out <= counter_in + UCostEqual_SetSetSet(this, other)
  {
    ModelSizeBound_SetSetSet(this);
    ModelSizeBound_SetSetSet(other);
    reveal Model(), other.Model();
    equal := elements == other.Repr();
    counter_out := counter_in + CostEqual_SetSetSet(this, other);
  }

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains_SetSetSet(this)
    ensures counter_out <= counter_in + UCostContains_SetSetSet(this)
  {
    ModelSizeBound_SetSetSet(this);
    reveal Model();
    reveal e.Model();
    b := e.Repr() in elements;
    counter_out := counter_in + CostContains_SetSetSet(this);
  }

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= USize1() then R.USize1() == USize1()
            else R.USize1() == e.Size0()
    ensures if e.Size1() <= USize2() then R.USize2() == USize2()
            else R.USize2() == e.Size1()
    ensures ((R.USize1() == USize1()) || (R.USize1() == e.Size0())) &&
            ((R.USize2() == USize2()) || (R.USize2() == e.Size1()))
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd_SetSetSet(this)
    ensures counter_out <= counter_in + UCostAdd_SetSetSet(this)
  {
    ModelSizeBound_SetSetSet(this);
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSetSet(elements + {e.Repr()}, universe + {e.Repr()});
    AddUniverseMeasures_SetSetSet(this, R, e);
    if e.Repr() in elements {
      assert elements + {e.Repr()} == elements;
    } else {
      assert |elements + {e.Repr()}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd_SetSetSet(this);
  }

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove_SetSetSet(this)
    ensures counter_out <= counter_in + UCostRemove_SetSetSet(this)
  {
    ModelSizeBound_SetSetSet(this);
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSetSet(elements - {e.Repr()}, universe);
    reveal USize1(), USize2(), R.USize1(), R.USize2();
    counter_out := counter_in + CostRemove_SetSetSet(this);
  }

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() == Size1()
    ensures R.USize2() == Size2()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_SetSetSet(this)
    ensures counter_out <= counter_in + UCostCopy_SetSetSet(this)
  {
    ModelSizeBound_SetSetSet(this);
    reveal Model();
    R := new ConcreteSetSetSet(elements, elements);
    reveal R.USize1(), R.USize2();
    counter_out := counter_in + CostCopy_SetSetSet(this);
  }
}


method New_Set<T(==)>(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_Set()
{
  R := new ConcreteSet({}, {});
  counter_out := counter_in + CostNew_Set();
}

method New_SetSet<T(==)>(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures R.USize1() == 0
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_SetSet()
{
  R := new ConcreteSetSet({}, {});
  reveal R.USize1();
  counter_out := counter_in + CostNew_SetSet();
}

method New_SetSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures R.USize1() == 0 && R.USize2() == 0
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_SetSetSet()
{
  R := new ConcreteSetSetSet({}, {});
  reveal R.USize1(), R.USize2();
  counter_out := counter_in + CostNew_SetSetSet();
}

method NewWithUniverse_Set<T(==)>(ghost U:set<T>, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_Set()
{
  R := new ConcreteSet({}, U);
  counter_out := counter_in + CostNew_Set();
}

method NewWithUniverse_SetSet<T(==)>(ghost U:set<set<T>>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_SetSet()
{
  R := new ConcreteSetSet({}, U);
  counter_out := counter_in + CostNew_SetSet();
}

method NewWithUniverse_SetSetSet<T(==)>(ghost U:set<set<set<T>>>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_SetSetSet()
{
  R := new ConcreteSetSetSet({}, U);
  counter_out := counter_in + CostNew_SetSetSet();
}
