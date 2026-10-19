include "../Lemmas/Lemmas.dfy"


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
    subset_cardinality_bound(elements_in, universe_in);
  }

  function ExecutableModel():set<T> { elements }
  ghost function Universe():set<T> { universe }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + CostPick()
  {
    reveal Model();
    e :| e in elements;
    counter_out := counter_in + CostPick();
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty();
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount();
  }

  method Equal(other:Set<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)
  {
    reveal Model(), other.Model();
    equal := elements == other.ExecutableModel();
    counter_out := counter_in + CostEqual(other);
  }

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()
  {
    reveal Model();
    b := e in elements;
    counter_out := counter_in + CostContains();
  }

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures counter_out == counter_in + CostAdd()
    ensures counter_out <= counter_in + UCostAdd()
  {
    reveal Model();
    R := new ConcreteSet(elements + {e}, universe + {e});
    if e in elements {
      assert elements + {e} == elements;
    } else {
      assert |elements + {e}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd();
  }

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()
  {
    reveal Model();
    R := new ConcreteSet(elements - {e}, universe);
    counter_out := counter_in + CostRemove();
  }

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    R := new ConcreteSet(elements, elements);
    counter_out := counter_in + CostCopy();
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
    reveal Model();
    subset_cardinality_bound(elements_in, universe_in);
    reveal UCardinality1();
    max_by_monotonic(elements_in, universe_in, item => |item|);
    nonnegative_product_monotonic(|elements_in|, MaxCardinality_set(elements_in), |universe_in|, MaxCardinality_set(universe_in));
  }

  function ExecutableModel():set<set<T>> { elements }
  ghost function Universe():set<set<T>> { universe }

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
  {
    reveal Model();
    var chosen:set<T> :| chosen in elements;
    reveal UCardinality1();
    max_by_member(universe, chosen, item => |item|);
    e := new ConcreteSet(chosen, chosen);
    counter_out := counter_in + CostPick(e);
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty();
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount();
  }

  method Equal(other:SetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)
  {
    reveal Model(), other.Model();
    equal := elements == other.ExecutableModel();
    counter_out := counter_in + CostEqual(other);
  }

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()
  {
    reveal Model();
    reveal e.Model();
    b := e.ExecutableModel() in elements;
    counter_out := counter_in + CostContains();
  }

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
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSet(elements + {e.ExecutableModel()}, universe + {e.ExecutableModel()});
    add_universe_measures_set_set(this, R, e);
    if e.ExecutableModel() in elements {
      assert elements + {e.ExecutableModel()} == elements;
    } else {
      assert |elements + {e.ExecutableModel()}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd();
  }

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
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSet(elements - {e.ExecutableModel()}, universe);
    reveal UCardinality1(), R.UCardinality1();
    counter_out := counter_in + CostRemove();
  }

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.UCardinality1() == Cardinality1()
    ensures R.UCardinality1() <= UCardinality1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    R := new ConcreteSetSet(elements, elements);
    reveal R.UCardinality1();
    counter_out := counter_in + CostCopy();
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
    reveal Model();
    subset_cardinality_bound(elements_in, universe_in);
    reveal UCardinality1(), UCardinality2();
    max_by_monotonic(elements_in, universe_in, item => |item|);
    max_by_monotonic(elements_in, universe_in, item => MaxCardinality_set(item));
    nonnegative_product_monotonic(MaxCardinality_set(elements_in), MaxMemberCardinality_setset(elements_in), MaxCardinality_set(universe_in), MaxMemberCardinality_setset(universe_in));
    nonnegative_product_monotonic(|elements_in|, MaxCardinality_set(elements_in) * MaxMemberCardinality_setset(elements_in), |universe_in|, MaxCardinality_set(universe_in) * MaxMemberCardinality_setset(universe_in));
  }

  function ExecutableModel():set<set<set<T>>> { elements }
  ghost function Universe():set<set<set<T>>> { universe }

  method {:isolate_assertions} Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
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
  {
    reveal Model();
    var chosen:set<set<T>> :| chosen in elements;
    reveal UCardinality1(), UCardinality2();
    max_by_member(universe, chosen, item => |item|);
    max_by_member(universe, chosen, item => MaxCardinality_set(item));
    nonnegative_product_monotonic(|chosen|, MaxCardinality_set(chosen), UCardinality1(), UCardinality2());
    e := new ConcreteSetSet(chosen, chosen);
    reveal e.UCardinality1();
    counter_out := counter_in + CostPick(e);
  }

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + CostIsEmpty();
  }

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + CostCount();
  }

  method Equal(other:SetSetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual(other)
    ensures counter_out <= counter_in + UCostEqual(other)
  {
    reveal Model(), other.Model();
    equal := elements == other.ExecutableModel();
    counter_out := counter_in + CostEqual(other);
  }

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains()
    ensures counter_out <= counter_in + UCostContains()
  {
    reveal Model();
    reveal e.Model();
    b := e.ExecutableModel() in elements;
    counter_out := counter_in + CostContains();
  }

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
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSetSet(elements + {e.ExecutableModel()}, universe + {e.ExecutableModel()});
    add_universe_measures_set_set_set(this, R, e);
    if e.ExecutableModel() in elements {
      assert elements + {e.ExecutableModel()} == elements;
    } else {
      assert |elements + {e.ExecutableModel()}| == |elements| + 1;
    }
    counter_out := counter_in + CostAdd();
  }

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
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSetSet(elements - {e.ExecutableModel()}, universe);
    reveal UCardinality1(), UCardinality2(), R.UCardinality1(), R.UCardinality2();
    counter_out := counter_in + CostRemove();
  }

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
  {
    reveal Model();
    R := new ConcreteSetSetSet(elements, elements);
    reveal R.UCardinality1(), R.UCardinality2();
    counter_out := counter_in + CostCopy();
  }
}


method New_Set<T(==)>(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSet({}, {});
  counter_out := counter_in + CostNew_SetFamily();
}

method New_SetSet<T(==)>(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures R.UCardinality1() == 0
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSetSet({}, {});
  reveal R.UCardinality1();
  counter_out := counter_in + CostNew_SetFamily();
}

method New_SetSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures R.UCardinality1() == 0 && R.UCardinality2() == 0
  ensures R.USize1() == 0 && R.USize2() == 0
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == {}
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSetSetSet({}, {});
  reveal R.UCardinality1(), R.UCardinality2();
  counter_out := counter_in + CostNew_SetFamily();
}

method NewWithUniverse_Set<T(==)>(ghost U:set<T>, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSet({}, U);
  counter_out := counter_in + CostNew_SetFamily();
}

method NewWithUniverse_SetSet<T(==)>(ghost U:set<set<T>>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSetSet({}, U);
  counter_out := counter_in + CostNew_SetFamily();
}

method NewWithUniverse_SetSetSet<T(==)>(ghost U:set<set<set<T>>>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures R.Valid()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures counter_out == counter_in + CostNew_SetFamily()
{
  R := new ConcreteSetSetSet({}, U);
  counter_out := counter_in + CostNew_SetFamily();
}
