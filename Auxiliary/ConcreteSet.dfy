include "Lemmas.dfy"


class ConcreteSet<T(==)> extends Set<T> {
  const elements:set<T>
  ghost const universe:set<T>

  constructor(elements_in:set<T>, ghost universe_in:set<T>)
    requires elements_in <= universe_in
    ensures Model() == elements_in
    ensures Universe() == universe_in
    ensures Valid()
  {
    elements := elements_in;
    universe := universe_in;
    reveal Model();
    set_subset_cardinality(elements_in, universe_in);
  }

  function Repr():set<T> { elements }
  ghost function Universe():set<T> { universe }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + cost_Pick(0)
  {
    reveal Model();
    e :| e in elements;
    counter_out := counter_in + cost_Pick(0);
  }

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + cost_Empty();
  }

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + cost_nElements();
  }

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())
  {
    reveal Model();
    b := e in elements;
    counter_out := counter_in + cost_Contains(UBSize0());
  }

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + cost_Add(UBSize0())
  {
    reveal Model();
    R := new ConcreteSet(elements + {e}, universe + {e});
    if e in elements {
      assert elements + {e} == elements;
    } else {
      assert |elements + {e}| == |elements| + 1;
    }
    counter_out := counter_in + cost_Add(UBSize0());
  }

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())
  {
    reveal Model();
    R := new ConcreteSet(elements - {e}, universe);
    counter_out := counter_in + cost_Remove(UBSize0());
  }

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
  {
    reveal Model();
    R := new ConcreteSet(elements, elements);
    counter_out := counter_in + cost_Copy(UBSize0());
  }
}


class ConcreteSetSet<T(==)> extends SetSet<T> {
  const elements:set<set<T>>
  ghost const universe:set<set<T>>
  ghost const ub_size1:nat

  constructor(elements_in:set<set<T>>, ghost universe_in:set<set<T>>, ghost ub_size1_in:nat)
    requires elements_in <= universe_in
    requires forall s | s in universe_in :: |s| <= ub_size1_in
    ensures Model() == elements_in
    ensures Universe() == universe_in
    ensures UBSize1() == ub_size1_in
    ensures Valid()
  {
    elements := elements_in;
    universe := universe_in;
    ub_size1 := ub_size1_in;
    reveal Model();
    set_subset_cardinality(elements_in, universe_in);
  }

  function Repr():set<set<T>> { elements }
  ghost function Universe():set<set<T>> { universe }
  ghost function UBSize1():nat { ub_size1 }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.UBSize0() <= UBSize1()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + cost_Pick(UBSize1())
  {
    reveal Model();
    var chosen:set<T> :| chosen in elements;
    e := new ConcreteSet(chosen, chosen);
    counter_out := counter_in + cost_Pick(UBSize1());
  }

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + cost_Empty();
  }

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + cost_nElements();
  }

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    b := e.Repr() in elements;
    counter_out := counter_in + cost_Contains(UBSize0());
  }

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.UBSize0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.UBSize0()
    ensures (R.UBSize1() == UBSize1()) || (R.UBSize1() == e.UBSize0())
    ensures counter_out == counter_in + cost_Add(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    ghost var new_ub_size1 := if e.UBSize0() <= UBSize1() then UBSize1() else e.UBSize0();
    assert forall s | s in universe + {e.Repr()} :: |s| <= new_ub_size1;
    R := new ConcreteSetSet(elements + {e.Repr()}, universe + {e.Repr()}, new_ub_size1);
    if e.Repr() in elements {
      assert elements + {e.Repr()} == elements;
    } else {
      assert |elements + {e.Repr()}| == |elements| + 1;
    }
    counter_out := counter_in + cost_Add(UBSize0());
  }

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSet(elements - {e.Repr()}, universe, UBSize1());
    counter_out := counter_in + cost_Remove(UBSize0());
  }

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
  {
    reveal Model();
    R := new ConcreteSetSet(elements, elements, UBSize1());
    counter_out := counter_in + cost_Copy(UBSize0());
  }
}


class ConcreteSetSetSet<T(==)> extends SetSetSet<T> {
  const elements:set<set<set<T>>>
  ghost const universe:set<set<set<T>>>
  ghost const ub_size1:nat
  ghost const ub_size2:nat

  constructor(elements_in:set<set<set<T>>>, ghost universe_in:set<set<set<T>>>, ghost ub_size1_in:nat, ghost ub_size2_in:nat)
    requires elements_in <= universe_in
    requires forall s | s in universe_in :: forall s' | s' in s :: |s|*|s'| <= ub_size1_in
    requires forall s | s in universe_in :: forall s' | s' in s :: |s'| <= ub_size2_in
    ensures Model() == elements_in
    ensures Universe() == universe_in
    ensures UBSize1() == ub_size1_in
    ensures UBSize2() == ub_size2_in
    ensures Valid()
  {
    elements := elements_in;
    universe := universe_in;
    ub_size1 := ub_size1_in;
    ub_size2 := ub_size2_in;
    reveal Model();
    set_subset_cardinality(elements_in, universe_in);
  }

  function Repr():set<set<set<T>>> { elements }
  ghost function Universe():set<set<set<T>>> { universe }
  ghost function UBSize1():nat { ub_size1 }
  ghost function UBSize2():nat { ub_size2 }

  method {:isolate_assertions} Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.UBSize0() <= UBSize1()
    ensures e.UBSize1() <= UBSize2()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + cost_Pick(UBSize1())
  {
    reveal Model();
    var chosen:set<set<T>> :| chosen in elements;
    ghost var quotient_bound:nat := if |chosen| == 0 then 0 else UBSize1()/|chosen|;
    ghost var chosen_ub_size1:nat := if quotient_bound <= UBSize2() then quotient_bound else UBSize2();
    if chosen != {} {
      assert 0 < |chosen|;
      forall inner | inner in chosen
        ensures |inner| <= quotient_bound
      {
        quotient_upper_bound(|chosen|, |inner|, UBSize1());
      }
      nat_mult_mono(|chosen|, chosen_ub_size1, quotient_bound);
      assert UBSize1() == |chosen|*quotient_bound + UBSize1()%|chosen|;
      assert |chosen|*quotient_bound <= UBSize1();
    } else {
      assert |chosen| == 0;
    }
    assert forall inner | inner in chosen :: |inner| <= chosen_ub_size1;
    assert |chosen|*chosen_ub_size1 <= UBSize1();
    e := new ConcreteSetSet(chosen, chosen, chosen_ub_size1);
    counter_out := counter_in + cost_Pick(UBSize1());
  }

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()
  {
    reveal Model();
    b := elements == {};
    counter_out := counter_in + cost_Empty();
  }

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()
  {
    reveal Model();
    size := |elements|;
    counter_out := counter_in + cost_nElements();
  }

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    b := e.Repr() in elements;
    counter_out := counter_in + cost_Contains(UBSize0());
  }

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.UBSize0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.UBSize0()
    ensures if e.UBSize1() <= UBSize2() then R.UBSize2() == UBSize2()
            else R.UBSize2() == e.UBSize1()
    ensures ((R.UBSize1() == UBSize1()) || (R.UBSize1() == e.UBSize0())) &&
            ((R.UBSize2() == UBSize2()) || (R.UBSize2() == e.UBSize1()))
    ensures counter_out == counter_in + cost_Add(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    ghost var new_ub_size1 := if e.UBSize0() <= UBSize1() then UBSize1() else e.UBSize0();
    ghost var new_ub_size2 := if e.UBSize1() <= UBSize2() then UBSize2() else e.UBSize1();
    forall s | s in universe + {e.Repr()}
      ensures forall inner | inner in s :: |s|*|inner| <= new_ub_size1
      ensures forall inner | inner in s :: |inner| <= new_ub_size2
    {
      if s !in universe {
        assert s == e.Repr();
        forall inner | inner in s
          ensures |s|*|inner| <= new_ub_size1
          ensures |inner| <= new_ub_size2
        {
          assert inner in e.Universe();
          nat_mult_mono(|s|, |inner|, e.UBSize1());
          assert |s|*e.UBSize1() == e.UBSize0();
        }
      }
    }
    R := new ConcreteSetSetSet(elements + {e.Repr()}, universe + {e.Repr()}, new_ub_size1, new_ub_size2);
    if e.Repr() in elements {
      assert elements + {e.Repr()} == elements;
    } else {
      assert |elements + {e.Repr()}| == |elements| + 1;
    }
    counter_out := counter_in + cost_Add(UBSize0());
  }

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.UBSize2() <= UBSize2()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())
  {
    reveal Model();
    reveal e.Model();
    R := new ConcreteSetSetSet(elements - {e.Repr()}, universe, UBSize1(), UBSize2());
    counter_out := counter_in + cost_Remove(UBSize0());
  }

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures R.UBSize2() == UBSize2()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
  {
    reveal Model();
    R := new ConcreteSetSetSet(elements, elements, UBSize1(), UBSize2());
    counter_out := counter_in + cost_Copy(UBSize0());
  }
}


method New_Set<T(==)>(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Valid()
{
  R := new ConcreteSet({}, {});
  counter_out := counter_in + cost_New();
}

method New_SetSet<T(==)>(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Valid()
{
  R := new ConcreteSetSet({}, {}, 0);
  counter_out := counter_in + cost_New();
}

method New_SetSetSet<T(==)>(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Valid()
{
  R := new ConcreteSetSetSet({}, {}, 0, 0);
  counter_out := counter_in + cost_New();
}

method New_Set_params<T(==)>(ghost U:set<T>, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.Valid()
{
  R := new ConcreteSet({}, U);
  counter_out := counter_in + cost_New();
}

method New_SetSet_params<T(==)>(ghost U:set<set<T>>, ghost UBSize1:nat, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
  requires forall u | u in U :: |u| <= UBSize1
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.UBSize1() == UBSize1
  ensures R.Valid()
{
  R := new ConcreteSetSet({}, U, UBSize1);
  counter_out := counter_in + cost_New();
}

method New_SetSetSet_params<T(==)>(ghost U:set<set<set<T>>>, ghost UBSize1:nat, ghost UBSize2:nat, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
  requires forall u | u in U :: |u|*UBSize2 <= UBSize1
  requires forall u | u in U :: forall u' | u' in u :: |u'| <= UBSize2
  ensures counter_out == counter_in + cost_New()
  ensures R.Model() == {}
  ensures R.Universe() == U
  ensures R.UBSize1() == UBSize1
  ensures R.UBSize2() == UBSize2
  ensures R.Valid()
{
  forall outer | outer in U
    ensures forall inner | inner in outer :: |outer|*|inner| <= UBSize1
  {
    forall inner | inner in outer
      ensures |outer|*|inner| <= UBSize1
    {
      nat_mult_mono(|outer|, |inner|, UBSize2);
    }
  }
  R := new ConcreteSetSetSet({}, U, UBSize1, UBSize2);
  counter_out := counter_in + cost_New();
}
