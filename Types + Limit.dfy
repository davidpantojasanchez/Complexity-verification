include "Auxiliary.dfy"

abstract module TypeLimitMod{
  /*type A(==)
  type B(==)
  type C(==)
  type D(==)
  type T(==)*/
  const sizeT:nat := 1  // upper bound
  const upperBound:nat
  //function polynomial() : nat

  predicate bound(counter_in:nat, counter_out:nat) {
    counter_out <= counter_in + upperBound
  }

  type Set<T(==)>{

  ghost function Model():set<T>
  ensures |Model()| <= upperBound

  ghost function Size():(R:nat)
  ensures R <= upperBound
  {|Model()|*sizeT}

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + sizeT
    ensures e in Model()
    ensures bound(counter_in, counter_out)
  
  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Cardinality(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires |Model()| < upperBound
    ensures  R.Model() == Model() + {e}
    ensures if e in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + sizeT
    ensures bound(counter_in, counter_out)

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e}
    ensures if e !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)
  
  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e in Model()) 
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    ensures R.Model() == Model()
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)

  }


  type SetSet<T(==)>{
   ghost function Model():set<set<T>>
   ghost function maximumSizeElements():nat
   ensures forall s | s in Model() :: maximumSizeElements() >= |s|*sizeT
   ensures exists s :: s in Model() && maximumSizeElements() == |s|*sizeT

   ghost function Size():nat
    {|Model()|*maximumSizeElements()}

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + maximumSizeElements()
    ensures e.Model() in Model()
    ensures bound(counter_in, counter_out)

  method Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Cardinality(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + maximumSizeElements()
    ensures bound(counter_in, counter_out)

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)
  
  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e.Model() in Model()) 
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    ensures R.Model() == Model()
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)
  }


  type SetSetSet<T(==)>{
   ghost function Model():set<set<set<T>>>

   ghost function maximumSizeElements():nat
   ensures forall s | s in Model() :: maximumSizeElements() >= |s|*maximumSizeElements'()
   ensures exists s :: s in Model() && maximumSizeElements() == |s|*maximumSizeElements'()

   ghost function maximumSizeElements'():nat
   ensures forall s | s in Model() :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*sizeT)
   ensures exists s | s in Model() :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*sizeT)


   ghost function Size():nat
    {|Model()|*maximumSizeElements()}

  method Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + maximumSizeElements()
    ensures e.Model() in Model()
    ensures bound(counter_in, counter_out)

  method Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Cardinality(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
    ensures bound(counter_in, counter_out)
  
  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + maximumSizeElements()
    ensures bound(counter_in, counter_out)

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)
  
  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e.Model() in Model()) 
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    ensures R.Model() == Model()
    ensures counter_out == counter_in + Size()
    ensures bound(counter_in, counter_out)
  }


  type Map<T0(==), T1(==)>{

  ghost function Model():map<T0, T1>
  ghost function Size():nat
  {|Model()|*sizeT}

  method Get(q:T0, ghost counter_in:nat) returns (a:T1, ghost counter_out:nat)
    requires Model() != map[]
    requires q in Model().Keys
    ensures counter_out == counter_in + sizeT
    ensures a == Model()[q]
    ensures bound(counter_in, counter_out)

  method Add(q:T0, a:T1, ghost counter_in:nat) returns (R:Map<T0, T1>, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + sizeT
    ensures R.Model() == Model()[q := a]
    ensures bound(counter_in, counter_out)

  method Remove(q:T0, ghost counter_in:nat) returns (R:Map<T0, T1>, ghost counter_out:nat)
    requires q in Model().Keys
    ensures counter_out == counter_in + sizeT
    ensures R.Model() == Model() - {q}
    ensures bound(counter_in, counter_out)

  method Keys(ghost counter_in:nat) returns (keys:Set<T0>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Keys
    ensures bound(counter_in, counter_out)

  method Values(ghost counter_in:nat) returns (keys:Set<T1>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Values
    ensures bound(counter_in, counter_out)

  method Items(ghost counter_in:nat) returns (keys:Set<(T0, T1)>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Items
    ensures bound(counter_in, counter_out)

  method HasKey(q:T0, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q in Model().Keys)
    ensures bound(counter_in, counter_out)
  
  /*
  method Restrict(s:set<T0>, ghost counter_in:nat) returns (R:map<T0, T1>, ghost counter_out:nat)
    requires s <= Model().Keys
    ensures counter_out == counter_in + Size()
    ensures R.Keys == s
    ensures forall key:T0 | key in R.Keys :: R[key] == Model()[key]
    ensures forall i:(T0, T1) | i in R.Items :: i in Model().Items              // redundante
  */
  
  }


  type MapMap<T0(==), T1(==), T2(==)>{

  ghost function Model():map<map<T0, T1>, T2>
  ghost function Size():nat
  {|Model()|*maximumSizeElements()}

   ghost function maximumSizeElements():nat
   ensures forall s | s in Model().Keys :: maximumSizeElements() >= |s.Items|*sizeT
   ensures exists s :: s in Model() && maximumSizeElements() == |s.Items|*sizeT

  method Get(q:Map<T0, T1>, ghost counter_in:nat) returns (a:T2, ghost counter_out:nat)
    requires Model() != map[]
    requires q.Model() in Model().Keys
    ensures counter_out == counter_in + maximumSizeElements()
    ensures a == Model()[q.Model()]
    ensures bound(counter_in, counter_out)

  method Add(q:Map<T0, T1>, a:T2, ghost counter_in:nat) returns (R:MapMap<T0, T1, T2>, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + maximumSizeElements()
    ensures R.Model() == Model()[q.Model() := a]
    ensures bound(counter_in, counter_out)
  
  method Remove(q:Map<T0, T1>, ghost counter_in:nat) returns (R:MapMap<T0, T1, T2>, ghost counter_out:nat)
    requires q.Model() in Model().Keys
    ensures counter_out == counter_in + maximumSizeElements()
    ensures R.Model() == Model() - {q.Model()}
    ensures bound(counter_in, counter_out)
    
  method Keys(ghost counter_in:nat) returns (keys:SetMap<T0, T1>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Keys
    ensures bound(counter_in, counter_out)

  method Values(ghost counter_in:nat) returns (keys:Set<T2>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Values
    ensures bound(counter_in, counter_out)

  method Items(ghost counter_in:nat) returns (keys:SetPairMap<T0, T1, T2>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Items
    ensures bound(counter_in, counter_out)

  method HasKey(q:Map<T0, T1>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q.Model() in Model().Keys)
    ensures bound(counter_in, counter_out)

  }
  

  type Map_Map_SetMap<T0(==), T1(==)>{

  ghost function Model():map<map<T0, T1>, set<map<T0, T1>>>
  ghost function Size():nat
  {|Model()|*maximumSizeElements()}

  ghost function maximumSizeElements():nat
  ensures ((maximumSizeElements() >= maximumSizeKeys()) && (maximumSizeElements() == maximumSizeValues())) ||
          ((maximumSizeElements() == maximumSizeKeys()) && (maximumSizeElements() >= maximumSizeValues()))

  ghost function maximumSizeKeys():nat
  ensures forall s | s in Model().Keys :: maximumSizeKeys() >= |s.Items|*sizeT
  ensures exists s :: s in Model() && maximumSizeKeys() == |s.Items|*sizeT

  ghost function maximumSizeValues():nat
  ensures forall setMap | setMap in Model().Values ::
          forall m | m in setMap :: maximumSizeValues() >= |m.Items|*sizeT
  ensures exists setMap | setMap in Model().Values ::
          exists m | m in setMap :: maximumSizeValues() == |m.Items|*sizeT

  method Get(q:Map<T0, T1>, ghost counter_in:nat) returns (a:SetMap<T0, T1>, ghost counter_out:nat)
    requires Model() != map[]
    requires q.Model() in Model().Keys
    ensures counter_out == counter_in + maximumSizeElements()
    ensures a.Model() == Model()[q.Model()]
    ensures bound(counter_in, counter_out)

  method Add(q:Map<T0, T1>, a:SetMap<T0, T1>, ghost counter_in:nat) returns (R:Map_Map_SetMap<T0, T1>, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + maximumSizeElements()
    ensures R.Model() == Model()[q.Model() := a.Model()]
    ensures bound(counter_in, counter_out)
  
  method Remove(q:Map<T0, T1>, ghost counter_in:nat) returns (R:Map_Map_SetMap<T0, T1>, ghost counter_out:nat)
      requires q.Model() in Model().Keys
      ensures counter_out == counter_in + maximumSizeElements()
      ensures R.Model() == Model() - {q.Model()}
    ensures bound(counter_in, counter_out)
    
  method Keys(ghost counter_in:nat) returns (keys:SetMap<T0, T1>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Keys
    ensures bound(counter_in, counter_out)

  method Values(ghost counter_in:nat) returns (keys:SetSetMap<T0, T1>, ghost counter_out:nat)
    ensures counter_out == counter_in + Size()
    ensures keys.Model() == Model().Values
    ensures bound(counter_in, counter_out)

  method HasKey(q:Map<T0, T1>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q.Model() in Model().Keys)
    ensures bound(counter_in, counter_out)

  }
  

  type SetMap<T0(==), T1(==)>{
    ghost function Model():set<map<T0, T1>>

    ghost function Size():nat
    {|Model()|*maximumSizeElements()}

    ghost function maximumSizeElements():nat
    ensures forall s | s in Model() :: maximumSizeElements() >= |s.Items|*sizeT
    ensures exists s :: s in Model() && maximumSizeElements() == |s.Items|*sizeT

    method Pick(ghost counter_in:nat) returns (e:Map<T0, T1>, ghost counter_out:nat)
      requires Model() != {}
      ensures counter_out == counter_in + maximumSizeElements()
      ensures e.Model() in Model()
      ensures bound(counter_in, counter_out)
    
    method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures b == (Model() == {})
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Cardinality(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
      ensures  size == |Model()|
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Add(e:Map<T0, T1>, ghost counter_in:nat) returns (R:SetMap<T0, T1>, ghost counter_out:nat)
      ensures  R.Model() == Model() + {e.Model()}
      ensures if e.Model() in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| + 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Remove(e:Map<T0, T1>, ghost counter_in:nat) returns (R:SetMap<T0, T1>, ghost counter_out:nat)
      ensures  R.Model() == Model() - {e.Model()}
      ensures if e.Model() !in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| - 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)
    
    method Contains(e:Map<T0, T1>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures  b == (e.Model() in Model()) 
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Copy(ghost counter_in:nat) returns (R:SetMap<T0, T1>, ghost counter_out:nat)
      ensures R.Model() == Model()
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

  }


type SetSetMap<T0(==), T1(==)>{
    ghost function Model():set<set<map<T0, T1>>>

    ghost function Size():nat
    {|Model()|*maximumSizeElements()}

    ghost function maximumSizeElements():nat
    // ensures forall s | s in Model() :: maximumSizeElements() >= |s.Items|*sizeT
    //ensures exists s :: s in Model() && maximumSizeElements() == |s.Items|*sizeT

    method Pick(ghost counter_in:nat) returns (e:SetMap<T0, T1>, ghost counter_out:nat)
      requires Model() != {}
      ensures counter_out == counter_in + maximumSizeElements()
      ensures e.Model() in Model()
      ensures bound(counter_in, counter_out)
    
    method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures b == (Model() == {})
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Cardinality(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
      ensures  size == |Model()|
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Add(e:SetMap<T0, T1>, ghost counter_in:nat) returns (R:SetSetMap<T0, T1>, ghost counter_out:nat)
      ensures  R.Model() == Model() + {e.Model()}
      ensures if e.Model() in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| + 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Remove(e:SetMap<T0, T1>, ghost counter_in:nat) returns (R:SetSetMap<T0, T1>, ghost counter_out:nat)
      ensures  R.Model() == Model() - {e.Model()}
      ensures if e.Model() !in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| - 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)
    
    method Contains(e:SetMap<T0, T1>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures  b == (e.Model() in Model()) 
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Copy(ghost counter_in:nat) returns (R:SetSetMap<T0, T1>, ghost counter_out:nat)
      ensures R.Model() == Model()
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

  }


  type SetPairMap<T0(==), T1(==), T2(==)>{
    ghost function Model():set<(map<T0, T1>, T2)>

    ghost function Size():nat
    {|Model()|*maximumSizeElements()}

    ghost function maximumSizeElements():nat
    ensures forall s | s in Model() :: maximumSizeElements() >= |s.0.Items|*sizeT
    ensures exists s :: s in Model() && maximumSizeElements() == |s.0.Items|*sizeT

    method Pick(ghost counter_in:nat) returns (e:(Map<T0, T1>, T2), ghost counter_out:nat)
      requires Model() != {}
      ensures counter_out == counter_in + maximumSizeElements()
      ensures exists m | m in Model() :: m.0 == e.0.Model() && m.1 == e.1
      ensures bound(counter_in, counter_out)
    
    method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures b == (Model() == {})
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Cardinality(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
      ensures  size == |Model()|
      ensures counter_out == counter_in + 1
      ensures bound(counter_in, counter_out)
    
    method Add(e:(Map<T0, T1>, T2), ghost counter_in:nat) returns (R:SetPairMap<T0, T1, T2>, ghost counter_out:nat)
      ensures  R.Model() == Model() + {(e.0.Model(), e.1)}
      ensures if (e.0.Model(), e.1) in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| + 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Remove(e:(Map<T0, T1>, T2), ghost counter_in:nat) returns (R:SetPairMap<T0, T1, T2>, ghost counter_out:nat)
      ensures  R.Model() == Model() - {(e.0.Model(), e.1)}
      ensures if (e.0.Model(), e.1) !in Model() then |R.Model()| == |Model()|
              else |R.Model()| == |Model()| - 1
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)
    
    method Contains(e:(Map<T0, T1>, T2), ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
      ensures  b == ((e.0.Model(), e.1) in Model()) 
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

    method Copy(ghost counter_in:nat) returns (R:SetPairMap<T0, T1, T2>, ghost counter_out:nat)
      ensures R.Model() == Model()
      ensures counter_out == counter_in + Size()
      ensures bound(counter_in, counter_out)

  }


 method NewSet(ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}
    ensures bound(counter_in, counter_out)
  
  method NewSetSet(ghost counter_in:nat) returns (R:SetSet, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}
    ensures bound(counter_in, counter_out)

  method NewSetSetSet(ghost counter_in:nat) returns (R:SetSetSet, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}
    ensures bound(counter_in, counter_out)

  method MakeSet<T(==)>(s:set<T>, ghost sizeT:nat, ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT*|s|
    ensures R.Model() == s
    ensures bound(counter_in, counter_out)


  method NewMap(ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == map[]
    ensures bound(counter_in, counter_out)

  method NewMapMap(ghost counter_in:nat) returns (R:MapMap, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == map[]
    ensures bound(counter_in, counter_out)

  method MakeMap<A(==), B(==)>(s:map<A, B>, ghost sizeT:nat, ghost counter_in:nat) returns (R:Map<A, B>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT*|s|
    ensures R.Model() == s
    ensures bound(counter_in, counter_out)


}



/*
module IntMod refines TypeMod {
  type T = int
  const sizeT := 1
}

module BoolMod refines TypeMod {
  type T = bool
  const sizeT := 1
}

module QuestionMod refines TypeMod {
  import opened Auxiliary
  type T = Question
  const sizeT := 1
}

module AnswerMod refines TypeMod {
  import opened Auxiliary
  type T = Answer
  const sizeT := 1
}
*/
