


module ImmutableUnorderedSet {


  trait {:termination false} ImmutableUnorderedSet<K(==, !new)> {

    ghost function compare(e1:K,e2:K):nat

    ghost function sizeT():nat
    ensures forall e1,e2 | e1 in Model() && e2 in Model()::compare(e1,e2) <= sizeT()
  
    //cota superior del coste que cuesta comparar los elementos del conjunto

    ghost function Model():set<K> 
    reads this

    method Pick(ghost counter_in:int) returns (x:K, s:ImmutableUnorderedSet<K>, ghost counter_out:int)
      requires Model()!={}
      ensures x in Model()
      ensures s.Model() == Model()-{x}
      ensures |s.Model()| == |Model()| - 1
      ensures counter_out == counter_in + sizeT()
    

    method Empty(ghost counter_in:int) returns (b: bool, ghost counter_out:int)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1


    method Size(ghost counter_in:int) returns (n: nat,ghost counter_out:int)
      ensures n == |Model()|
      ensures counter_out == counter_in + 1


    method Contains(x: K, ghost counter_in:int) returns (b: bool, ghost counter_out:int)
      decreases 0
      ensures b == (x in Model())
      ensures counter_out == counter_in + |Model()|*sizeT()


    method Add(x: K, ghost counter_in:int) returns(s :ImmutableUnorderedSet<K>,ghost counter_out:int)
      decreases 0
      ensures s.Model() == Model() + {x}
      ensures if x in Model() then |s.Model()| == |Model()|
              else |s.Model()| == |Model()| + 1
      ensures counter_out == counter_in + |Model()|*sizeT()
    


    method Remove(x: K,ghost counter_in:int) returns (s:ImmutableUnorderedSet<K>,ghost counter_out:int)
      decreases 0
      ensures s.Model() == Model() - {x}
      ensures  if x in Model() then
        |s.Model()| == |Model()| - 1
      else
        |s.Model()| == |Model()|
      ensures counter_out == counter_in + |Model()|*sizeT()


  }


  





  class ImmutableUnorderedSetInt extends ImmutableUnorderedSet<int> {
   var simp:set<int>
   ghost function compare(e1:int,e2:int):nat
   {1}
  
   ghost function sizeT():nat
   ensures forall e1,e2 | e1 in Model() && e2 in Model()::compare(e1,e2) <= sizeT()
   {1}
  
   ghost function Model():set<int>
   reads this
   {simp}
   
   constructor(other:set<int>)
   ensures other == Model()
   { simp := other;}

   method Pick(ghost counter_in:int) returns (x:int, s:ImmutableUnorderedSet<int>, ghost counter_out:int)
      requires Model()!={}
      ensures x in Model()
      ensures s.Model() == Model()-{x}
      ensures |s.Model()| == |Model()| - 1
      ensures counter_out == counter_in + sizeT()
    {
     var z:| z in simp;
     x := z;
     s := new ImmutableUnorderedSetInt(simp -{x}); 
     counter_out := counter_in + sizeT();
    }

    method Empty(ghost counter_in:int) returns (b: bool, ghost counter_out:int)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
    {
      b := (simp == {});
      counter_out := counter_in + 1;
    }


    method Size(ghost counter_in:int) returns (n: nat,ghost counter_out:int)
      ensures n == |Model()|
      ensures counter_out == counter_in + 1
    { 
      n := |simp|;
      counter_out := counter_in + 1;
    }

    method Contains(x: int, ghost counter_in:int) returns (b: bool, ghost counter_out:int)
      decreases 0
      ensures b == (x in Model())
      ensures counter_out == counter_in + |Model()|*sizeT()
    { b := x in simp;
      counter_out := counter_in + |simp|;
    }
   
    method Add(x: int, ghost counter_in:int) returns(s :ImmutableUnorderedSet<int>,ghost counter_out:int)
      decreases 0 
      ensures s.Model() == Model() + {x}
      ensures if x in Model() then |s.Model()| == |Model()|
              else |s.Model()| == |Model()| + 1
      ensures counter_out == counter_in + |Model()|*sizeT()
    { 
      s := new ImmutableUnorderedSetInt(simp + {x});
      assert (x in simp) ==> (simp + {x} == simp);
      counter_out := counter_in + |simp|;

    }

    method Remove(x: int,ghost counter_in:int) returns (s:ImmutableUnorderedSet<int>,ghost counter_out:int)
      decreases 0
      ensures s.Model() == Model() - {x}
      ensures  if x in Model() then
        |s.Model()| == |Model()| - 1
      else
        |s.Model()| == |Model()|
      ensures counter_out == counter_in + |Model()|*sizeT()
    { s := new ImmutableUnorderedSetInt(simp - {x});
      counter_out := counter_in + |simp|;
    }


  }
} 


module ImmutableUnorderedSetofSet{
 import opened ImmutableUnorderedSet 
 trait {:termination false} ImmutableUnorderedSetofSet<K(==, !new)> {

    
    ghost function compare(e1:ImmutableUnorderedSet<K>,e2:ImmutableUnorderedSet<K>):nat
    ensures compare(e1,e2) <= |e1.Model()| && compare(e1,e2) <= |e1.Model()|

    ghost function sizeT():nat
    ensures forall e1,e2 | e1 in ObjectModel() && e2 in ObjectModel()::compare(e1,e2) <= sizeT()
 
    //cota superior del coste que cuesta comparar los elementos del conjunto
    ghost function ObjectModel():set<ImmutableUnorderedSet<K>> 
    reads this
    

    ghost function Model():set<set<K>> 
    reads this//, ObjectModel()
    //{set s | s in ObjectModel():: s.Model() }

    method Pick(ghost counter_in:int) returns (x:ImmutableUnorderedSet<K>, s:ImmutableUnorderedSetofSet<K>, ghost counter_out:int)
      requires Model()!={}
      ensures x.Model() in Model()
      ensures s.Model() == Model()-{x.Model()}
      ensures |s.Model()| == |Model()| - 1
      ensures counter_out == counter_in + sizeT()
    

    method Empty(ghost counter_in:int) returns (b: bool, ghost counter_out:int)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1


    method Size(ghost counter_in:int) returns (n: nat,ghost counter_out:int)
      ensures n == |Model()|
      ensures counter_out == counter_in + 1


    method Contains(x:ImmutableUnorderedSet<K>, ghost counter_in:int) returns (b: bool, ghost counter_out:int)
      decreases 0
      ensures b == (x.Model() in Model())
      ensures counter_out == counter_in + |Model()|*sizeT()


    method Add(x: ImmutableUnorderedSet<K>, ghost counter_in:int) returns(s :ImmutableUnorderedSetofSet<K>,ghost counter_out:int)
      decreases 0
      ensures s.Model() == Model() + {x.Model()}
      ensures if x.Model() in Model() then |s.Model()| == |Model()|
              else |s.Model()| == |Model()| + 1
      ensures counter_out == counter_in + |Model()|*sizeT()
    


    method Remove(x: ImmutableUnorderedSet<K>,ghost counter_in:int) returns (s:ImmutableUnorderedSetofSet<K>,ghost counter_out:int)
      decreases 0
      ensures s.Model() == Model() - {x.Model()}
      ensures  if x.Model() in Model() then
        |s.Model()| == |Model()| - 1
      else
        |s.Model()| == |Model()|
      ensures counter_out == counter_in + |Model()|*sizeT()


  } 
}