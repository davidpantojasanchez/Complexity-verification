include "AdtWithoutThis.dfy"
//include "KeyValue.dfy"
include "SetObject.dfy"



module UnorderedSetSpec {
  import opened ADT
  //import opened KeyValue
  import opened SetObject


  trait {:termination false} UnorderedSet<K(==)> extends ADT<set<K>> {

    ghost function sizeT(): nat
    //cota superior del coste que cuesta comparar los elementos del conjunto

    twostate predicate PickModel(new x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
    { && x in old(Model())
      && Model() == old(Model()) - {x}
      && |Model()| == old(|Model()|) - 1
      
    }



    method Pick(ghost counter_in:int) returns (x:K, ghost counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures PickModel(x)
      ensures counter_out == counter_in + sizeT()
    
    
    
    twostate predicate EmptyModel(b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (Model() == {})
    }

    method Empty(ghost counter_in:int) returns (b: bool, ghost counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures EmptyModel(b)
      ensures counter_out == counter_in + 1

    twostate predicate SizeModel(s: nat)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && s == |Model()|
    }

    method Size(ghost counter_in:int) returns (s: nat,ghost counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures SizeModel(s)
      ensures counter_out == counter_in + 1



    twostate predicate ContainsModel(x: K, b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (x in Model())
    }

    method Contains(x: K, ghost counter_in:int) returns (b: bool, counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures ContainsModel(x, b)
      ensures counter_out == counter_in + |Model()|*sizeT()

    twostate predicate AddModel(x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) + {x}
      && if x in old(Model()) then
        |Model()| == old(|Model()|)
      else
        |Model()| == old(|Model()|) + 1
    }

    method Add(x: K, ghost counter_in:int) returns(ghost counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures AddModel(x)
      ensures counter_out == counter_in + |Model()|*sizeT()


    twostate predicate RemoveModel(x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) - {x}
      && if x in old(Model()) then
        |Model()| == old(|Model()|) - 1
      else
        |Model()| == old(|Model()|)
    }

    method Remove(x: K,ghost counter_in:int) returns (ghost counter_out:int)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures RemoveModel(x)
      ensures counter_out == counter_in + |Model()|*sizeT()


  }


} 




