
abstract module SetMod {
  type T
  const sizeT :nat

  type Set{

  ghost function Model():set<T>
  ghost function sizeSet():nat
  {|Model()|*sizeT}

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + 1
    ensures e in Model()
  
  method Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
  

  method Size(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
  


  method Add(e:T, ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures  R.Model() == Model() + {e}
    ensures if e in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + sizeSet()




  method Remove(e:T, ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e}
    ensures if e !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + sizeSet()
  

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e in Model()) 
    ensures counter_out == counter_in + sizeSet()

  }
  type SetSet{
   ghost function Model():set<set<T>>
   ghost function maximumSize():nat
   ensures forall s | s in Model() :: maximumSize() >= |s|*sizeT
   ensures exists s :: s in Model() && maximumSize() == |s|*sizeT

   ghost function sizeSetSet():nat
    {|Model()|*maximumSize()}


  method Pick(ghost counter_in:nat) returns (e:Set, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + maximumSize()
    ensures e.Model() in Model()

  method Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
  

  method Size(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
  


  method Add(e:Set, ghost counter_in:nat) returns (R:SetSet, ghost counter_out:nat)
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + sizeSetSet()




  method Remove(e:Set, ghost counter_in:nat) returns (R:SetSet, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + sizeSetSet()
  

  method Contains(e:Set, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e.Model() in Model()) 
    ensures counter_out == counter_in + sizeSetSet()


  }
}

module SetInt refines SetMod{
type T = int
const sizeT := 1

}



abstract module SetCover{
  import opened SetMod
  ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
  {
   forall e | e in universe :: (exists s | s in sets :: e in s)
  }

method verifySetCover(U:Set, S:SetSet, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
//ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
{
  counter := counter_in;
  ghost var oldU := U;
  
  var emptyU;
  emptyU,counter := U.Empty(counter); //+1
  
  var e:T,U'; U':=U; //copia: ESTO IGUAL DEBE SER UN METODO ADICIONAL?? 
  assert U.Model()-U'.Model() == {} && |U.Model()-U'.Model()|==0;
  
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())
   {         
    ghost var oldU' := U';
    
    e,counter := U'.Pick(counter); //+sizeT
    U',counter:= U'.Remove(e,counter);//+|U'|*sizeT

    var empty,S'; S':=S; 
    
    assert |S.Model()-S'.Model()| == 0; 
    assert U.Model()-U'.Model() == U.Model()-oldU'.Model() + {e};
    assert |U.Model()-U'.Model()| == |U.Model()|-|U'.Model()| == |U.Model()|-|oldU'.Model()|+1;

    empty,counter := S.Empty(counter); //+1
    var found := false;
                       
    while !empty && !found
    decreases (if !empty && !found then 1 else 0)+|S'.Model()|
    invariant empty == (S'.Model() == {}) 
    invariant U'.Model() == oldU'.Model()-{e}
    invariant S'.Model()<= S.Model()
    invariant !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
    invariant found ==> exists s:set<T> :: s in S.Model() && e in s
    {
  
     var s;
     ghost var oldS':= S';
     s,counter := S'.Pick(counter); //+maxS
     S',counter := S'.Remove(s,counter);//+|S|*maxS
     found,counter := s.Contains(e,counter);//+maxS*sizeT
     empty,counter := S'.Empty(counter);//+1
              //Total suma <= maxS*(|S| + sizeT + 1)+1
    }

    b := b && found;
    emptyU,counter := U'.Empty(counter);//+1
  } 
   
  var size;
  size,counter := S.Size(counter);
  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());

  b := emptyU && b && size <= k;

}

}



