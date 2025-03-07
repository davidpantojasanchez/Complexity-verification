/*include "ImmutableUnorderedSetSpec.dfy"
import opened ImmutableUnorderedSet
import opened ImmutableUnorderedSetofSet*/
include "SetModuleClara.dfy"
import opened SetMod
//DEFINICION DEL PROBLEMA SET COVER

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}

ghost function maximumSize<T>(S:set<set<T>>):nat
ensures forall s | s in S :: maximumSize(S) >= |s|
ensures exists s :: s in S && maximumSize(S) == |s|



method verifySetCover<T>(U:set<T>, ghost sizeT:nat, S:set<set<T>>, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
requires sizeT >= 1
ensures b == (isCover(U,S) &&  |S| <= k)
/*ensures counter <= counter_in + 1 +
                  |U|* // para cada elemento
                  (|U|*(sizeT+1) +  //sacarlo del conjunto y borrarlo
                   1 + //mirar si S es vacio
                   |S|* //para cada conjunto de S
                   (maximumSize(S)*(|S| + sizeT + 1)+1)) //sacarlo de S, borrarlo, ver si contiene el elemento, ver si es vacio 
*/
{
  counter := counter_in;
  ghost var maxS := maximumSize(S); 
  
  assume |S| >= 1 && |U| >= 1;
  assume maxS >= 1;

  var emptyU;
  emptyU,counter := Empty(U,counter); //+1
  
  var e:T,U'; U':=U; //copia: ESTO IGUAL DEBE SER UN METODO ADICIONAL?? 
  assert U-U' == {} && |U-U'|==0;
  /*assert counter <= counter_in + 1 +
                  |U-U'|* // para cada elemento ya procesado
                  (|U|*(sizeT+1) +  //sacarlo del conjunto y borrarlo
                   1 + //mirar si S es vacio
                   |S|* //para cada conjunto de S
                   (maximumSize(S)*(|S| + sizeT + 1)+1));*/
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'|
   invariant emptyU == (U' == {})
   invariant U' <= U
   invariant b == isCover(U-U',S)
   {         
    ghost var oldU' := U';
    
    e,counter := Pick(U',sizeT,counter); //+sizeT
    U',counter:= Remove(U',e,sizeT,counter);//+|U'|*sizeT

    var empty,S'; S':=S; 
    
    assert |S-S'| == 0; 
    assert U-U' == U-oldU' + {e};
    assert |U-U'| == |U|-|U'| == |U|-|oldU'|+1;

    empty,counter := Empty(S,counter); //+1
    var found := false;
                       
    while !empty && !found
    decreases (if !empty && !found then 1 else 0)+|S'|
    invariant empty == (S' == {}) 
    invariant U' == oldU'-{e}
    invariant S'<= S
    invariant !found ==> (forall s| s in S-S':: e !in s)
    invariant found ==> exists s:set<T> :: s in S && e in s
    {
  
     var s;
     ghost var oldS':= S';
     s,counter := Pick(S',maxS,counter); //+maxS
     S',counter := Remove(S',s,maxS,counter);//+|S|*maxS
     found,counter := Contains(s,e,sizeT,counter);//+maxS*sizeT
     empty,counter := Empty(S',counter);//+1
              //Total suma <= maxS*(|S| + sizeT + 1)+1
    }

    b := b && found;
    emptyU,counter := Empty(U',counter);//+1
  } 
   
  var size;
  size,counter := Size(S,counter);
  assert emptyU && b ==> U-U' == U && isCover(U,S);

  b := emptyU && b && size <= k;

  /*calc{ |U|* 
      (|U|*(sizeT+1) + 1 + |S|*  (maxS*(|S| + sizeT + 1)+1));
      |U|*|U|*sizeT + |U|*|U| + |U|+ |U|*|S|*maxS * |S|+ |U|*|S|*maxS*sizeT + |U|*|S|*maxS + |U|*|S|;
          <=  {assume |U|*|U|*sizeT <= |U|*|U|*|S|*|S|*maxS*sizeT;
               assert |U|*|U| <= |U|*|U|*|S|*|S|*maxS*sizeT;
               assume |U|*|S|*maxS*|S| <= |U|*|U|*|S|*|S|*maxS*sizeT;
               assume |U|*|S|*maxS*sizeT <= |U|*|U|*|S|*|S|*maxS*sizeT;
               assume |U|*|S|*maxS <= |U|*|U|*|S|*|S|*maxS*sizeT;
               assume |U|*|S| <= |U|*|U|*|S|*|S|*maxS*sizeT;
                assume false;
              }
      7*|U|*|U|*|S|*|S|*maxS*sizeT;
  }*/

}


/*method verifySetCover<T(==,!new)>(U:ImmutableUnorderedSet<T>, S:ImmutableUnorderedSetofSet<T>, k:nat) returns (b:bool)
ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
//ensures counter_out  <= counter_in + |U|*|S.Model()|*(max s | s in s.Model(): |s.Model()|)
//ensures counter_out <= counter_in + |U|*|S.Model()|*
{
    ghost var counter := 0;
  var emptyU;
  emptyU,counter := U.Empty(counter);

  var e,U'; U':=U; 
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())
  {         
    ghost var oldU' := U'.Model();

    e,U',counter := U'.Pick(counter);


    var empty,S'; S':=S;
    empty,counter := S.Empty(counter); var found := false;
    while !empty && !found
    decreases (if !empty && !found then 1 else 0)+|S'.Model()|
    invariant empty == (S'.Model() == {}) 
    invariant U'.Model() == oldU'-{e}
    invariant S'.Model()<=S.Model()
    invariant !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
    invariant found ==> exists s:set<T> :: s in S.Model() && e in s
    {
     var s;
     ghost var oldS':= S'.Model();
     s,S',counter := S'.Pick(counter);
     found,counter := s.Contains(e,counter);
     empty,counter := S'.Empty(counter);
     
    }

    assert U.Model() - U'.Model() == U.Model()- oldU' + {e};
    b := b && found;
    emptyU,counter := U'.Empty(counter);
  } 
  var size;
  size,counter := S.Size(counter);
  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());

  b := emptyU && b && size <= k;
}*/