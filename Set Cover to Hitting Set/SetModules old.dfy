
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
   ghost function maximumSizeElements():nat
   ensures forall s | s in Model() :: maximumSizeElements() >= |s|*sizeT
   ensures exists s :: s in Model() && maximumSizeElements() == |s|*sizeT

   ghost function sizeSetSet():nat
    {|Model()|*maximumSizeElements()}

  method Pick(ghost counter_in:nat) returns (e:Set, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + maximumSizeElements()
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


  type SetSetSet{
   ghost function Model():set<set<set<T>>>
   ghost function maximumSizeElements():nat
   ghost function maximumSizeElements'():nat

   ensures forall s | s in Model() :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*sizeT)
   ensures exists s | s in Model() :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*sizeT)

   ensures forall s | s in Model() :: maximumSizeElements() >= |s|*maximumSizeElements'()
   ensures exists s :: s in Model() && maximumSizeElements() == |s|*maximumSizeElements'()

   ghost function sizeSetSetSet():nat
    {|Model()|*maximumSizeElements()}

  method Pick(ghost counter_in:nat) returns (e:SetSet, ghost counter_out:nat)
    requires Model() != {}
    ensures counter_out == counter_in + maximumSizeElements()
    ensures e.Model() in Model()

  method Empty(ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (Model() == {})
    ensures counter_out == counter_in + 1
  
  method Size(ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |Model()|
    ensures counter_out == counter_in + 1
  
  method Add(e:SetSet, ghost counter_in:nat) returns (R:SetSetSet, ghost counter_out:nat)
    ensures  R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| + 1
    ensures counter_out == counter_in + sizeSetSetSet()

  method Remove(e:SetSet, ghost counter_in:nat) returns (R:SetSetSet, ghost counter_out:nat)
    ensures  R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then |R.Model()| == |Model()|
            else |R.Model()| == |Model()| - 1
    ensures counter_out == counter_in + sizeSetSetSet()
  
  method Contains(e:SetSet, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e.Model() in Model()) 
    ensures counter_out == counter_in + sizeSetSetSet()

  }


  method NewSet(ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}

  method NewSetSet(ghost counter_in:nat) returns (R:SetSet, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}

  method NewSetSetSet(ghost counter_in:nat) returns (R:SetSetSet, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == {}

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

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
requires forall s | s in S :: s <= U // los sets son subsets del universo
requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires forall s | s in sets :: s <= universe // los sets son subsets del universo
{
  exists s:set<T> :: hitsSets(sets, s) && |s| <= cardinality && s <= universe
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}

ghost function maximumSizeElements<T>(S:set<set<T>>):nat
ensures forall s | s in S :: maximumSizeElements(S) >= |s|
ensures exists s :: s in S && maximumSizeElements(S) == |s|

lemma mult_preserves_order(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{
}

// VERIFICACIÓN DE SET COVER ES POLINÓMICA

method verifySetCover(U:Set, S:SetSet, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
ensures counter <= counter_in + 2 + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3)
{
  counter := counter_in;
  
  var emptyU;
  emptyU,counter := U.Empty(counter); //+1
  
  var e:T,U'; U':=U; //copia: ESTO IGUAL DEBE SER UN METODO ADICIONAL?? 
  assert U.Model()-U'.Model() == {} && |U.Model()-U'.Model()|==0;
  
  ghost var j := 0;
  assert counter == counter_in + 1;
  ghost var increment_per_iteration_outer := U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())

   invariant j == (|U.Model()| - |U'.Model()|)
   invariant counter <= counter_in + 1 + j*increment_per_iteration_outer
   {
    ghost var counter_outer := counter;
    assert counter_outer <= counter_in + 1 + j*increment_per_iteration_outer;
    ghost var oldU' := U';
    
    e,counter := U'.Pick(counter); //+sizeT
    assert counter == counter_outer + 1;
    U',counter:= U'.Remove(e,counter);//+|U'|*sizeT
    assert counter <= counter_outer + 1 + U.sizeSet() by {
      assert |U'.Model()| <= |U.Model()|;
      assert U'.sizeSet() == |U'.Model()|*sizeT;
      assert U.sizeSet() == |U.Model()|*sizeT;
      mult_preserves_order(|U'.Model()|, sizeT, |U.Model()|, sizeT);
      assert U'.sizeSet() <= U.sizeSet();
    }

    var empty,S'; S':=S; 
    
    assert |S.Model()-S'.Model()| == 0; 
    assert U.Model()-U'.Model() == U.Model()-oldU'.Model() + {e};
    assert |U.Model()-U'.Model()| == |U.Model()|-|U'.Model()| == |U.Model()|-|oldU'.Model()|+1;

    empty,counter := S.Empty(counter); //+1
    assert counter <= counter_outer + 1 + U.sizeSet() + 1;
    
    ghost var counter_start_inner_loop := counter;
    var found := false;
    ghost var i := 0;
    assert counter == counter_start_inner_loop + i*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1);
    ghost var increment_per_iteration_inner := S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1;
    while !empty && !found
      decreases (if !empty && !found then 1 else 0)+|S'.Model()|
      invariant empty == (S'.Model() == {}) 
      invariant U'.Model() == oldU'.Model()-{e}
      invariant S'.Model()<= S.Model()
      invariant !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
      invariant found ==> exists s:set<T> :: s in S.Model() && e in s
      
      invariant i == (|S.Model()| - |S'.Model()|)
      invariant counter <= counter_start_inner_loop + i*(increment_per_iteration_inner)    // *(|S.Model()| - |S'.Model()|)
    {
     ghost var counter_inner := counter;
     assert counter_inner <= counter_start_inner_loop + i*(increment_per_iteration_inner);
     ghost var prev_i := i;
    
     assert S'.maximumSizeElements() <= S.maximumSizeElements();
  
     var s;
     ghost var oldS':= S';
     s,counter := S'.Pick(counter); //+maxS
     assert |oldS'.Model()| == |S'.Model()|;
     assert oldS' == S';
     
     ghost var counter_1 := counter;
     assert s.Model() in S'.Model();
     S',counter := S'.Remove(s,counter);//+|S|*maxS
     assert |S'.Model()| == |oldS'.Model()| - 1;
     
     assert counter == counter_1 + oldS'.sizeSetSet();
     assert counter_1 == counter_inner + oldS'.maximumSizeElements();
     assert counter == counter_inner + oldS'.maximumSizeElements() + oldS'.sizeSetSet();
     
     ghost var counter_2 := counter;
     found,counter := s.Contains(e,counter);//+maxS*sizeT
     empty,counter := S'.Empty(counter);//+1
     assert counter <= counter_2 + S.maximumSizeElements() + 1;
              //Total suma <= maxS*(|S| + sizeT + 1)+1
     
     assert counter <= counter_inner + oldS'.maximumSizeElements() + oldS'.sizeSetSet() + S.maximumSizeElements() + 1;
     assert 0 <= |oldS'.Model()| <= |S.Model()|;
     assert 0 <= oldS'.maximumSizeElements() <= S.maximumSizeElements();
    
     mult_preserves_order(|oldS'.Model()|, oldS'.maximumSizeElements(), |S.Model()|, S.maximumSizeElements());
     assert |oldS'.Model()|*oldS'.maximumSizeElements() <= |S.Model()|*S.maximumSizeElements();

     assert oldS'.sizeSetSet() == |oldS'.Model()|*oldS'.maximumSizeElements();
     assert S.sizeSetSet() == |S.Model()|*S.maximumSizeElements();

     assert oldS'.sizeSetSet() <= S.sizeSetSet();
     assert counter <= counter_inner + S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1;
     assert counter_inner <= counter_start_inner_loop + i*(increment_per_iteration_inner);
     
     i := i + 1;
     assert i == prev_i + 1;
     assert counter <= counter_inner + increment_per_iteration_inner;
     assert counter_inner <= counter_start_inner_loop + (i-1)*(increment_per_iteration_inner);
     assert counter <= counter_start_inner_loop + i*(increment_per_iteration_inner);
    }
    assert counter <= counter_start_inner_loop + i*(increment_per_iteration_inner);
    assert i <= |S.Model()|;
    mult_preserves_order(i, increment_per_iteration_inner, |S.Model()|, increment_per_iteration_inner);
    assert counter_start_inner_loop <= counter_outer + 1 + U.sizeSet() + 1;
    assert counter <= counter_outer + 1 + U.sizeSet() + 1 + |S.Model()|*(increment_per_iteration_inner);

    b := b && found;
    emptyU,counter := U'.Empty(counter);//+1
    assert counter <= counter_outer + U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
    assert counter <= counter_outer + increment_per_iteration_outer;

    j := j + 1;
  }
  assert counter <= counter_in + 1 + j*increment_per_iteration_outer;
  assert j <= |U.Model()|;
  mult_preserves_order(j, increment_per_iteration_outer, |U.Model()|, increment_per_iteration_outer);
  assert counter <= counter_in + 1 + |U.Model()|*increment_per_iteration_outer;
  assert increment_per_iteration_outer == U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
  assert counter <= counter_in + 1 + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3);
   
  var size;
  size,counter := S.Size(counter);
  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());

  b := emptyU && b && size <= k;

  assert counter <= counter_in + 2 + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3);
  assert b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k);
}





// LA REDUCCIÓN ES CORRECTA

function SetCover_to_HittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S, newS, k)
}

//DEMOSTRACION DE QUE SON EQUIVALENTES
// es decir:  SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
// siendo (HU,HS,Hk) la transformacion de (U,S,k)


lemma SetCover_HittingSet<T>(U:set<T>, S:set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
  {
   var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
   SetCover_HittingSet1(U,S,k);
   SetCover_HittingSet2(U,S,k);
  } 

// Vamos a demostrar estos dos lemas:
//El primer lema demuestra HS ==> SC

 lemma SetCover_HittingSet1<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) <== HittingSet(HU,HS,Hk)
{ var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
   if (HittingSet(HU,HS,Hk)) {  
    var C:set<set<T>> :| hitsSets(HS, C) && |C| <= Hk && C <= HU;
    //Veamos que se cumple que C es cobertura de U, es decir, isCover(U,C)
    forall u | u in U
    ensures exists s :: s in C && u in s
     { var ss := (set s | s in S && u in s);
       assert ss in HS && ss * C != {};
       var s :| s in ss * C;
       assert u in s;
     }
   }
}

//El segundo lema demuestra SC ==> HS

//Usamos dos lemas auxiliares que hacen falta para demostrar 
//que la propia cobertura es el Hitting-set
lemma intersect_set_of_sets<T>(U:set<T>,u:T,S: set<set<T>>, C:set<set<T>>)
requires u in U
requires forall s | s in S :: s <= U
requires C <= S && isCover(U, C) 
ensures  var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {}
{assert C != {};
 var ss := (set s | s in S && u in s);
 var cs :| cs in C && u in cs;
 assert cs in ss * C;
 assert  ss * C != {};
}

//Version generalizada del anterior
lemma gintersect_set_of_sets<T>(U:set<T>,S: set<set<T>>, C:set<set<T>>)
requires forall s | s in S :: s <= U
requires C <= S && isCover(U, C) 
ensures  forall u | u in U ::
         (var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {})
{forall u | u in U 
 ensures (var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {})
         {intersect_set_of_sets(U,u,S,C);}

}

lemma SetCover_HittingSet2<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
  {  var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
     if (U == {}) { 
      //Este es un caso especial algo raro 
      //pero no lo he quitado en las precondiciones
      //Solo hay dos casos S={} o S={{}}
        if (S == {}) {}
        else if (S == {{}}) { 
              var C := {};
              assert C <= U && |C| <= Hk;
              assert HittingSet(HU,HS,Hk);}
        else {//Este caso no es posible
              //Lo demostramos por reduccion al absurdo
              if (S!={} && S!={{}}) 
               { var s :| s in S && s!={} ;
                 assert exists u :: u in s; 
                 assert false;}
             }
    }
     else{
      if (SetCover(U,S,k)) {
       var C:set<set<T>> :| C <= S && isCover(U, C) && |C| <= k;
       assert C <= HU && |C| <= Hk by
           {assert C!={};
            var s :| s in S && s !={};
            assert s in S-{{}};
            assert S-{{}}!={};}
      //Tenemos que demostrar que el mismo C es Hitting set
      //Por ser C cobertura sabemos que cada elemento de U
      //corresponde a un conjunto de newS cuyos conjuntos contienen a u
      //Usamos el lema auxiliar
      gintersect_set_of_sets(U,S,C);
      //assert forall s | s in HS :: C * s != {};
      //assert exists s:set<set<T>> :: hitsSets(HS, s) && |s| <= Hk && s <= HU;
      }
     } 
  }




method method_SetCover_to_HittingSet(U:Set, S:SetSet, k: nat) returns (r:(set<set<T>>, set<set<set<T>>>, int), ghost counter:int)
  requires forall s | s in S.Model() :: s <= U.Model()
  requires isCover(U.Model(), S.Model())
  ensures r == SetCover_to_HittingSet(U.Model(), S.Model(), k)
  //ensures counter <= 2*|U| + 2*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|U|*|U|
{
  assert |U.Model()| >= 0 && |S.Model()| >= 0;

  ghost var sizeT:int := 1;
  counter := 0;

  var HU := S;
  var Hk := k;

  var HS:set<set<set<T>>> := {};
  var U2 := U;

  while 0<|U2.Model()|
    decreases U2
    
    invariant forall s | s in HS :: s <= HU.Model()
    invariant HS == (set u | u in (U.Model() - U2.Model()) :: (set s | s in S.Model() && u in s))
    
    invariant |HS| <= |U.Model() - U2.Model()|
    invariant counter <= ((2 + (2*|S.Model()| + |U.Model()| + 2)*(|S.Model()|))  + 3*|U.Model()|) * |U.Model() - U2.Model()|

    //invariant |U| >= 0 && |S| >= 0
  {

    ghost var prevDifference := |U.Model() - U2.Model()|;
    ghost var prevCounter := counter;
    counter := counter + 1;
    //var v :| v in U2;
    var v;
    v, counter := U2.Pick(counter);
    assert counter == prevCounter + 2;

    var S2 := S;
    //assert counter == prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|);
    var hs:SetSet, counter := NewSetSet(counter);

    while 0<|S2.Model()|
      decreases S2

      invariant hs.Model() == (set s | s in (S.Model() - S2.Model()) && v in s)
      invariant HS == (set u | u in (U.Model() - U2.Model()) :: (set s | s in S.Model() && u in s))

      invariant forall s | s in S2.Model() :: s <= U.Model()
      invariant S2.Model() <= S.Model()
      invariant hs.Model() <= S.Model()

      //invariant counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|)
    {
      //ghost var increment := 1 + |U| + |S|*|U| + |U| + |S|*|U|;
      //assert 1 + |U| + |S|*|U| + |U| + |S|*|U| == increment;

      ghost var counter_iteration_loop := counter;
      ghost var prev_S_minus_S2 := |S.Model()| - |S2.Model()|;

      counter := counter + 1;
      //var s :| s in S2;
      var s:Set;
      s, counter := S2.Pick(counter);        // |U|
      assert counter <= counter_iteration_loop + 1 + |U.Model()|;

      if_subset_then_smaller(s.Model(), U.Model());
      if_subset_then_smaller(S2.Model(), S.Model());

      assert |S.Model()| - |S2.Model()| == prev_S_minus_S2;
      //S2 := S2 - {s};
      S2, counter := S2.Remove(s, counter);  // |S|*|U|
      //assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U|;

      //assert |S| - |S2| == prev_S_minus_S2 + 1;

      var cont:bool;
      cont, counter := s.Contains(v, counter);  // |U|
      //assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U| + |U|;
      if (cont == true) { //v in s {
        //hs := hs + {s};
        assert s.Model() in S.Model();
        hs, counter := hs.Add(s, counter);  // |S|*|U|
        assert hs.Model() <= S.Model();
        if_subset_then_smaller(hs.Model(), S.Model());
      }
      
      //assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|)
      //by {
      //  assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U| + |U| + |S|*|U|;
      //  assert counter <= counter_iteration_loop + increment;

      //  assert hs == (set s | s in (S - S2) && v in s);
      // assert HS == (set u | u in (U - U2) :: (set s | s in S && u in s));

      //  assert forall s | s in S2 :: s <= U;
      //  assert S2 <= S;
      //  assert hs <= S;

      //  assert counter_iteration_loop <= prevCounter + 2 + (increment)*prev_S_minus_S2;
      //  assert |S| - |S2| == prev_S_minus_S2 + 1;

      //  assert counter <= prevCounter + 2 + (increment)*prev_S_minus_S2 + increment;
      //  assert counter <= prevCounter + 2 + (increment)*(prev_S_minus_S2 + 1);
      //}
    }
  
    //assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S|);
    
    //HS := HS + {hs};
    ghost var prevHS := HS;
    HS, counter := SetMod.add(HS, hs, |U|*|S|, counter);
    assert |HS| <= |prevHS| + 1;


    assert |HS| <= |U|;
    assert |U| >= 0 && |S| >= 0;
    //assert 0 <= |U|;
    //assert 0 <= |S|*|U|;
    assert |HS|*(|U|*|S|) <= |U|*(|U|*|S|);

    assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S|) + |U|*|U|*|S|;
    
    assume false;

    ghost var U3 := U2;
    //U2 := U2 - {v};
    U2, counter := SetMod.remove(U2, v, 1, counter);
    assert hs == (set s | s in (S - S2) && v in s);
    assert prevHS == (set u | u in (U - U3) :: (set s | s in S && u in s));
    assert (U - (U2 + {v})) == (U - U3);
    assert prevHS + {hs} == (set u | u in (U - (U2 + {v})) :: (set s | s in S && u in s)) + {(set s | s in (S - S2) && v in s)};

    assert forall s | s in S2 :: !(v in s);

    if_S2_has_no_set_with_v_then_can_remove_safely(S, S2, v);
    assert {(set s | s in S && v in s)} == {(set s | s in (S - S2) && v in s)};

    assert (set u | u in {v} :: (set s | s in S && u in s)) == {(set s | s in (S - S2) && v in s)};

    assert (set u | u in (U - (U2 + {v})) :: (set s | s in S && u in s))
            + (set u | u in {v} :: (set s | s in S && u in s))
            == (set u | u in (U - (U2 + {v})) + {v} :: (set s | s in S && u in s));
    assert (U - (U2 + {v})) + {v} == (U - U2 + {v});

    assert prevHS + {hs} == (set u | u in (U - U2) :: (set s | s in S && u in s));
    
  }
  assert counter <= 2*|U| + 2*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|U|*|U|;

  r := (HU, HS, Hk);
  assert r == (HU, HS, Hk);

  ghost var e := SetCover_to_HittingSet<T>(U, S, k);
  assert HU == e.0;
  assert Hk == e.2;

  assert HS == (set u | u in (U - U2) :: (set s | s in S && u in s));
  assert U2 == {};
  assert (U - {}) == U;
  assert HS == (set u | u in U :: (set s | s in S && u in s));

  assert HS == e.1;

  assert r == SetCover_to_HittingSet<T>(U, S, k);
}


lemma if_subset_then_smaller<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if |A| == 0 || |B| == 0 { // trivial base case
  }
  else if A <= B {
    var a:T :| a in A;
    if_subset_then_smaller(A - {a}, B - {a});
  }
}

lemma if_S2_has_no_set_with_v_then_can_remove_safely<T>(S:set<set<T>>, S2:set<set<T>>, v:T)
  decreases |S2|
  requires S2 <= S
  requires forall s | s in S2 :: !(v in s)
  ensures {(set s | s in S && v in s)}
       == {(set s | s in (S - S2) && v in s)}
{
  if |S2| == 0 {
    calc == {
      (set s | s in (S - S2) && v in s);
      (set s | s in (S - {}) && v in s);
      (set s | s in S && v in s);
    }
  }
  else {
    var a:set<T> :| a in S2;
    if_S2_has_no_set_with_v_then_can_remove_safely(S, S2 - {a}, v);
    assert {(set s | s in (S) && v in s)}
      == {(set s | s in ((S) - (S2 - {a})) && v in s)};
    assert !(v in a);
    calc == {
      (set s | s in (S - (S2 - {a})) && v in s);
      (set s | s in (S - S2) && v in s);
    }
  }
}
  





}
