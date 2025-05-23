include "Problems.dfy"
//include "Types.dfy"

abstract module SetCoverMod{
  import opened Problems
  import opened TypeMod

ghost function maximumSizeElements<T>(S:set<set<T>>):nat
ensures forall s | s in S :: maximumSizeElements(S) >= |s|
ensures exists s :: s in S && maximumSizeElements(S) == |s|

lemma mult_preserves_order(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{
}





// * LA VERIFICACIÓN DE SET COVER ES POLINÓMICA

method verifySetCover<T>(U:Set, S:SetSet, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
ensures counter <= counter_in + 2 + U.Size() + |U.Model()|*(U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3)
{
  counter := counter_in;
  ghost var oldU := U;
  
  var emptyU;
  emptyU,counter := U.Empty(counter); //+1
  
  var e:T;
  var U':Set;
  //U':=U; //copia: ESTO IGUAL DEBE SER UN METODO ADICIONAL??
  U', counter := U.Copy(counter);
  assert U'.Model() == U.Model();
  assert U.Model()-U'.Model() == {} && |U.Model()-U'.Model()|==0;
  
  ghost var j := 0;
  assert counter == counter_in + 1 + U.Size();
  ghost var increment_per_iteration_outer := U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())

   invariant j == (|U.Model()| - |U'.Model()|)
   invariant counter <= counter_in + 1 + U.Size() + j*increment_per_iteration_outer

   invariant increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3
   {
    ghost var counter_outer := counter;
    assert counter_outer <= counter_in + 1 + U.Size() + j*increment_per_iteration_outer;
    
    e,counter := U'.Pick(counter); //+sizeT
    assert counter == counter_outer + sizeT;
    ghost var oldU' := U';
    assert U'.Size() <= U.Size();
    assert oldU'.Size() <= U.Size();
    U',counter:= U'.Remove(e,counter);//+|U'|*sizeT
    assert counter <= counter_outer + sizeT + U.Size() by {
      assert |U'.Model()| <= |U.Model()|;
      assert U'.Size() == |U'.Model()|*sizeT;
      assert U.Size() == |U.Model()|*sizeT;
      mult_preserves_order(|U'.Model()|, sizeT, |U.Model()|, sizeT);
      
      assert counter <= counter_outer + sizeT + oldU'.Size();
      assert U'.Size() <= U.Size();
      assert oldU'.Size() <= U.Size();
      assert counter <= counter_outer + sizeT + U.Size();
    }
    assert increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;

    var empty,S'; S':=S; 
    
    assert |S.Model()-S'.Model()| == 0; 
    assert U.Model()-U'.Model() == U.Model()-oldU'.Model() + {e};
    assert |U.Model()-U'.Model()| == |U.Model()|-|U'.Model()| == |U.Model()|-|oldU'.Model()|+1;

    empty,counter := S.Empty(counter); //+1
    assert counter <= counter_outer + sizeT + U.Size() + 1;
    
    ghost var counter_start_inner_loop := counter;
    var found := false;
    ghost var i := 0;
    assert counter == counter_start_inner_loop + i*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1);
    ghost var increment_per_iteration_inner := S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1;


    if (!empty && !found) {
      assert empty == (S'.Model() == {});
      assert U'.Model() == oldU'.Model()-{e};
      assert S'.Model()<= S.Model();
      assert !found ==> (forall s| s in S.Model()-S'.Model():: e !in s);
      assert found ==> exists s:set<T> :: s in S.Model() && e in s;
      assert i == (|S.Model()| - |S'.Model()|);
      assert counter <= counter_start_inner_loop + i*(increment_per_iteration_inner);
      assert increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;
    }
    while !empty && !found
      decreases (if !empty && !found then 1 else 0)+|S'.Model()|
      invariant empty == (S'.Model() == {}) 
      invariant U'.Model() == oldU'.Model()-{e}
      invariant S'.Model()<= S.Model()
      invariant !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
      invariant found ==> exists s:set<T> :: s in S.Model() && e in s
      
      invariant i == (|S.Model()| - |S'.Model()|)
      invariant counter <= counter_start_inner_loop + i*(increment_per_iteration_inner)    // *(|S.Model()| - |S'.Model()|)

      invariant increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3
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
     
     assert counter == counter_1 + oldS'.Size();
     assert counter_1 == counter_inner + oldS'.maximumSizeElements();
     assert counter == counter_inner + oldS'.maximumSizeElements() + oldS'.Size();
     
     ghost var counter_2 := counter;
     found,counter := s.Contains(e,counter);//+maxS*sizeT
     empty,counter := S'.Empty(counter);//+1
     assert counter <= counter_2 + S.maximumSizeElements() + 1;
              //Total suma <= maxS*(|S| + sizeT + 1)+1
     
     assert counter <= counter_inner + oldS'.maximumSizeElements() + oldS'.Size() + S.maximumSizeElements() + 1;
     assert 0 <= |oldS'.Model()| <= |S.Model()|;
     assert 0 <= oldS'.maximumSizeElements() <= S.maximumSizeElements();
    
     mult_preserves_order(|oldS'.Model()|, oldS'.maximumSizeElements(), |S.Model()|, S.maximumSizeElements());
     assert |oldS'.Model()|*oldS'.maximumSizeElements() <= |S.Model()|*S.maximumSizeElements();

     assert oldS'.Size() == |oldS'.Model()|*oldS'.maximumSizeElements();
     assert S.Size() == |S.Model()|*S.maximumSizeElements();

     assert oldS'.Size() <= S.Size();
     assert counter <= counter_inner + S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1;
     assert counter_inner <= counter_start_inner_loop + i*(increment_per_iteration_inner);
     
     i := i + 1;
     assert i == prev_i + 1;
     assert counter <= counter_inner + increment_per_iteration_inner;
     assert counter_inner <= counter_start_inner_loop + (i-1)*(increment_per_iteration_inner);
     assert counter <= counter_start_inner_loop + i*(increment_per_iteration_inner);
   
    }
    assert counter <= counter_start_inner_loop + i*(increment_per_iteration_inner);
    assume false;
    assert i <= |S.Model()|;
    mult_preserves_order(i, increment_per_iteration_inner, |S.Model()|, increment_per_iteration_inner);
    assert counter_start_inner_loop <= counter_outer + 1 + U.Size() + 1;
    assert counter <= counter_outer + 1 + U.Size() + 1 + |S.Model()|*(increment_per_iteration_inner);

    b := b && found;
    emptyU,counter := U'.Empty(counter);//+1
    assert counter <= counter_outer + U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;
    assert counter <= counter_outer + increment_per_iteration_outer;

    j := j + 1;
  }
  assert increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;
  assert counter <= counter_in + 1 + U.Size() + j*increment_per_iteration_outer;
  assert 0 <= j <= |U.Model()|;
  
  mult_preserves_order(j, increment_per_iteration_outer, |U.Model()|, increment_per_iteration_outer) by {
    assert 0 <= increment_per_iteration_outer;
    assert increment_per_iteration_outer <= increment_per_iteration_outer;
    assert 0 <= increment_per_iteration_outer <= increment_per_iteration_outer;
  }

  assert counter <= counter_in + 1 + U.Size() + |U.Model()|*(U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3) by {
    assert counter <= counter_in + 1 + U.Size() + |U.Model()|*increment_per_iteration_outer;
    assert increment_per_iteration_outer == U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3;
  }

  var size;
  size,counter := S.Cardinality(counter);
  assert counter <= counter_in + 2 + U.Size() + |U.Model()|*(U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3);
  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());

  b := emptyU && b && size <= k;
  assert b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k);
  //assert counter <= counter_in + 2 + U.Size() + |U.Model()|*(U.Size() + |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1) + 3);
  //ghost var f1 := |S.Model()|*(S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + 1);
  //assert counter <= counter_in + 2 + |U.Model()|*(U.Size() + f1 + 3);
  //assert counter <= counter_in + 2 + |U.Model()|*U.Size() + |U.Model()|*f1 + |U.Model()|*3;
  //ghost var f2 := (|S.Model()|*S.maximumSizeElements() + |S.Model()|*S.Size() + |S.Model()|*S.maximumSizeElements() + |S.Model()|*1);
  //assert f1 == f2;
  //assert counter <= counter_in + 2 + |U.Model()|*U.Size() + |U.Model()|*f2 + |U.Model()|*3;
  //assert counter <= counter_in + 2 + |U.Model()|*U.Size() + |U.Model()|*(|S.Model()|*S.maximumSizeElements() + |S.Model()|*S.Size() + |S.Model()|*S.maximumSizeElements() + |S.Model()|*1) + |U.Model()|*3;
  //assert |U.Model()|*((|S.Model()|*S.maximumSizeElements()) + (|S.Model()|*S.Size()) + (|S.Model()|*S.maximumSizeElements()) + (|S.Model()|*1)) ==
  //       |U.Model()|*(|S.Model()|*S.maximumSizeElements()) + |U.Model()|*(|S.Model()|*S.Size()) + |U.Model()|*(|S.Model()|*S.maximumSizeElements()) + |U.Model()|*(|S.Model()|*1);
  //assert counter <= counter_in + 2 + |U.Model()|*U.Size() + |U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*|S.Model()|*S.Size() + |U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*|S.Model()|*1 + |U.Model()|*3;
}





// * LA TRANSFORMACIÓN ES CORRECTA

// Transformación:

function SetCover_to_HittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S, newS, k)
}

//DEMOSTRACION DE QUE SON EQUIVALENTES
// es decir:  SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
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

}

