include "Problems.dfy"

abstract module SetCoverMod{
  import opened Problems
  import opened Auxiliary
  import opened TypeMod

ghost function maximumSizeElements<T>(S:set<set<T>>):nat
ensures forall s | s in S :: maximumSizeElements(S) >= |s|
ensures exists s :: s in S && maximumSizeElements(S) == |s|


// * LA VERIFICACIÓN DE SET COVER ES POLINÓMICA

method verifySetCover<T>(U:Set, S:SetSet, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
ensures counter <= counter_in + 3*poly(U,S) + poly(U,S)*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)))
{
  counter := counter_in;
  ghost var oldU := U;
  
  var emptyU;
  emptyU,counter := U.Empty(counter); //+1
  
  var e:T;
  var U':Set;
  //U':=U;
  U', counter := U.Copy(counter);
  assert U'.Model() == U.Model();
  assert U.Model()-U'.Model() == {} && |U.Model()-U'.Model()|==0;
  
  ghost var j := 0;
  //assert counter == counter_in + 1 + U.Size();
  assert counter <= counter_in + 2*poly(U,S);
  b :=true;

  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())

   invariant j == (|U.Model()| - |U'.Model()|)
   invariant counter <= counter_in + 2*poly(U,S) + j*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)))
  {
    U', b, emptyU, j, counter := body_loop_outer<T>(U, S, k, U', j, counter);
  }
  
  assert counter <= counter_in + 2*poly(U,S) + j*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)));

  var size;
  size,counter := S.Cardinality(counter);
  assert counter <= counter_in + 3*poly(U,S) + poly(U,S)*(4*poly(U,S) + poly(U,S)*(4*poly(U,S))) by {
    assert counter <= counter_in + 3*poly(U,S) + j*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)));
    assert j <= |U.Model()|;
    assert j <= poly(U,S);
    mult_preserves_order(j, (4*poly(U,S) + poly(U,S)*(4*poly(U,S))), poly(U,S), (4*poly(U,S) + poly(U,S)*(4*poly(U,S))));
    assert counter <= counter_in + 3*poly(U,S) + poly(U,S)*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)));
  }

  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());
  b := emptyU && b && size <= k;
  assert b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k) by {
    assume (emptyU && b) == isCover(U.Model(),S.Model());
    assert size == |S.Model()|;
    assert ((emptyU && b) && size <= k) == (isCover(U.Model(),S.Model()) &&  size <= k);
    assert (size <= k) == (|S.Model()| <= k);
    assert ((emptyU && b) && size <= k) == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k);
  }
}




function poly(U:Set, S:SetSet):(R:nat)   // {:opaque}
ensures R >= U.Size()
ensures R >= S.Size()
ensures R >= |U.Model()|
ensures R >= |S.Model()|
ensures R >= 1

function poly2(U:Set, S:SetSet):(R:nat)
ensures R >= poly(U,S)*poly(U,S)

function poly3(U:Set, S:SetSet):(R:nat)
ensures R >= poly(U,S)*poly2(U,S)


method body_loop_inner<T>(U:Set, S:SetSet, k:nat, S'_:SetSet, e:T, ghost i_:nat, ghost counter_in:nat)
returns (S':SetSet, empty:bool, found:bool, ghost i:nat, ghost counter:nat)
  
  requires S'_.Model() != {}
  requires S'_.Model() <= S.Model()
  requires i_ == (|S.Model()| - |S'_.Model()|)
  requires (forall s| s in S.Model()-S'_.Model():: e !in s)

  ensures S'.Model()<= S.Model()
  ensures empty == (S'.Model() == {}) 
  ensures !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
  ensures found ==> exists s:set<T> :: s in S.Model() && e in s
  ensures i == (|S.Model()| - |S'.Model()|)
  ensures i == i_+1

  ensures (!empty && !found) ==> (|S'.Model()| < |S'_.Model()|)
  ensures counter <= counter_in + 4*poly(U,S)
{
  S' := S'_;
  counter := counter_in;
  var s;
  s,counter := S'.Pick(counter); //+maxS
  assert counter <= counter_in + poly(U,S);
  ghost var prev_S' := S';
  S',counter := S'.Remove(s,counter);//+|S|*maxS
  assert counter <= counter_in + 2*poly(U,S) by {
    assert counter <= counter_in + poly(U,S) + prev_S'.Size();
    assert prev_S'.Size() <= S.Size() by {
      assert prev_S'.Model() <= S.Model();
      assert prev_S'.maximumSizeElements() <= S.maximumSizeElements();
      mult_preserves_order(|prev_S'.Model()|, prev_S'.maximumSizeElements(), |S.Model()|, S.maximumSizeElements());
    }
  }
  found,counter := s.Contains(e,counter);//+maxS*sizeT
  assert counter <= counter_in + 3*poly(U,S);
  empty,counter := S'.Empty(counter);//+1
  assert counter <= counter_in + 4*poly(U,S);

  i := i_ + 1;
}



method body_loop_outer<T>(U:Set, S:SetSet, k:nat, U'_:Set, ghost j_:nat, ghost counter_in:nat) returns (U':Set, b:bool, emptyU:bool, ghost j:nat, ghost counter:nat)
/*
while !emptyU && b
decreases (if !emptyU then 1 else 0)+|U'.Model()|
invariant emptyU == (U'.Model() == {})
invariant U'.Model() <= U.Model()
invariant b == isCover(U.Model()-U'.Model(),S.Model())

invariant j == (|U.Model()| - |U'.Model()|)
invariant counter <= counter_in + 2*poly(U,S) + j*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)))
*/
requires U'_.Model() <= U.Model()
requires j_ == (|U.Model()| - |U'_.Model()|)
requires U'_.Model() != {}
requires isCover(U.Model()-U'_.Model(),S.Model())

ensures (!emptyU) ==> (|U'.Model()| < |U'_.Model()|)
ensures emptyU == (U'.Model() == {})
ensures U'.Model() <= U.Model()
ensures b == isCover(U.Model()-U'.Model(),S.Model())
ensures j == (|U.Model()| - |U'.Model()|)
ensures j == j_ + 1
ensures counter <= counter_in + 4*poly(U,S) + poly(U,S)*(4*poly(U,S))

{
  U' := U'_;
  counter := counter_in;

  var e:T;
  e,counter := U'.Pick(counter); //+sizeT
  U',counter:= U'.Remove(e,counter);//+|U'|*sizeT
  var empty,S'; S':=S;
  empty,counter := S.Empty(counter); //+1
  var found := false;
  assert counter <= counter_in + 3*poly(U,S);
  ghost var i := 0;

  while !empty && !found
    decreases (if !empty && !found then 1 else 0)+|S'.Model()|
    invariant empty == (S'.Model() == {}) 
    invariant U'.Model() == U'_.Model()-{e}
    invariant S'.Model()<= S.Model()
    invariant !found ==> (forall s| s in S.Model()-S'.Model():: e !in s)
    invariant found ==> exists s:set<T> :: s in S.Model() && e in s
    
    invariant i == (|S.Model()| - |S'.Model()|)
    invariant counter <= counter_in + 3*poly(U,S) + i*(4*poly(U,S))    // *(|S.Model()| - |S'.Model()|)
  {
    assert counter <= counter_in + 3*poly(U,S) + i*(4*poly(U,S));
    ghost var counter_start_body := counter;
    ghost var i_start_body := i;
    S', empty, found, i, counter := body_loop_inner(U, S, k, S', e, i, counter);

    assert S'.Model()<= S.Model();
    assert empty == (S'.Model() == {});
    assert !found ==> (forall s| s in S.Model()-S'.Model():: e !in s);
    assert found ==> exists s:set<T> :: s in S.Model() && e in s;
    assert i == (|S.Model()| - |S'.Model()|);
    assert counter <= counter_in + 3*poly(U,S) + i*(4*poly(U,S)) + 4*poly(U,S) by {
      assert counter <= counter_start_body + 4*poly(U,S);
      assert i-1 == i_start_body;
      assert counter_start_body <= counter_in + 3*poly(U,S) + (i-1)*(4*poly(U,S));
    }
  }
  assert counter <= counter_in + 3*poly(U,S) + poly(U,S)*(4*poly(U,S)) by {
    assert counter <= counter_in + 3*poly(U,S) + i*(4*poly(U,S));
    assert i <= |S.Model()|;
    mult_preserves_order(i, (4*poly(U,S)), poly(U,S), (4*poly(U,S)));
  }

  b := found;
  assert b == isCover(U.Model()-U'.Model(),S.Model()) by {
    assert isCover(U.Model()-U'_.Model(),S.Model());
    if found {
      ghost var prev_difference := (U.Model()-U'_.Model());
      assert forall e | e in (prev_difference + {e}) :: (exists s | s in S.Model() :: e in s) by {
        assert exists_s_in_S_such_that_e_in_s(S, e) by { reveal exists_s_in_S_such_that_e_in_s(); }
        assert forall e | e in prev_difference :: exists_s_in_S_such_that_e_in_s(S, e) by { reveal exists_s_in_S_such_that_e_in_s(); }
        assume false;
        assert forall e | e in (prev_difference+{e}) :: exists_s_in_S_such_that_e_in_s(S, e);
      }
      assert ((U.Model()-U'_.Model()) + {e}) == (U.Model()-U'.Model());
      assert isCover(U.Model()-U'.Model(),S.Model());
    }
    else {
      assert !b;
      assert !(exists s | s in S.Model() :: e in s);
      assert !(forall e | e in ((U.Model()-U'_.Model()) + {e}) :: (exists s | s in S.Model() :: e in s));
      assert !isCover(((U.Model()-U'_.Model()) + {e}),S.Model());
      assert ((U.Model()-U'_.Model()) + {e}) == (U.Model()-U'.Model());
      assert !isCover(U.Model()-U'.Model(),S.Model());
    }
  }
  emptyU,counter := U'.Empty(counter);
  j := j_ + 1;
  assert counter <= counter_in + 4*poly(U,S) + poly(U,S)*(4*poly(U,S));
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

lemma adding_case_to_exists_property<T>(S:SetSet, U:set<T>, e:T)
requires exists_s_in_S_such_that_e_in_s(S, e)
requires forall e | e in U :: exists_s_in_S_such_that_e_in_s(S, e)
ensures forall e | e in (U+{e}) :: exists_s_in_S_such_that_e_in_s(S, e)
{
  if U == {} {
    //assert (forall e | e in (U+{e}) :: exists_s_in_S_such_that_e_in_s(S, e)) == (forall e | e in ({}+{e}) :: exists_s_in_S_such_that_e_in_s(S, e)) == (forall e | e in {e} :: exists_s_in_S_such_that_e_in_s(S, e));
    assert forall e | e in U :: exists_s_in_S_such_that_e_in_s(S, e);
    assert forall e | e in {e} :: exists_s_in_S_such_that_e_in_s(S, e) by {
      assert exists_s_in_S_such_that_e_in_s(S, e);
      abcd(S,e,exists_s_in_S_such_that_e_in_s(S, e));
      assume false;
    }
  }
  else {
    assume false;
  }
}

/*
lemma forall_e_in_e<T>(S:SetSet, e:T)
ensures (forall e | e in {e} :: exists_s_in_S_such_that_e_in_s(S, e)) == exists_s_in_S_such_that_e_in_s(S, e)
{
  assert !exists_s_in_S_such_that_e_in_s(S, e) ==> !(forall e | e in {e} :: exists_s_in_S_such_that_e_in_s(S, e));
  assert exists_s_in_S_such_that_e_in_s(S, e) ==> !(exists e | e in {e} :: !exists_s_in_S_such_that_e_in_s(S, e));
  assume false;
}
*/

lemma abcd<T>(S:SetSet, e:T, b:bool)
requires b
ensures forall e:T | e in {e} :: b
{
}

ghost predicate {:opaque} exists_s_in_S_such_that_e_in_s<T>(S:SetSet, e:T) {
  (exists s | s in S.Model() :: e in s)
}

}



