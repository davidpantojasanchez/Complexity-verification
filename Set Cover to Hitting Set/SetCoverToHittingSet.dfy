
include "SetCover.dfy"
include "HittingSet.dfy"

//TRANSFORMACION DE SET COVER A HITTING SET
// EJEMPLO: U = {1,2,3,4,5}, S= {{1,2,3}, {4,5}, {3,4}, {}}, K=3
//Set Cover devolveria True (una cobertura es {{1,2,3},{4,5}})
// Si hiciesemos: Hk=3
//      HU = {{1,2,3}, {4,5}, {3,4}, {}} , 
//      HS = {{{1,2,3}}, {{1,2,3},{3,4}}, {{3,4},{4,5}}, {{4,5}}},
//El Hitting-set es el mismo {{1,2,3},{4,5}}

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


lemma SetCover_HittingSet<T>(U:set<T>, S: set<set<T>>, k:nat)
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
 

 
       
  





