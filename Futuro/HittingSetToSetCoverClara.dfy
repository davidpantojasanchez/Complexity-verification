//Created by: Clara Segura
include "SetCover.dfy"
include "HittingSet.dfy"

lemma tisCover(U: set<int>, S: set<set<int>>) 
requires forall s | s in S :: s <= U
requires {} !in S
 ensures 
   var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
   isCover(S,newS)
{ var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
  forall e | e in S ensures (exists s | s in newS :: e in s)
  {    assert e != {};
       assert exists n :: n in e; 
       var n :| n in e;
       assert e in (set s | s in S && n in s);
       assert (set s | s in S && n in s) in newS;
    }
    
}

function HittingSet_to_SetCover(U: set<int>, S: set<set<int>>, k: nat) : (r:(set<set<int>>, set<set<set<int>>>, int))
  requires forall s | s in S ::  s <= U // los sets son subsets del universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
  ensures isCover(r.0, r.1) // existe un subconjunto de sets tal que su union es igual al universo
{
  var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
  
  if ({} in S) then (S, (set s | s in S :: {s}), 0)//que devuelva falso siempre 
  else
   tisCover(U,S);
   (S, newS, k)
}


lemma {:induction C} cardinal_of_sets1(U: set<int>, S:set<set<int>>, C:set<int>,CS:set<set<set<int>>>)
requires C <= U 
requires CS == (set x | x in C :: (set ys | ys in S && x in ys))
ensures |CS| <= |C|
//EJEMPLO: C={1,2}, S={{1,2}} CS ={ {{1,2}} } 
{
  if C=={} { assert |CS|==|C|==0; }
    else{ 

    var x:| x in C;
    var CS' := (set y | y in C-{x} :: (set ys | ys in S && y in ys));
    
    assert CS == CS' +{(set ys | ys in S && x in ys)} by{
      calc{  CS;{}
          (set y | y in C :: (set ys | ys in S && y in ys));
          {assert C==C-{x}+{x};}
          (set y | y in C-{x}+{x} :: (set ys | ys in S && y in ys));
          (set y | y in C-{x} :: (set ys | ys in S && y in ys)) + (set y | y in {x} :: (set ys | ys in S && y in ys));
          CS' + {(set ys | ys in S && x in ys)};
        }
    }
    if ((set ys | ys in S && x in ys) in CS') {
      assert CS' == CS;
      assert |CS| == |CS'|;    
    }
    else {
      assert |CS| == |CS'| + 1; 
    }
    cardinal_of_sets1(U,S,C-{x},CS');
    assert |CS'| <= |C-{x}|;
    assert |CS| <= |C|;
  }
}


//La anterior propuesta no era correcta porque |C| puede ser >= |CS|
//Tenemos que asegurarnos de que tenemos solo un elemento de cada CS 
//Por ejemplo {1,2}, {3,4} ->  -> CS = {{{1,2}}, {{3,4}}} 
// C={1,2,3,4} con esta definicion pero debería ser {1,3} por ejemplo
//Uno del mismo tamaño que CS

function min(s:set<int>) : (x:int)
requires s != {}
ensures x in s && (forall y | y in s :: x <= y)


lemma HittingSet_SetCover(U:set<int>, S: set<set<int>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) <==> SetCover(SU,SS,Sk)
  { var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
    HittingSet_SetCover1(U,S,k);
    HittingSet_SetCover2(U,S,k);
  }

lemma HittingSet_SetCover1(U:set<int>, S: set<set<int>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) ==> SetCover(US,SS,kS)
{
  var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
  if (HittingSet(U,S,k)) {
    if ({} in S) { assert false; }
    else { 
    var C:set<int> :| hitsSets(S, C) && |C| <= k && C <= U;      // {2,4}
    var CS := (set x | x in C :: (set y | y in US && x in y)); // { {{1,2,3},{2,4}}, {{2,4},{3,4},{4,5}} }

    //Para demostrar que es cobertura hay que demostrar lo siguiente
    forall s | s in US 
    ensures (exists ss | ss in CS :: s in ss)
    {
     assert C * s != {}; //por ser C Hitting-set
     var y :| y in C * s; 
     var ss := (set ys | ys in US && y in ys);
     assert ss in CS && s in ss;
     }
     cardinal_of_sets1(U,S,C,CS);
     assert |CS| <= |C| <= k;
     //Idea de demo, la funcion es inyectiva 
 }
}
}
function setsElem(U:set<int>, S: set<set<int>>, e:int): (r:set<set<int>>)
requires forall s | s in S :: s <= U 
{ set s | s in S && e in s}

//lemma extensionality(s1:set<set<int>>, s2:set<set<int>>)
//ensures s1 == s2 <==> forall xs | xs in s1 :: xs in s2 && forall xs | xs in s2 :: xs in s1

function minSetsElem(U:set<int>, S: set<set<int>>, e:int): (m:int)
requires forall s | s in S :: s <= U 
requires e in U && setsElem(U,S,e) != {}
{ 
  assert e in U && setsElem(U,S,e) == setsElem(U,S,e);
  var allEs:set<int> := set e' | e' in U && setsElem(U,S,e') == setsElem(U,S,e);
  assert e in U && setsElem(U,S,e) == setsElem(U,S,e);
  assert e in allEs;
  min(allEs)  
}

function minCSElem(U:set<int>, S:set<set<int>>,k:nat,CS: set<set<set<int>>>, xs:set<int>): (m:int)
requires forall s | s in S :: s <= U 
requires xs in S 
requires exists e :: e in U && xs in setsElem(U,S,e) && setsElem(U,S,e) in CS
requires var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
         CS <= SS && isCover(US, CS) && {} !in CS && |CS| <= kS
{ 
  var allEs:set<int> := set e' | e' in U && xs in setsElem(U,S,e') && setsElem(U,S,e') in CS;
  assert exists e :: e in U && xs in setsElem(U,S,e) && setsElem(U,S,e) in CS;
  var e:int :| e in U && xs in setsElem(U,S,e) && setsElem(U,S,e) in CS;
  assert e in allEs;
 min(allEs)  
}


lemma {:induction C,CS} cardinal_of_sets2(U: set<int>, S:set<set<int>>, k:nat, C:set<int>,CS:set<set<set<int>>>)
requires forall s | s in S :: s <= U 
requires C <= U 
requires CS <= (set u | u in U :: (set s | s in S && u in s)) && {} !in CS
requires C == set e | e in U  && (set s | s in S && e in s) in CS :: minSetsElem(U,S,e)
ensures |C| == |CS|
{ if CS== {} {}
  else {
    var cs:| cs in CS;
    var ecs :| ecs in U && (set s | s in S && ecs in s) == cs && ecs in C ;
    assert C - {ecs} == set e | e in U  && (set s | s in S && e in s) in CS-{cs} :: minSetsElem(U,S,e);
    cardinal_of_sets2(U,S,k,C-{ecs},CS-{cs});
    }
}



lemma HittingSet_SetCover2(U:set<int>, S: set<set<int>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) <== SetCover(US,SS,kS)
{
  var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
  if (SetCover(US,SS,kS)) {
    var CS':set<set<set<int>>> :| CS' <= SS && isCover(US, CS') && |CS'| <= kS; // { {{1,2,3},{2,4}}, {{2,4},{3,4},{4,5}} }
    

    if ({} in S) { 
      //Hay que demostrar que SetCover devuelve falso
      // para (S, (set s | s in S :: {s}), 0)
      assert !isCover(S,{});
    }
    else { 
      var CS :set<set<set<int>>> := CS' -{{}};
      assert CS <= SS && isCover(US, CS) && |CS| <= kS && {} !in CS;

      var C:set<int> := set e | e in U  && (set s | s in S && e in s) in CS :: minSetsElem(U,S,e);
      forall xs | xs in S
      ensures xs * C != {} 
      {
        var cs :| cs in CS && xs in cs;
        var intersection := minCSElem(U,S,k,CS,xs);
        assert intersection in xs;
        assert intersection in U;
        assert (set s | s in S && intersection in s) in CS;
        assert xs in setsElem(U,S,intersection) && setsElem(U,S,intersection) in CS;
        
        var mse := minSetsElem(U,S,intersection);
        var allEs:set<int> := set e' | e' in U && setsElem(U,S,e') == setsElem(U,S,intersection);
        assert intersection in allEs;
        assert allEs != {};
        assert intersection >= min(allEs) == mse;
        
        var allCs:set<int> := set e' | e' in U && xs in setsElem(U,S,e') && setsElem(U,S,e') in CS;
        assert mse in U && xs in setsElem(U,S,mse) && setsElem(U,S,mse) in CS;
        assert mse in allCs;
        assert intersection <= mse;
        assert intersection == mse;

        assert intersection in C;
        assert intersection in xs * C;
      }
      assert hitsSets(S, C);
      cardinal_of_sets2(U,S,k,C,CS);
      assert |C| ==|CS|;
    }
  }
}