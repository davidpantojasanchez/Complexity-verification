abstract module SetMod{
  type T(==)
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

  method Copy(ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures R.Model() == Model()
    ensures counter_out == counter_in + sizeSet()

  method GetSet(ghost counter_in:nat) returns (R:set<T>, ghost counter_out:nat)
    ensures R == Model()
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

  method Copy(ghost counter_in:nat) returns (R:SetSet, ghost counter_out:nat)
    ensures R.Model() == Model()
    ensures counter_out == counter_in + sizeSetSet()
  }


  type SetSetSet{
   ghost function Model():set<set<set<T>>>

   ghost function maximumSizeElements():nat
   ensures forall s | s in Model() :: maximumSizeElements() >= |s|*maximumSizeElements'()
   ensures exists s :: s in Model() && maximumSizeElements() == |s|*maximumSizeElements'()

   ghost function maximumSizeElements'():nat
   ensures forall s | s in Model() :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*sizeT)
   ensures exists s | s in Model() :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*sizeT)


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

  method Copy(ghost counter_in:nat) returns (R:SetSetSet, ghost counter_out:nat)
    ensures R.Model() == Model()
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

  method MakeSet(s:set<T>, ghost sizeT:nat, ghost counter_in:nat) returns (R:Set, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT*|s|
    ensures R.Model() == s

}

module SetInt refines SetMod{
  type T = int
  const sizeT := 1
}

module SetQuestion refines SetMod{
  import opened Auxiliar
  type T = Question
  const sizeT := 1
}

module SetAnswer refines SetMod{
  import opened Auxiliar
  type T = Answer
  const sizeT := 1
}

module SetQA refines SetMod{
  import opened Auxiliar
  type T = map<Question, Answer>
  const sizeT := 1
}






abstract module MapMod {

  type A(==)
  type B(==)
  type C(==)
  const sizeT :nat  // upper bound of A, B and C

  type Map{

  ghost function Model():map<A, B>
  ghost function sizeMap():nat
  {|Model()|*sizeT}

  method Get(q:A, ghost counter_in:nat) returns (a:B, ghost counter_out:nat)
    requires Model() != map[]
    requires q in Model().Keys
    ensures counter_out == counter_in + sizeT
    ensures a == Model()[q]

  method Add(q:A, a:B, ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + sizeT
    ensures R.Model() == Model()[q := a]

  method Remove(q:A, ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    requires q in Model().Keys
    ensures counter_out == counter_in + sizeT
    ensures R.Model() == Model() - {q}

  method Keys(ghost counter_in:nat) returns (keys:set<A>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMap()
    ensures keys == Model().Keys

  method Values(ghost counter_in:nat) returns (keys:set<B>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMap()
    ensures keys == Model().Values

  method Items(ghost counter_in:nat) returns (keys:set<(A, B)>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMap()
    ensures keys == Model().Items

  method HasKey(q:A, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q in Model().Keys)
  
  method Restrict(s:set<A>, ghost counter_in:nat) returns (R:map<A, B>, ghost counter_out:nat)
    requires s <= Model().Keys
    ensures counter_out == counter_in + sizeMap()
    ensures R.Keys == s
    ensures forall key:A | key in R.Keys :: R[key] == Model()[key]
    ensures forall i:(A, B) | i in R.Items :: i in Model().Items              // redundante
  
  }

  type MapMap{

  ghost function Model():map<map<A, B>, C>
  ghost function sizeMapMap():nat
  {|Model()|*maximumSizeElements()}

   ghost function maximumSizeElements():nat
   ensures forall s | s in Model().Keys :: maximumSizeElements() >= |s.Items|*sizeT
   ensures exists s :: s in Model() && maximumSizeElements() == |s.Items|*sizeT

  method Get(q:map<A, B>, ghost counter_in:nat) returns (a:C, ghost counter_out:nat)
    requires Model() != map[]
    requires q in Model().Keys
    ensures counter_out == counter_in + maximumSizeElements()
    ensures a == Model()[q]

  method Add(q:map<A, B>, a:C, ghost counter_in:nat) returns (R:MapMap, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + maximumSizeElements()
    ensures R.Model() == Model()[q := a]
  
  method Remove(q:map<A, B>, ghost counter_in:nat) returns (R:MapMap, ghost counter_out:nat)
      requires q in Model().Keys
      ensures counter_out == counter_in + maximumSizeElements()
      ensures R.Model() == Model() - {q}
    
  method Keys(ghost counter_in:nat) returns (keys:set<map<A, B>>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMapMap()
    ensures keys == Model().Keys

  method Values(ghost counter_in:nat) returns (keys:set<C>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMapMap()
    ensures keys == Model().Values

  method Items(ghost counter_in:nat) returns (keys:set<(map<A, B>, C)>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeMapMap()
    ensures keys == Model().Items

  method HasKey(q:map<A, B>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q in Model().Keys)
  
  method Restrict(s:set<map<A, B>>, ghost counter_in:nat) returns (R:MapMap, ghost counter_out:nat)
    requires s <= Model().Keys
    ensures counter_out == counter_in + sizeMapMap()
    ensures R.Model().Keys == s
    ensures forall key:map<A, B> | key in R.Model().Keys :: R.Model()[key] == Model()[key]
    ensures forall i:(map<A, B>, C) | i in R.Model().Items :: i in Model().Items              // redundante
  
  }

  method NewMap(ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == map[]

  method NewMapMap(ghost counter_in:nat) returns (R:MapMap, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == map[]

  method MakeMap(s:map<A, B>, ghost sizeT:nat, ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT*|s|
    ensures R.Model() == s
  
}

module MapBool refines MapMod{
  import opened Auxiliar
  type A = Question
  type B = Answer
  type C = bool
  const sizeT := 1
}

module MapInt refines MapMod{
  import opened Auxiliar
  type A = Question
  type B = Answer
  type C = int
  const sizeT := 1
}

/*
module MapSet refines MapMod{
  import opened Auxiliar
  type A = Question
  type B = Answer
  type C = set<map<Question, Answer>>
  const sizeT := 1
}
*/


module GroupMod {
  import opened Auxiliar
  
  const sizeT :nat := 1
  
  type GroupCandidates {
   ghost function Model():map<map<Question, Answer>, set<map<Question, Answer>>>

   ghost function maximumSizeElements():nat
   ensures forall s | s in Model().Values :: maximumSizeElements() >= |s|*maximumSizeElements'()
   ensures exists s | s in Model().Values :: maximumSizeElements() == |s|*maximumSizeElements'()

   ghost function maximumSizeElements'():nat
   ensures forall s | s in Model().Values :: (forall s' | s' in s :: maximumSizeElements'() >= |s'|*sizeT)
   ensures exists s | s in Model().Values :: (exists s' | s' in s :: maximumSizeElements'() == |s'|*sizeT)

   ghost function sizeGroup():nat
    {|Model()|*maximumSizeElements()}

  method Get(q:map<Question, Answer>, ghost counter_in:nat) returns (a:set<map<Question, Answer>>, ghost counter_out:nat)
    requires Model() != map[]
    requires q in Model().Keys
    ensures counter_out == counter_in + maximumSizeElements()
    ensures a == Model()[q]

  method Add(q:map<Question, Answer>, a:set<map<Question, Answer>>, ghost counter_in:nat) returns (R:GroupCandidates, ghost counter_out:nat)
    //requires !(q in Model().Keys)
    ensures counter_out == counter_in + maximumSizeElements()
    ensures R.Model() == Model()[q := a]
  
  method Remove(q:map<Question, Answer>, ghost counter_in:nat) returns (R:GroupCandidates, ghost counter_out:nat)
      requires q in Model().Keys
      ensures counter_out == counter_in + maximumSizeElements()
      ensures R.Model() == Model() - {q}
    
  method Keys(ghost counter_in:nat) returns (keys:set<map<Question, Answer>>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeGroup()
    ensures keys == Model().Keys

  method Values(ghost counter_in:nat) returns (values:set<set<map<Question, Answer>>>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeGroup()
    ensures values == Model().Values

  method Items(ghost counter_in:nat) returns (items:set<(map<Question, Answer>, set<map<Question, Answer>>)>, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeGroup()
    ensures items == Model().Items

  method HasKey(q:map<Question, Answer>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures counter_out == counter_in + sizeT
    ensures b == (q in Model().Keys)

  }

  method NewGroup(ghost counter_in:nat) returns (R:GroupCandidates, ghost counter_out:nat)
    ensures counter_out == counter_in +1
    ensures R.Model() == map[]

}




abstract module Problems{
  import opened SetMod
  import opened Auxiliar
  
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

// D-ATDP : Problema determinista de decisión de tests adaptativos
/*
Problema de determinar si es posible construir unos tests adaptativo (árbol de tests) de hasta k tests que pueda determinar
si una IUT (implementation under test) en C es correcta (está en las especificaciones E) o incorrecta
*/
ghost predicate {:opaque} DATDP(C:set<map<Question, Answer>>, E:set<map<Question, Answer>>, k:int, I:set<Question>)
  requires E <= C
  requires 0 <= k <= |I|
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
{
  if k == 0 then
    separatedSet(C, E)
  else
    exists i:Question | i in I ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in C :: m[i]) ::
        DATDP(
          restrictSet(C, i, o),
          restrictSet(E, i, o),
          k - 1,
          I
        )
}

/*
Variante de D-ATDP diseñada para ser más similar al problema PCD-Límite. En lugar del conjunto de especificaciones
correctas E, tiene un mapa f de IUTs (mapas de tests a comportamientos) a bool (si la IUT es correcta o no)
*/
ghost predicate {:opaque} DATDPintermediate(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, k: int, I: set<Question>)
  requires f.Keys == C
  requires 0 <= k <= |I|
  requires forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I
{
  if k == 0 then
    separatedMixed(C, f)
  else
    exists i: Question | i in I ::
      forall o: Answer | o in (set m:map<Question, Answer> | m in C :: m[i]) ::
        DATDPintermediate(
          restrictSet(C, i, o),
          restrictMap(f, i, o),
          k - 1,
          I
        )
}

// PCD-Límite : Problema de clasificación de datos con características privadas no exhaustivo, interactivo, con límite de preguntas y total
/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Con límite de preguntas: Las ramas de la entrevista adaptativa no puede tener más de k preguntas
Total: Requiere poder discernir la aptitud de la población completamente
       Independientemente de quién es el candidato entrevistado, la entrevista debe ser capaz de determinar con certeza absoluta si es apto o no
*/
ghost predicate {:opaque} PCDLim(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0 <= k <= |Q|
{
  okPrivate(f, g, P, a, b, Q) &&
  if k == 0 then
    okFitness(f)
  else
    okFitness(f) ||
    exists i:Question | i in Q ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
        PCDLim(
          restrictMap(f, i, o),
          restrictMap(g, i, o),
          P, k - 1, a, b, Q
        )
}

}







abstract module SetCoverMod{
  import opened SetMod
  import opened Problems

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

method verifySetCover(U:Set, S:SetSet, k:nat,ghost counter_in:nat) returns (b:bool,ghost counter:nat)
ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
ensures counter <= counter_in + 2 + U.sizeSet() + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3)
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
  assert counter == counter_in + 1 + U.sizeSet();
  ghost var increment_per_iteration_outer := U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
  b :=true;
  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'.Model()|
   invariant emptyU == (U'.Model() == {})
   invariant U'.Model() <= U.Model()
   invariant b == isCover(U.Model()-U'.Model(),S.Model())

   invariant j == (|U.Model()| - |U'.Model()|)
   invariant counter <= counter_in + 1 + U.sizeSet() + j*increment_per_iteration_outer

   invariant increment_per_iteration_outer == U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3
   {
    ghost var counter_outer := counter;
    assert counter_outer <= counter_in + 1 + U.sizeSet() + j*increment_per_iteration_outer;
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

      invariant increment_per_iteration_outer == U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3
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
  assert increment_per_iteration_outer == U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
  assert counter <= counter_in + 1 + U.sizeSet() + j*increment_per_iteration_outer;
  assert 0 <= j <= |U.Model()|;
  
  mult_preserves_order(j, increment_per_iteration_outer, |U.Model()|, increment_per_iteration_outer) by {
    assert 0 <= increment_per_iteration_outer;
    assert increment_per_iteration_outer <= increment_per_iteration_outer;
    assert 0 <= increment_per_iteration_outer <= increment_per_iteration_outer;
  }


  assert counter <= counter_in + 1 + U.sizeSet() + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3) by {
    assert counter <= counter_in + 1 + U.sizeSet() + |U.Model()|*increment_per_iteration_outer;
    assert increment_per_iteration_outer == U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3;
  }

  var size;
  size,counter := S.Size(counter);
  assert counter <= counter_in + 2 + U.sizeSet() + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3);
  assert emptyU && b ==> U.Model()-U'.Model() == U.Model() && isCover(U.Model(),S.Model());

  b := emptyU && b && size <= k;
  assert b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k);
  //assert counter <= counter_in + 2 + U.sizeSet() + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3);
  //ghost var f1 := |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1);
  //assert counter <= counter_in + 2 + |U.Model()|*(U.sizeSet() + f1 + 3);
  //assert counter <= counter_in + 2 + |U.Model()|*U.sizeSet() + |U.Model()|*f1 + |U.Model()|*3;
  //ghost var f2 := (|S.Model()|*S.maximumSizeElements() + |S.Model()|*S.sizeSetSet() + |S.Model()|*S.maximumSizeElements() + |S.Model()|*1);
  //assert f1 == f2;
  //assert counter <= counter_in + 2 + |U.Model()|*U.sizeSet() + |U.Model()|*f2 + |U.Model()|*3;
  //assert counter <= counter_in + 2 + |U.Model()|*U.sizeSet() + |U.Model()|*(|S.Model()|*S.maximumSizeElements() + |S.Model()|*S.sizeSetSet() + |S.Model()|*S.maximumSizeElements() + |S.Model()|*1) + |U.Model()|*3;
  //assert |U.Model()|*((|S.Model()|*S.maximumSizeElements()) + (|S.Model()|*S.sizeSetSet()) + (|S.Model()|*S.maximumSizeElements()) + (|S.Model()|*1)) ==
  //       |U.Model()|*(|S.Model()|*S.maximumSizeElements()) + |U.Model()|*(|S.Model()|*S.sizeSetSet()) + |U.Model()|*(|S.Model()|*S.maximumSizeElements()) + |U.Model()|*(|S.Model()|*1);
  //assert counter <= counter_in + 2 + |U.Model()|*U.sizeSet() + |U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*|S.Model()|*S.sizeSetSet() + |U.Model()|*|S.Model()|*S.maximumSizeElements() + |U.Model()|*|S.Model()|*1 + |U.Model()|*3;
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












abstract module PCD {
  import opened SetQuestion
  import opened MapBool
  import opened MapInt
  import opened Auxiliar
  import opened SetQA
  import opened GroupMod

  // * LA VERIFICACIÓN DE PCDLim ES POLINÓMICA

  method verifyPCD//(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    (f:MapBool.MapMap, g:MapInt.MapMap, P:SetQuestion.Set, k:int, a:real, b:real, Q:SetQuestion.Set, questionsToVerify:SetQuestion.Set, ghost counter_in:nat)
    returns (R:bool, ghost counter:nat)
  //ensures b == (isCover(U.Model(),S.Model()) &&  |S.Model()| <= k)
  //ensures counter <= counter_in + 2 + U.sizeSet() + |U.Model()|*(U.sizeSet() + |S.Model()|*(S.maximumSizeElements() + S.sizeSetSet() + S.maximumSizeElements() + 1) + 3)
  requires forall m | m in g.Model().Keys :: m.Keys == Q.Model()
  requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= b <= 1.0
  requires 0 <= k <= |Q.Model()|

  requires questionsToVerify.Model() <= Q.Model()

  /*
  ensures |questionsToVerify.Model()| <= k &&
          forall answers:map<Question, Answer> | answers.Keys == questionsToVerify.Model() ::                                                                                     // para todas las formas de responder a la entrevista...
          (
          var f' := map candidate:map<Question, Answer> | candidate in f.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == answers[q]) :: f.Model()[candidate];
          var g' := map candidate:map<Question, Answer> | candidate in g.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == answers[q]) :: g.Model()[candidate];
          okFitness(f') && okPrivate(f', g', P.Model(), a, b, Q.Model())
          )
  */

  // Para todas las formas válidas de responder a las preguntas de la entrevista / grupos de tipos de candidatos (<= |f.Keys|), ver si la población restante es apta y/o infiere información privada
{
  counter := counter_in;
  var candidates:SetQA.Set;
  R := false;
  var nQuestions:int;
  nQuestions, counter := questionsToVerify.Size(counter);
  if nQuestions <= k {
    var keys:set<map<A, B>>;
    var candidates:SetQA.Set;
    var candidates_empty:bool;
    var groups:GroupCandidates;
    groups, counter := GroupMod.NewGroup(counter);
    keys, counter := f.Keys(counter);
    candidates, counter := SetQA.MakeSet(keys, f.maximumSizeElements(), counter);
    candidates_empty, counter := candidates.Empty(counter);

    assert counter == counter_in + 1 + 1 + f.sizeMapMap() + |keys|*f.maximumSizeElements() + 1;
    assert counter == counter_in + 2*f.sizeMapMap() + 3;
    
    while candidates_empty != true
      decreases |candidates.Model()|
      invariant candidates_empty == (candidates.Model() == {})
      invariant candidates.Model() <= keys
    {
      var candidate:map<Question, Answer>;
      candidate, counter := candidates.Pick(counter);
      var candidateMap:MapBool.Map;
      candidateMap, counter := MapBool.MakeMap(candidate, 1, counter);

      var answers:map<Question, Answer>;
      //answers, counter := MapBool.NewMap(counter);
      
      var qtvSet:set<Question>;
      qtvSet, counter := questionsToVerify.GetSet(counter);


      answers, counter := candidateMap.Restrict(qtvSet, counter) by {   // forma de responder a las preguntas de la entrevista
        assert qtvSet == questionsToVerify.Model() <= Q.Model();
        assert forall m | m in f.Model().Keys :: m.Keys == Q.Model();
        assert forall m | m in keys :: m.Keys == Q.Model();
        assert candidate in candidates.Model();
        assert candidates.Model() <= keys;
        assert candidate in keys;
        assert candidate.Keys == Q.Model();
        assert qtvSet <= candidate.Keys;
      }

      var hasKey:bool;
      hasKey, counter := groups.HasKey(answers, counter);

      if hasKey {
        var setCandidates:set<map<Question, Answer>>;
        setCandidates, counter := groups.Get(answers, counter);
        var setCandidates':SetQA.Set;
        setCandidates', counter := SetQA.MakeSet(setCandidates, f.maximumSizeElements(), counter);
        setCandidates', counter := setCandidates'.Add(candidate, counter);
        setCandidates, counter := setCandidates'.GetSet(counter);
        groups, counter := groups.Add(answers, setCandidates, counter);
      }
      else {
        groups, counter := groups.Add(answers, {candidate}, counter);
      }
  
      candidates, counter := candidates.Remove(candidate, counter);
      candidates_empty, counter := candidates.Empty(counter);
    }

    var aux:(bool, nat);
    assume forall candidates | candidates in groups.Model().Values ::     // !
           forall key | key in candidates ::
           key in f.Model().Keys;
    aux := okPrivateGroup(groups, f, g, P, k, a, b, Q, counter);
    R := aux.0;
    aux := okFitnessGroup(groups, f, g, P, k, a, b, Q, counter);
    R := R && aux.0;
    counter := aux.1;
  }
}
/*
{
  okPrivate(f, g, P, a, b, Q) &&
  if k == 0 then
    okFitness(f)
  else
    okFitness(f) ||
    exists i:Question | i in Q ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
        PCDLim(
          restrictMap(f, i, o),
          restrictMap(g, i, o),
          P, k - 1, a, b, Q
        )


  map m:map<Question, Answer> | m in f.Keys && m[i] == o :: f[m] // restrict map
}
*/

function okPrivateGroup(groups:GroupCandidates, f:MapBool.MapMap, g:MapInt.MapMap, P:SetQuestion.Set, k:int, a:real, b:real, Q:SetQuestion.Set, ghost counter_in:nat) : (r:(bool, nat))
  requires forall m | m in g.Model().Keys :: m.Keys == Q.Model()
  requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b

  requires forall candidates | candidates in groups.Model().Values ::
           forall key | key in candidates ::
           key.Keys <= Q.Model()

  requires forall candidates | candidates in groups.Model().Values ::
           forall key | key in candidates ::
           key in f.Model().Keys

  ensures r.1 == counter_in + 1
  ensures r.0 ==
          forall candidates | candidates in groups.Model().Values ::
          var f' := map key | key in candidates :: f.Model()[key];
          var g' := map key | key in candidates :: g.Model()[key];
          okPrivate(f', g', P.Model(), a, b, Q.Model())


function okFitnessGroup(groups:GroupCandidates, f:MapBool.MapMap, g:MapInt.MapMap, P:SetQuestion.Set, k:int, a:real, b:real, Q:SetQuestion.Set, ghost counter_in:nat) : (r:(bool, nat))
  requires forall m | m in g.Model().Keys :: m.Keys == Q.Model()
  requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b

  requires forall candidates | candidates in groups.Model().Values ::
           forall key | key in candidates ::
           key.Keys <= Q.Model()

  requires forall candidates | candidates in groups.Model().Values ::
           forall key | key in candidates ::
           key in f.Model().Keys

  ensures r.1 == counter_in + 1
  ensures r.0 ==
          forall candidates | candidates in groups.Model().Values ::
          var f' := map key | key in candidates :: f.Model()[key];
          var g' := map key | key in candidates :: g.Model()[key];
          okFitness(f')













// * LA TRANSFORMACIÓN ES POLINÓMICA

function DATDP_to_PCDLim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>) :
(r:(map<map<Question, Answer>, bool>, map<map<Question, Answer>, int>, set<Question>, int, real, real, set<Question>))
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
{
  (fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
}

method {:verify false} method_DATDP_to_PCDLim(C:SetQA.Set, E:SetQA.Set, k:int, I:SetQuestion.Set, ghost counter_in:nat)   //(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>)
returns (r:(map<map<Question, Answer>, bool>, map<map<Question, Answer>, int>, set<Question>, int, real, real, set<Question>), ghost counter:nat)
  requires E.Model() <= C.Model()
  requires 0 <= k <= |I.Model()|
  requires (forall vehicle:map<Question, Answer> | vehicle in C.Model() :: vehicle.Keys == I.Model())
  ensures r == DATDP_to_PCDLim(C.Model(), E.Model(), k, I.Model())
  ensures counter <= (|E.Model()| + 1) * |C.Model()|
  //ensures counter <= (|E| + 2) * |C|
{
  counter := counter_in;
  var P:set<Question> := {};
  var a:real := 0.0;
  var b:real := 1.0;

  var f:map<map<Question, Answer>, bool> := map[];
  var g:map<map<Question, Answer>, int> := map[];

  var C2:SetQA.Set;
  C2, counter := C.Copy(counter);

  ghost var prev_C := C;
  ghost var prev_f := f;
  ghost var prev_C2 := C2;

  assert f.Keys == (C.Model() - C2.Model());
  assert prev_f.Keys <= f.Keys;
  assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];
  assert forall c | c in (C.Model() - C2.Model()) :: f[c] == (c in E.Model());
  assert prev_C == C;
  assert C2.Model() <= C.Model();

  assert counter == counter_in + C.sizeSet();

  while 0 < |C2.Model()|
  {
    ghost var prevCounter := counter;
    prev_C2 := C2;
    prev_f := f;
    counter := counter + 1;

    var c:map<Question, Answer>;
    //c, counter := C2.Pick(counter);

    //...
  }
  
  assume false;
}

function fitness1(C:set<map<Question, Answer>>, E:set<map<Question, Answer>>, I:set<Question>) : (f:map<map<Question, Answer>, bool>)
  requires E <= C
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  ensures f.Keys == C
  ensures forall vehicle:map<Question, Answer> | vehicle in C :: f[vehicle] == (vehicle in E)
{
  map vehicle | vehicle in C :: (vehicle in E)
}

function quantity1(C:set<map<Question, Answer>>, I:set<Question>) : (g:map<map<Question, Answer>, int>)
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  ensures g.Keys == C
  ensures forall vehicle:map<Question, Answer> | vehicle in C :: g[vehicle] == 1
{
  map candidate | candidate in C :: 1
}




}




















module Auxiliar {

// 1 - Tipos de datos, funciones y predicados auxiliares

// "Question" representa a las preguntas de PCD o a los tests de D-ATDP
// "Answer" representa a las respuestas de PCD o a los comportamientos de D-ATDP
datatype Question = CharacteristicQ(int)
datatype Answer = CharacteristicA(int) | T

// "Maybe" es usado en mapas de Question a Maybe<Answer> para poder representar preguntas que no han sido respondidas
datatype Maybe<T> = 
  | Nothing
  | Just(value: T)

// Selecciona un elemento de un conjunto
ghost function Pick<T>(s: set<T>) : (r:T)
  requires s != {}
  ensures r in s
{
  var x :| x in s; x
}

// Determina si se ha podido determinar correctamente si la IUT testeada es correcta
// Comprueba si las IUTs restantes son todas correctas o todas incorrectas
ghost predicate separatedSet(C:set<map<Question, Answer>>, E:set<map<Question, Answer>>)
{
  E == C || E == {}
  //(forall m:map<Question, Answer> | m in C :: m in E) || (forall m:map<Question, Answer> | m in C :: m !in E)
}

// Similar a separatedSet, pero en lugar de usar un conjunto de especificaciones correctas E usa un mapa de IUTs a bool
// Usado por D-ATDP-Intermediate
ghost predicate separatedMixed(C:set<map<Question, Answer>>, f:map<map<Question, Answer>, bool>)
  requires f.Keys == C
{
  (forall m:map<Question, Answer> | m in C :: f[m]) ||
  (forall m:map<Question, Answer> | m in C :: !f[m])
}

// Acota un conjunto de IUTs o candidatos a un subconjunto donde todos los candidatos responden o a la pregunta i (o lo equivalente con las IUTs)
ghost function restrictSet(C: set<map<Question, Answer>>, i: Question, o: Answer) : (C1: set<map<Question, Answer>>)
  requires forall c | c in C :: i in c.Keys
  ensures forall C2: set<map<Question, Answer>> | 
      C <= C2 && (forall c | c in C2 :: i in c.Keys) :: C1 <= (set m: map<Question, Answer> | m in C2 && m[i] == o :: m)
  ensures C1 <= C
{
  set m: map<Question, Answer> | m in C && m[i] == o :: m
}

// Acota un mapa cuyas llaves son IUTs o candidatos y sus valores tienen un tipo no determinado (puede ser bool para f o int para g)
// a un submapa donde todas las llaves son candidatos que responden o a la pregunta i (o lo equivalente con las IUTs)
ghost function restrictMap<T>(f:map<map<Question, Answer>, T>, i:Question, o:Answer) : (f1:map<map<Question, Answer>, T>)
  requires forall c | c in f.Keys :: i in c.Keys
{
  map m:map<Question, Answer> | m in f.Keys && m[i] == o :: f[m]
}

// Similar a separatedSet
// Comprueba si todos los valores del mapa f son iguales,
// en cuyo caso se únicamente quedarán candidatos aptos o candidatos no aptos en la población
ghost predicate okFitness(f:map<map<Question, Answer>, bool>)
{
  (forall b:bool | b in f.Values :: b == true) ||
  (forall b:bool | b in f.Values :: b == false)
}

// Similar a okFitness, pero utilizada por PCD-Parcial
// Determina si todos los valores del mapa están en un rango determinado
ghost predicate okFitnessPartial(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, Q:set<Question>, x:real, y:real)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires 0.0 <= x <= y <= 1.0
{
  var nC:real := nCandidates(g, Q) as real;
  var nF:real := nFit(f, g, Q) as real;
  if nC == 0.0 then
    true
  else
    x <= nF / nC <= y
}

// Comprueba que no se ha inferido más información privada que la permitida
ghost predicate okPrivate(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b
{
  forall i:Question | i in P ::
    var nC:real := nCandidates(g, Q) as real;
    var nP:real := nPrivate(g, Q, i, T) as real;
    if nC == 0.0 then
      true
    else
      a <= nP / nC <= b
}

// Devuelve el número de candidatos que quedan en la población
ghost function nCandidates(g:map<map<Question, Answer>, int>, Q:set<Question>) : (r:int)
  requires forall m | m in g.Keys :: m.Keys == Q
{
  if g.Keys == {} then
    0
  else
    var c:map<Question, Answer> := Pick(g.Keys);
    g[c] + nCandidates(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q
    )
}

// Dada una característica privada, devuelve el número de candidatos que la tienen
ghost function nPrivate(g:map<map<Question, Answer>, int>, Q:set<Question>, privateQuestion:Question, selectedAnswer:Answer) : (r:int)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires privateQuestion in Q
{
  if g.Keys == {} then
    0
  else
    var c:map<Question, Answer> := Pick(g.Keys);
    (if c[privateQuestion] == selectedAnswer then g[c] else 0) +
    nPrivate(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q, privateQuestion, selectedAnswer
    )
}

// Cuenta el número de candidatos aptos en una población
ghost function nFit(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, Q:set<Question>) : (r:int)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
{
  if g.Keys == {} then
    0
  else
    var c:map<Question, Answer> := Pick(g.Keys);
    (if f[c] then g[c] else 0) +
    nFit(
      (map m:map<Question, Answer> | m in f.Keys && m != c :: f[m]),
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q
    )
}

// Dada una entrevista y un mapa de preguntas a respuestas, determina si el mapa representa unas posibles respuestas a la entrevista
// Es decir, comprueba que todas las preguntas han sido respondidas y que no se ha respondido a ninguna pregunta no presente en la entrevista
ghost predicate answered(interview:set<Question>, answers:map<Question, Maybe<Answer>>, Q:set<Question>)
requires answers.Keys == Q
requires interview <= Q
{
  forall q | q in Q :: if q in interview then answers[q] != Nothing else answers[q] == Nothing
}

function fitness(C:set<map<Question, Answer>>, E:set<map<Question, Answer>>, I:set<Question>) : (f:map<map<Question, Answer>, bool>)
  requires E <= C
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  ensures f.Keys == C
  ensures forall vehicle:map<Question, Answer> | vehicle in C :: f[vehicle] == (vehicle in E)
{
  map vehicle | vehicle in C :: (vehicle in E)
}

function quantity(C:set<map<Question, Answer>>, I:set<Question>) : (g:map<map<Question, Answer>, int>)
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  ensures g.Keys == C
  ensures forall vehicle:map<Question, Answer> | vehicle in C :: g[vehicle] == 1
{
  map candidate | candidate in C :: 1
}

}














// * LA TRANSFORMACIÓN ES CORRECTA


abstract module Reduction {
  import opened Auxiliar
  import opened Problems



// D-ATDP ==> D-ATDP-Intermediate

ghost predicate {:opaque} PredDATDP(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>) {
  E <= C
  && 0 <= k <= |I|
  && (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  && DATDP(C, E, k, I)
}

lemma {:induction false} DATDPimpliesDATDPintermediate(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>)
  decreases k
  requires PredDATDP(C, E, k, I)
  ensures 
    reveal PredDATDP(); DATDPintermediate(C, fitness(C, E, I), k, I)
{
  if (k==0) {
    reveal PredDATDP();
    assert DATDPintermediate(C, fitness(C, E, I), k, I) by { reveal DATDPintermediate(); reveal DATDP(); }
  }
  else {
    assert E <= C by { reveal PredDATDP(); }
    assert 0 <= k <= |I| by { reveal PredDATDP(); }
    assert forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I by { reveal PredDATDP(); }
    assert DATDP(C, E, k, I) by {       
      reveal PredDATDP();
    }
    // Por definicion de DATDP(C, E, k, I), sé que existe un i :
    reveal DATDP();
    assert
      exists i:Question | i in I ::
        forall o:Answer | o in (set m:map<Question, Answer> | m in C :: m[i]) ::
          DATDP(
            restrictSet(C, i, o),
            restrictSet(E, i, o),
            k - 1,
            I
          )
    by {
      assert DATDP(C, E, k, I);
    }
    var i: Question :| i in I &&
      forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
        DATDP( restrictSet(C, i, o), restrictSet(E, i, o), k - 1, I);
    // Vamos a demostrar DATDPintermediate(C, fitness(C, E, I), k, I) usando dicho i
    forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i])
      ensures DATDPintermediate(restrictSet(C, i, o), restrictMap(fitness(C, E, I), i, o),k - 1, I){

      var C1 := restrictSet(C, i, o);
      var E1 := restrictSet(E, i, o);

      assert PredDATDP(C1, E1, k - 1, I) by { reveal PredDATDP(); }

      DATDPimpliesDATDPintermediate(C1, E1, k - 1, I);

      assert DATDPintermediate(C1, fitness(C1, E1, I), k-1, I); 
      assert fitness(C1, E1, I) == restrictMap(fitness(C, E, I), i, o);
      assert DATDPintermediate(restrictSet(C, i, o),restrictMap(fitness(C, E, I), i, o),k - 1, I);
    }
    assert DATDPintermediate(C, fitness(C, E, I), k, I) by { reveal DATDPintermediate();}
  }
}


// D-ATDP <== D-ATDP-Intermediate


ghost function correctSpecifications(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, I:set<Question>) : (E: set<map<Question, Answer>>)
  requires f.Keys == C
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  ensures E <= C
  ensures forall vehicle:map<Question, Answer> | vehicle in C :: f[vehicle] == (vehicle in E)
{
  set candidate | candidate in f.Keys && (f[candidate]) :: candidate
}

ghost predicate {:opaque} PredDATDPintermediate(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, k: int, I: set<Question>) {
  f.Keys == C
  && 0 <= k <= |I|
  && (forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  && DATDPintermediate(C, f, k, I)
}

lemma {:induction false} DATDPintermediateimpliesDATDP(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, k: int, I: set<Question>)
  decreases k
  requires PredDATDPintermediate(C, f, k, I)
  ensures 
    reveal PredDATDPintermediate(); DATDP(C, correctSpecifications(C, f, I), k, I)
{
  if (k==0) {
    reveal PredDATDPintermediate();
    assert DATDP(C, correctSpecifications(C, f, I), k, I) by { reveal DATDP(); reveal DATDPintermediate(); }
  }
  else {
    assert f.Keys == C by { reveal PredDATDPintermediate(); }
    assert 0 <= k <= |I| by { reveal PredDATDPintermediate(); }
    assert (forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I) by { reveal PredDATDPintermediate(); }
    assert DATDPintermediate(C, f, k, I) by {       
      reveal PredDATDPintermediate();
    }
    // Por definicion de DATDPintermediate(C, E, k, I), sé que existe un i :
    reveal DATDPintermediate();
    var i: Question :| i in I &&
      forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
        DATDPintermediate( restrictSet(C, i, o), restrictMap(f, i, o), k - 1, I);
    // Vamos a demostrar DATDP(C, correctSpecifications(C, f, I), k, I) usando dicho i
    forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i])
      ensures DATDP(restrictSet(C, i, o), restrictSet(correctSpecifications(C, f, I), i, o), k - 1, I) {
        
      var C1 := restrictSet(C, i, o);
      var f1 := restrictMap(f, i, o);

      assert PredDATDPintermediate(C1, f1, k - 1, I) by { reveal PredDATDPintermediate(); }
      DATDPintermediateimpliesDATDP(C1, f1, k - 1, I);

      assert correctSpecifications(C1, f1, I) == restrictSet(correctSpecifications(C, f, I), i, o) by { reveal PredDATDPintermediate(); reveal DATDPintermediate(); }

      assert DATDP(restrictSet(C, i, o), restrictSet(correctSpecifications(C, f, I), i, o), k - 1, I); 

      reveal DATDP();
      reveal DATDPintermediate();
      reveal PredDATDPintermediate();
    }
    assert DATDP(C, correctSpecifications(C, f, I), k, I) by { reveal DATDP(); }
  }
}



// ATDP-Intermediate ==> PCD-Limit

lemma {:induction false} DATDPintermediateImpliesPCDLim(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>,k: int, I: set<Question>)
  decreases k
  requires PredDATDPintermediate(C, f, k, I)
  ensures 
    reveal PredDATDPintermediate(); PCDLim(f, quantity(C, I), {}, k, 0.0, 1.0, I)
{
  if (k==0) {
    reveal PredDATDPintermediate();
    assert PCDLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) by { reveal DATDPintermediate(); reveal PCDLim(); }
  }
  else {
    assert f.Keys == C by { reveal PredDATDPintermediate(); }
    assert 0 <= k <= |I| by { reveal PredDATDPintermediate(); }
    assert (forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I) by { reveal PredDATDPintermediate(); }
    assert DATDPintermediate(C, f, k, I) by { reveal PredDATDPintermediate(); }
    assert okPrivate(f, quantity(C, I), {}, 0.0, 1.0, I);

    if (okFitness(f)) {
      // Si okFitness(f), PCDLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) es trivialmente cierto
    }
    else {
      //Por definicion de DATDPintermediate(C, f, k, i), sé que existe un i :
      reveal DATDPintermediate();
      var i: Question :| i in I &&
        forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
          DATDPintermediate(restrictSet(C, i, o), restrictMap(f, i, o), k - 1, I);
      // Vamos a demostrar PCDLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) usando dicho i
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) 
      ensures PCDLim(restrictMap(f, i, o), restrictMap(quantity(C, I), i, o), {}, k - 1, 0.0, 1.0, I)
      {
        var C1 := restrictSet(C, i, o);
        var f1 := restrictMap(f, i, o);

        assert PredDATDPintermediate(C1, f1, k - 1, I) by { reveal PredDATDPintermediate(); }
        DATDPintermediateImpliesPCDLim(C1,f1,k-1,I);
        assert PCDLim(f1, quantity(C1, I),{},k-1, 0.0, 1.0, I);

        assert restrictMap(quantity(C, I), i, o) == quantity(C1, I);
      }
    }
    assert PCDLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) by { reveal PCDLim(); }
  }
}


// DATDP-Intermediate <== PCDLimit


ghost predicate {:opaque} PredPCDLim(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>) {
  (forall m | m in g.Keys :: m.Keys == Q)
  && f.Keys == g.Keys
  && P <= Q
  && 0.0 <= a <= b <= 1.0
  && 0 <= k <= |Q|
  && PCDLim(f, g, P, k, a, b, Q)
}

// Todas las instancias de D-ATDP-intermediate en las que separatedMixed() es cierto son ciertas
lemma separationPersists(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, k: int, I: set<Question>)
  decreases k
  requires f.Keys == C
  requires 0 <= k <= |I|
  requires forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I
  requires separatedMixed(C, f)
  ensures DATDPintermediate(C, f, k, I)
{
  if (k == 0) {
    // Caso base trivial
    reveal DATDPintermediate();
  }
  else if (C == {}) {
    // Caso particular trivial
    reveal DATDPintermediate();
  }
  else {
    // Si ya se ha conseguido distinguir a las IUTs correctas de las incorrectas, cualquier subconjunto formado tras acotar la población a las IUTs que tienen la acción "o" frente al test "i" estará distinguiendo también a las IUTs
    assert forall i: Question | i in I ::
      forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
        separatedMixed(restrictSet(C, i, o), restrictMap(f, i, o)) by { reveal DATDPintermediate(); }
    // Hipótesis inductiva: asumimos que separationPersists(restrictSet(C, i, o), restrictMap(f, i, o), k-1, I) se cumple
    // De la hipótesis, podemos deducir:
    assert forall i: Question | i in I ::
      forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
        DATDPintermediate(restrictSet(C, i, o), restrictMap(f, i, o), k-1, I) by { 
          var i :| i in I;
          assert forall m | m in C :: i in m.Keys;
          var o :| o in (set m: map<Question, Answer> | m in C :: m[i]);
          separationPersists(restrictSet(C, i, o), restrictMap(f, i, o), k-1, I);
    }
    // Hemos encaminado lo suficiente al verificador para que pueda deducir que DATDPintermediate(C, f, k, I) es cierto
    assert DATDPintermediate(C, f, k, I) by { reveal DATDPintermediate(); }
  }
}

lemma {:induction false} PCDLimImpliesDATDPintermediate(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  decreases k
  requires PredPCDLim(f, g, P, k, a, b, Q)
  requires P == {}
  ensures 
    reveal PredPCDLim(); DATDPintermediate(g.Keys, f, k, Q)
{
  if (k==0) {
    reveal PredPCDLim();
    assert forall m:map<Question, Answer> | m in f.Keys :: f[m] in f.Values;
    assert separatedMixed(g.Keys, f) == okFitness(f);
    assert DATDPintermediate(g.Keys, f, k, Q) by { reveal PCDLim(); reveal DATDPintermediate(); }
  }
  else {
    assert  (forall m | m in g.Keys :: m.Keys == Q)
            && f.Keys == g.Keys
            && P <= Q
            && 0.0 <= a <= b <= 1.0
            && 0 <= k <= |Q| by { reveal PredPCDLim(); }
    assert PCDLim(f, g, P, k, a, b, Q) by {
      reveal PredPCDLim();
    }
    assert okPrivate(f, g, P, 0.0, 1.0, Q);
    
    if (okFitness(f)) {
      // Vamos a demostrar que okFitness(f) implica separatedMixed(g.Keys, f)
      var C := g.Keys;
      reveal PredPCDLim();
      assert f.Keys == C;
      assert forall m:map<Question, Answer> | m in f.Keys :: f[m] in f.Values;
      assert (forall m:map<Question, Answer> | m in C :: f[m]) || (forall m:map<Question, Answer> | m in C :: !f[m]);
      assert separatedMixed(C, f);
      // Todas las instancias de D-ATDP-intermediate en las que separatedMixed() es cierto son ciertas
      separationPersists(C, f, k, Q);
      // Por lo tanto, DATDPintermediate(g.Keys, f, k, Q) es cierto
    }
    else {
      //Por definicion de PCDLim(f, g, P, k, a, b, Q), sé que existe un i :
      reveal PCDLim();
      var i: Question :| i in Q &&
        forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
          PCDLim(
            restrictMap(f, i, o),
            restrictMap(g, i, o),
            P, k - 1, a, b, Q
          );
      // Vamos a demostrar DATDPintermediate(g.Keys, f, k, Q) usando dicho i
      forall o: Answer | o in (set m: map<Question, Answer> | m in g.Keys :: m[i])
      ensures DATDPintermediate(restrictSet(g.Keys, i, o), restrictMap(f, i, o), k - 1, Q)
      {
        var f1 := restrictMap(f, i, o);
        var g1 := restrictMap(g, i, o);

        assert PredPCDLim(f1, g1, P, k - 1, a, b, Q) by { reveal PredPCDLim(); }
        PCDLimImpliesDATDPintermediate(f1, g1, P, k - 1, a, b, Q);
        assert DATDPintermediate(g1.Keys, f1, k - 1, Q);

        assert restrictSet(g.Keys, i, o) == g1.Keys;
      }
    }
    assert DATDPintermediate(g.Keys, f, k, Q) by { reveal DATDPintermediate(); }
  }
}


// DATDP reduces to PCD-Limit


lemma DATDPreducesToPCDLim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>)
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  ensures DATDP(C, E, k, I) == PCDLim(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
{
  reveal PredDATDP();
  reveal PredDATDPintermediate();
  reveal PredPCDLim();
  if (DATDP(C, E, k, I)) {
    DATDPimpliesDATDPintermediate(C, E, k, I);
    assert DATDPintermediate(C, fitness(C, E, I), k, I);
    DATDPintermediateImpliesPCDLim(C, fitness(C, E, I), k , I);
  }
  else if PCDLim(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I) {
    PCDLimImpliesDATDPintermediate(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I);
    assert DATDPintermediate(quantity(C, I).Keys, fitness(C, E, I), k, I);
    assert C == quantity(C, I).Keys;
    DATDPintermediateimpliesDATDP(C, fitness(C, E, I), k, I);
    assert DATDP(C, correctSpecifications(C, fitness(C, E, I), I), k, I);

    assert correctSpecifications(C, fitness(C, E, I), I) == E by {
      reveal DATDPintermediate();
      assert correctSpecifications(C, fitness(C, E, I), I) == set candidate | candidate in fitness(C, E, I).Keys && (fitness(C, E, I)[candidate]) :: candidate;
      assert (set candidate | candidate in fitness(C, E, I).Keys && (fitness(C, E, I)[candidate]) :: candidate)
          == (set candidate | candidate in fitness(C, E, I).Keys && candidate in E :: candidate);
      assert forall candidate | candidate in fitness(C, E, I).Keys :: candidate in C;
      assert (set candidate | candidate in fitness(C, E, I).Keys && candidate in E :: candidate)
          == (set candidate | candidate in E :: candidate);
    }

    assert DATDP(C, E, k, I);
  }
}


}