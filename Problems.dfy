include "Auxiliary.dfy"

abstract module Problems {
  import opened Auxiliary
  
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
  okPrivate(g, P, a, b, Q) &&
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

