
module Auxiliary {

// 1 - Tipos de datos, funciones y predicados auxiliares

// "Question" representa a las preguntas de PCD o a los tests de D-ATDP
// "Answer" representa a las respuestas de PCD o a los comportamientos de D-ATDP
datatype Question = CharacteristicQ(int)
datatype Answer = CharacteristicA(int) | T

datatype Interview = Empty | Node ( Key:Question, Children:map<Answer, Interview>)

predicate correctSizeInterview(i:Interview, k:int)  // redundante con "correctQuestionsInterview", pero ayuda tenerlo separado
{
  if k == -1 then
    false
  else
  match i
    case Empty => true
    case Node (_, children) => forall child:Interview | child in children.Values :: correctSizeInterview(child, k-1)
}

predicate correctQuestionsInterview(i:Interview, k:int, Q:set<Question>)
{
  if k == -1 then
    false
  else
  match i
    case Empty => true
    case Node (key, children) => key in Q && forall child:Interview | child in children.Values :: correctQuestionsInterview(child, k-1, Q)
}

predicate correctAnswersInterview(i:Interview, k:int, A:set<Answer>)
{
  if k == -1 then
    false
  else
  match i
    case Empty => true
    case Node (key, children) => children.Keys == A && forall child:Interview | child in children.Values :: correctAnswersInterview(child, k-1, A)
}


lemma subinterviewsSmaller(interview:Interview, k:int)
requires correctSizeInterview(interview, k)
ensures match interview
  case Empty => true
  case Node (_, children) => forall child:Interview | child in children.Values :: correctSizeInterview(child, k-1)
{
}

predicate isPath(interview:Interview, k:int, path:set<Question>)
requires correctSizeInterview(interview, k)
{
  match interview
  case Empty => path=={}
  case Node (key, children) =>
    (key in path) &&
    (exists child:Interview | child in children.Values :: isPath(child, k-1, path - {key}))
}


ghost function pathsInterview(interview:Interview, k:int, Q:set<Question>) : (paths:set<set<Question>>)
decreases k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
requires k>=0
ensures forall path | path in paths :: (forall q | q in path :: q in Q)
{
  assert (k == 0) ==> ((interview == Empty) ||  |interview.Children|==0) by {
    if (k == 0) && !(interview == Empty) && !(|interview.Children|==0) {
      assert correctSizeInterview(interview, k) ==
             (forall child:Interview | (child in interview.Children.Values) :: correctSizeInterview(child, k-1));
      assert correctSizeInterview(interview, k) ==
             (forall child:Interview | (child in interview.Children.Values) :: correctSizeInterview(child, -1));
      assert correctSizeInterview(interview, k) ==
             (forall child:Interview | (child in interview.Children.Values) :: false);
      assert !correctSizeInterview(interview, k);
    }
  }
  match interview
  case Empty => {}
  case Node (key, children) =>
    if |interview.Children|==0 then {} else
    union (set child:Interview | child in children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset)) //pathsInterviewPlusElement(child, k-1, interview.Key))
}

ghost function pathsInterviewPlusElement(interview:Interview, k:int, e:Question, Q:set<Question>) : (paths:set<set<Question>>)
decreases k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
requires k>=0
requires e in Q
ensures forall path | path in paths :: (forall q | q in path :: q in Q)
{
  (set subset:set<Question> | subset in pathsInterview(interview, k, Q) :: {e} + subset)
}


ghost function union(S: set<set<set<Question>>>): (r:set<set<Question>>)
  ensures forall x | x in r :: (exists s | s in S :: x in s)
  ensures forall s | s in S :: (forall q | q in s :: q in r)


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
ghost predicate okPrivate(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  //requires f.Keys == g.Keys
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


lemma mult_preserves_order(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{
}


}



