include "Auxiliary.dfy"
include "Problems.dfy"
include "Types.dfy"
include "Reduction.dfy"

abstract module PCD {
  import opened Problems
  import opened TypeMod

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

