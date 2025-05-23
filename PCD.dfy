include "Auxiliary.dfy"
include "Problems.dfy"
include "Types.dfy"
include "Reduction.dfy"

abstract module PCD {
  import opened Auxiliary
  import opened Problems
  import opened TypeMod

  // * LA VERIFICACIÓN DE PCDLim ES POLINÓMICA

  method verifyPCD//(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    (f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>, ghost counter_in:nat)
    returns (R:bool, ghost counter:nat)
  requires forall m | m in f.Model().Keys :: m.Keys == Q.Model()
  requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= b <= 1.0
  requires 0 <= k <= |Q.Model()|
  requires questionsToVerify.Model() <= Q.Model()
  /*
  ensures |questionsToVerify.Model()| <= k &&
          forall answers:map<Question, Answer> | answers.Keys == questionsToVerify.Model() ::                              // para todas las formas de responder a la entrevista...
          (
          var f' := map candidate:map<Question, Answer> | candidate in f.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == answers[q]) :: f.Model()[candidate];
          var g' := map candidate:map<Question, Answer> | candidate in g.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == answers[q]) :: g.Model()[candidate];
          okFitness(f') && okPrivate(f', g', P.Model(), a, b, Q.Model())
          )
  */
  // Para todas las formas válidas de responder a las preguntas de la entrevista / grupos de tipos de candidatos
  // (<= |f.Keys|), ver si la población restante es apta y/o infiere información privada
  {
  counter := counter_in;
  R := false;
  var nQuestions:int;
  nQuestions, counter := questionsToVerify.Cardinality(counter);
  if nQuestions <= k {
    R := true;
    var candidates:SetMap<Question, Answer>;
    var candidates_empty:bool;
    candidates, counter := f.Keys(counter);
    candidates_empty, counter := candidates.Empty(counter);
    var groups:Map_Map_SetMap<Question, Answer>;
    assert counter == counter_in + f.Size() + 2;
    var i:int := 0;
    while candidates_empty != true
      decreases |candidates.Model()|
      invariant candidates_empty == (candidates.Model() == {})
      invariant forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys
      invariant counter == counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i
    {
      var candidate:Map<Question, Answer>;
      candidate, counter := candidates.Pick(counter);
      var answers:Map<Question, Answer>;

      var f':MapMap<Question, Answer, bool>;
      var g':MapMap<Question, Answer, int>;
      
      f', counter := those_who_would_answer_the_same(f, candidate, questionsToVerify, counter);
      g', counter := those_who_would_answer_the_same(g, candidate, questionsToVerify, counter);

      assert counter == (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i) + candidates.maximumSizeElements() + f.Size() + g.Size();

      var okFit:bool;
      var okPriv:bool;
      okFit, counter := okFitnessMethod(f', counter);
      okPriv, counter := okPrivateMethod(g', P, a, b, Q, counter);

      assert counter == (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i)
                        + candidates.maximumSizeElements() + f.Size() + g.Size() + f'.Size() + g'.Size();
      ghost var aux := (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i)
                        + candidates.maximumSizeElements() + f.Size() + g.Size() + f'.Size() + g'.Size();
      assert counter == aux;
      R := R && okFit && okPriv;
      candidates, counter := candidates.Remove(candidate, counter);
      assume false;
      assert counter == aux + candidates.Size();
      candidates_empty, counter := candidates.Empty(counter);

      assert counter == (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i)
                        + candidates.maximumSizeElements() + f.Size() + g.Size() + f'.Size() + g'.Size() + candidates.Size() + 1;
      i := i + 1;
      assume false;
    }
  }

  }


method Restrict(S:Map, s:Set, ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
    requires s.Model() <= S.Model().Keys
    ensures counter_out == counter_in + S.Size()
    ensures R.Model().Keys == s.Model()
    ensures forall key | key in R.Model().Keys :: R.Model()[key] == S.Model()[key]
    ensures forall i | i in R.Model().Items :: i in S.Model().Items
  

method those_who_would_answer_the_same<T>(f:MapMap<Question, Answer, T>, candidate:Map<Question, Answer>, questionsToVerify:Set<Question>, ghost counter_in:nat)
returns (f':MapMap<Question, Answer, T>, counter_out:nat)
  requires  forall person:map<Question, Answer> | person in f.Model().Keys ::
              (person.Keys == candidate.Model().Keys)
  requires  questionsToVerify.Model() <= candidate.Model().Keys
  ensures   forall person:map<Question, Answer> | person in f.Model().Keys ::
              if (forall q | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q])
                then (person in f'.Model().Keys && f'.Model()[person] == f.Model()[person])
              else (person !in f.Model().Keys)
  ensures f'.Model().Keys <= f.Model().Keys
  ensures counter_out == counter_in + f.Size()


method okFitnessMethod(f:MapMap<Question, Answer, bool>, ghost counter_in:nat) returns (R:bool, ghost counter_out:nat)
  ensures R == okFitness(f.Model())
  ensures counter_out == counter_in + f.Size()


method okPrivateMethod(g:MapMap<Question, Answer, int>, P:Set<Question>, a:real, b:real, Q:Set<Question>, ghost counter_in:nat) returns (R:bool, ghost counter_out:nat)
  requires forall m | m in g.Model().Keys :: m.Keys == Q.Model()
  //requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b
  ensures R == okPrivate(g.Model(), P.Model(), a, b, Q.Model())
  ensures counter_out == counter_in + g.Size()


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


      /*
      answers, counter := Restrict(candidate, questionsToVerify, counter) by {   // forma de responder a las preguntas de la entrevista
        assert questionsToVerify.Model() <= Q.Model();
        assert forall m | m in f.Model().Keys :: m.Keys == Q.Model();
        assert forall m | m in candidates.Model() :: m.Keys == Q.Model();
        assert candidate.Model() in candidates.Model();
        assert candidates.Model() <= f.Model().Keys;
        assert candidate.Model() in f.Model().Keys;
        assert candidate.Model().Keys == Q.Model();
        assert questionsToVerify.Model() <= candidate.Model().Keys;
      }
      
      var hasKey:bool;
      hasKey, counter := groups.HasKey(answers, counter);

      var setCandidates:SetMap<Question, Answer>;
      if hasKey {
        setCandidates, counter
      }
      else {
        setCandidates, counter := setCandidates.Add(candidate, counter);
        groups, counter := groups.Add(answers, setCandidates, counter);
      }
      */

}

