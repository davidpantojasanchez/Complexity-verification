include "Auxiliary.dfy"
include "Problems.dfy"
include "Types.dfy"
include "Reduction.dfy"

abstract module PCD {
  import opened Auxiliary
  import opened Problems
  import opened TypeMod

  // * LA VERIFICACIÓN DE PCDLim ES POLINÓMICA


  // Para todas las formas válidas de responder a las preguntas de la entrevista / grupos de tipos de candidatos
  // (<= |f.Keys|), ver si la población restante es apta y/o infiere información privada
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
    assert counter <= counter_in + 3*poly(f,g,P) by {
      assert counter == counter_in + f.Size() + 2;
      assert f.Size() <= poly(f,g,P);
    }
    var i:nat := 0;
    if candidates_empty != true {
      assert candidates.Model() <= f.Model().Keys;
      assert candidates_empty == (candidates.Model() == {});
      assert forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys;
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i);
      assert i == |f.Model().Keys| - |candidates.Model()|;
    }
    else {
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i);
    }
    while candidates_empty != true
      decreases |candidates.Model()|
      invariant candidates.Model() <= f.Model().Keys
      invariant candidates_empty == (candidates.Model() == {})
      invariant forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys
      invariant i == |f.Model().Keys| - |candidates.Model()|

      //invariant counter == counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i
      invariant counter <= counter_in + poly(f,g,P)*(3 + 7*i)
    {
      ghost var candidates_ := candidates;
      candidates, candidates_empty, i, R, counter := inner_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, i, counter_in, counter, R);
      assert i == |f.Model().Keys| - |candidates.Model()| by {
        assert postcondition(f, g, P, Q, candidates_, candidates, candidates_empty, i);
        assert   (candidates.Model() <= f.Model().Keys)
              && (candidates_empty == (candidates.Model() == {}))
              && (forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys)
              && (|candidates.Model()| == |candidates_.Model()| - 1)
              && (i == |f.Model().Keys| - |candidates.Model()|);
        assert i == |f.Model().Keys| - |candidates.Model()|;
      }
    }
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i);
  }

  }






method inner_loop
(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>,
candidates_:SetMap<Question, Answer>, i_:nat, ghost counter_in:nat, ghost counter_:nat, R':bool)
returns (candidates:SetMap<Question, Answer>, candidates_empty:bool, i:nat, R:bool, ghost counter:nat)

  requires forall m | m in f.Model().Keys :: m.Keys == Q.Model()
  requires f.Model().Keys == g.Model().Keys
  requires P.Model() <= Q.Model()
  requires 0.0 <= a <= b <= 1.0
  requires 0 <= k <= |Q.Model()|
  requires questionsToVerify.Model() <= Q.Model()

  requires candidates_.Model() <= f.Model().Keys
  requires candidates_.Model() != {}
  requires forall candidate | candidate in candidates_.Model() :: Q.Model() == candidate.Keys
  requires counter_ <= counter_in + poly(f,g,P)*(3 + 7*i_)
  requires i_ == |f.Model().Keys| - |candidates_.Model()|
  
  //ensures candidates.Model() <= f.Model().Keys
  //ensures candidates_empty == (candidates.Model() == {})
  //ensures forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys
  //invariant i == |f.Model().Keys| - |candidates.Model()|
  ensures postcondition(f, g, P, Q, candidates_, candidates, candidates_empty, i) && counter <= counter_in + poly(f,g,P)*(3 + 7*i)
{
  counter := counter_;
  candidates := candidates_;
  i := i_;
  candidates_empty := false;
  R := R';

  var candidate:Map<Question, Answer>;
  candidate, counter := candidates.Pick(counter);
  var answers:Map<Question, Answer>;

  var f':MapMap<Question, Answer, bool>;
  var g':MapMap<Question, Answer, int>;
  
  f', counter := those_who_would_answer_the_same(f, candidate, questionsToVerify, counter);
  g', counter := those_who_would_answer_the_same(g, candidate, questionsToVerify, counter);

  //assert counter == (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i) + candidates.maximumSizeElements() + f.Size() + g.Size();
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 3) by {
    assert counter <= (counter_in + poly(f,g,P)*(3 + 7*i)) + candidates.maximumSizeElements() + f.Size() + g.Size();
    assert candidates.maximumSizeElements() <= poly(f,g,P);
    assert counter <= (counter_in + poly(f,g,P)*(3 + 7*i)) + 3*poly(f,g,P);
  }
  var okFit:bool;
  var okPriv:bool;
  okFit, counter := okFitnessMethod(f', counter);
  okPriv, counter := okPrivateMethod(g', P, a, b, Q, counter);
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) by {
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 3) + f'.Size() + g'.Size();
    assert f'.Size() <= poly(f,g,P) && g'.Size() <= poly(f,g,P) by {
      assert f'.Size() <= f.Size() by {
        assert f.Size() == |f.Model()|*f.maximumSizeElements();
        assert f'.Size() == |f'.Model()|*f'.maximumSizeElements();
        assert f.maximumSizeElements() == f'.maximumSizeElements();
        assert |f'.Model()| <= |f.Model()|;
        mult_preserves_order(|f'.Model()|, f'.maximumSizeElements(), |f.Model()|, f.maximumSizeElements());
      }
      assert g'.Size() <= g.Size() by {
        assert g.Size() == |g.Model()|*g.maximumSizeElements();
        assert g'.Size() == |g'.Model()|*g'.maximumSizeElements();
        assert g.maximumSizeElements() == g'.maximumSizeElements();
        assert |g'.Model()| <= |g.Model()|;
        mult_preserves_order(|g'.Model()|, g'.maximumSizeElements(), |g.Model()|, g.maximumSizeElements());
      }
    }
  }
  // aux = counter_in + poly(f,g,P)*(3 + 7*i + 5)
  ghost var candidates' := candidates;
  R := R && okFit && okPriv;
  assert candidate.Model() in candidates.Model();
  candidates, counter := candidates.Remove(candidate, counter);
  //assert i == |f.Model().Keys| - |candidates.Model()| - 1;
  //     if e.Model() !in Model() then |R.Model()| == |Model()| else |R.Model()| == |Model()| - 1

  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 6) by {
    assert candidates.Size() <= candidates'.Size() by {
      assert if candidate.Model() !in candidates'.Model() then |candidates.Model()| == |candidates'.Model()| else |candidates.Model()| == |candidates'.Model()| - 1;
      assert candidates'.Size() == |candidates'.Model()|*candidates'.maximumSizeElements();
      assert candidates.Size() == |candidates.Model()|*candidates'.maximumSizeElements() by {
        assert candidates.Size() == |candidates.Model()|*candidates.maximumSizeElements();
        assert candidates.maximumSizeElements() == candidates'.maximumSizeElements();
      }
      assert |candidates.Model()| <= |candidates'.Model()|;
      mult_preserves_order(|candidates.Model()|, candidates'.maximumSizeElements(), |candidates'.Model()|, candidates'.maximumSizeElements());
      assert |candidates.Model()|*candidates'.maximumSizeElements() <= |candidates'.Model()|*candidates'.maximumSizeElements();
    }
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) + candidates'.Size();

    assert candidates'.Size() <= poly(f,g,P) by {
      assert candidates'.Size() <= f.Size() by {
        assert candidates'.Model() <= f.Model().Keys;

        assert candidates'.Size() == |candidates'.Model()|*candidates'.maximumSizeElements();
        assert f.Size() == |f.Model()|*f.maximumSizeElements();

        assert |candidates'.Model()| <= |f.Model()| by {
          assert candidates_.Model() <= f.Model().Keys;
          assert candidates'.Model() <= f.Model().Keys;
          smallerSetLessCardinality(candidates'.Model(), f.Model().Keys);
          assert |candidates'.Model()| <= |f.Model().Keys|;
        }
        assert candidates'.maximumSizeElements() <= f.maximumSizeElements();
        mult_preserves_order(|candidates'.Model()|, candidates'.maximumSizeElements(), |f.Model()|, f.maximumSizeElements());
      }
      assert f.Size() <= poly(f,g,P);
    }

    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) + poly(f,g,P);
  }

  candidates_empty, counter := candidates.Empty(counter);
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 7);
  //assert counter == (counter_in + f.Size() + 2 + (candidates.maximumSizeElements() + 2*f.Size() + 2*g.Size() + candidates.Size() + 1)*i) + candidates.maximumSizeElements() + f.Size() + g.Size() + f'.Size() + g'.Size() + candidates.Size() + 1;
  
  //assert i == |f.Model().Keys| - |candidates.Model()| - 1;
  ghost var i' := i;
  i := i + 1;
  //assert i == |f.Model().Keys| - |candidates.Model()|;

  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i) by {
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*(i-1) + 7) by {
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i' + 7);
      assert i' == i-1;
      basic_math_2(counter_in, poly(f,g,P), i, i');
    }

    ghost var polynomial := poly(f,g,P);
    assert polynomial*(3 + 7*(i-1) + 7) == polynomial*(3 + 7*i) by {
      basic_math(i, polynomial);
      assert polynomial*(3 + 7*(i-1) + 7) == polynomial*(3 + 7*i);
    }

  }

  //assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) by {

  assert postcondition(f, g, P, Q, candidates_, candidates, candidates_empty, i) by {
    reveal postcondition();
    assert candidates.Model() <= f.Model().Keys;
    assert candidates_empty == (candidates.Model() == {});
    assert forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys;
    assert |candidates.Model()| == |candidates_.Model()| - 1;
    assert i == |f.Model().Keys| - |candidates.Model()|;
  }

  assert postcondition(f, g, P, Q, candidates_, candidates, candidates_empty, i) && (counter <= counter_in + poly(f,g,P)*(3 + 7*i));
  assume false;
}






function poly(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>):(R:nat)   // {:opaque}
ensures R >= f.Size()
ensures R >= g.Size()
ensures R >= P.Size()
ensures R >= |f.Model().Keys|
ensures R >= |g.Model().Keys|
ensures R >= |f.Model().Values|
ensures R >= |g.Model().Values|
ensures R >= 1


ghost predicate postcondition(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, Q:Set<Question>, candidates_:SetMap<Question, Answer>, candidates:SetMap<Question, Answer>, candidates_empty:bool, i:nat) { //{:opaque}
     (candidates.Model() <= f.Model().Keys)
  && (candidates_empty == (candidates.Model() == {}))
  && (forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys)
  && (|candidates.Model()| == |candidates_.Model()| - 1)
  && (i == |f.Model().Keys| - |candidates.Model()|)
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
  ensures |f'.Model()| <= |f.Model()|
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


lemma basic_math(i:nat, a:nat)
  ensures a*(3 + 7*(i-1) + 7) == a*(3 + 7*i)
  {}

lemma basic_math_2(counter_in:nat, poly:nat, i:nat, i':nat)
  requires i == i'+1
  ensures counter_in + poly*(3 + 7*i' + 7) == counter_in + poly*(3 + 7*(i-1) + 7)
  {
    assert 7*i' == 7*(i-1);
  }

lemma smallerSetLessCardinality<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
  {
    if (A == {}) {
    }
    else {
      var a :| a in A && a in B;
      smallerSetLessCardinality(A - {a}, B - {a});
    }
  }


}

