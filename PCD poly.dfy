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
  
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

  ensures counter_is_polynomial(f, g, P, counter_in, counter)
  ensures R == verification(f, g, P, k, a, b, Q, questionsToVerify)
  /*
  ensures |questionsToVerify.Model()| <= k &&
          forall person:map<Question, Answer> | person.Keys == questionsToVerify.Model() ::                              // para todas las formas de responder a la entrevista...
          (
          var f' := map candidate:map<Question, Answer> | candidate in f.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == person[q]) :: f.Model()[candidate];
          var g' := map candidate:map<Question, Answer> | candidate in g.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == person[q]) :: g.Model()[candidate];
          okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
          )
  */
  /*
  ensures reveal problem_requirements();
    R == (|questionsToVerify.Model()| <= k) &&
    (forall person:map<Question, Answer> | person in f.Model().Keys ::                                                   // para todos los posibles entrevistados que pueden responder la entrevista...
    (
      var f' := map candidate:map<Question, Answer> | candidate in f.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == person[q]) :: f.Model()[candidate];
      var g' := map candidate:map<Question, Answer> | candidate in g.Model().Keys && (forall q:Question | q in candidate.Keys :: candidate[q] == person[q]) :: g.Model()[candidate];
      okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
    ))
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
      assert forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys by { reveal problem_requirements(); }
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i);
      assert i == |f.Model().Keys| - |candidates.Model()|;
    }
    else {
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i);
    }
    assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) && counter_loop(f, g, P, i, counter_in, counter) by {
      reveal invariant_loop(); reveal counter_loop();
    }

    //assert verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R) by { reveal verification_loop(); reveal problem_requirements(); }

    while candidates_empty != true
      decreases |candidates.Model()|
      invariant invariant_loop(f, g, P, Q, candidates, candidates_empty, i)
      invariant counter_loop(f, g, P, i, counter_in, counter)
      
      invariant reveal problem_requirements();
        R == (forall candidate:map<Question, Answer> | candidate in (f.Model() - candidates.Model()) :: 
        (
          var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
          var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
          okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
        ))
      //invariant verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
    {
      ghost var R_ := R;
      ghost var candidates_ := candidates;

      assert R_ == (forall candidate:map<Question, Answer> | candidate in (f.Model() - candidates_.Model()) ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
      )) by {
        reveal problem_requirements();
        reveal verification_loop();
      }

      candidates, candidates_empty, i, R, counter := body_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, candidates_empty, i, counter_in, counter, R) by {
        reveal problem_requirements();
        reveal invariant_loop();
        reveal no_termination_body();
      }
      assert |candidates.Model()| < |candidates_.Model()| by { reveal decreases_body(candidates_, candidates); }
      assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) by { reveal problem_requirements(); reveal invariant_loop(); }
      assert counter_loop(f, g, P, i, counter_in, counter) by { reveal problem_requirements(); reveal counter_loop(); }
      
      //assume false;
      assert R == (R_ && forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
      )) by {
        reveal problem_requirements();
        reveal verification_body();
        reveal invariant_loop();
        assert verification_body(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates, R_, R);
      }



      assume false;
    }
    assert counter <= counter_in + 10*poly(f,g,P)*poly(f,g,P) by {
      assert counter <= counter_in + poly(f,g,P)*(3 + 7*i) by { reveal counter_loop(); }
      assert 3 + 7*i <= 10*poly(f,g,P) by { reveal invariant_loop(); }
      mult_preserves_order(poly(f,g,P), (3 + 7*i), poly(f,g,P), 10*poly(f,g,P));
      assert poly(f,g,P)*(3 + 7*i) <= poly(f,g,P)*10*poly(f,g,P);
    }

    assert R == verification(f, g, P, k, a, b, Q, questionsToVerify) by {
      
      assert R == (forall candidate:map<Question, Answer> | candidate in f.Model() :: 
        (
          var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
          var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
          okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
        ))
      by {
        reveal problem_requirements();
        reveal verification_loop();
        assert R == (forall candidate:map<Question, Answer> | candidate in (f.Model() - candidates.Model()) :: 
          (
            var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
            var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
            okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
          ));
        assert (f.Model() - candidates.Model()) == f.Model() by {
          reveal invariant_loop();
          assert candidates_empty == true;
          assert candidates.Model() == {};
        }
      }

      reveal verification();
      assert (|questionsToVerify.Model()| <= k);

      assert R == ((|questionsToVerify.Model()| <= k) &&
      (forall candidate:map<Question, Answer> | candidate in f.Model().Keys ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
      ))) by {

        reveal verification();
        assert (|questionsToVerify.Model()| <= k);
        and_identity(f, g, P, k, a, b, Q, questionsToVerify);
        
        assert R == (forall candidate:map<Question, Answer> | candidate in f.Model() :: 
        (
          var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
          var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
          okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
        ))
        by {
          reveal problem_requirements(); reveal verification_body();
          assert R == (forall candidate:map<Question, Answer> | candidate in (f.Model() - candidates.Model()) :: 
            (
              var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
              var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
              okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
            ));
          assert (f.Model() - candidates.Model()) == f.Model() by {
            reveal invariant_loop();
            assert candidates_empty == true;
            assert candidates.Model() == {};
            assert (f.Model() - {}) == f.Model();
          }
        }

        assume false;
      }

      reveal verification();
    }

  }
  else {
    R := false;
    assert counter <= counter_in + 10*poly(f,g,P)*poly(f,g,P);
    assert R == verification(f, g, P, k, a, b, Q, questionsToVerify) by {
      assert (|questionsToVerify.Model()| > k);
      reveal verification();
      assert !verification(f, g, P, k, a, b, Q, questionsToVerify);
    }
  }
  assert counter_is_polynomial(f, g, P, counter_in, counter) by {
    assert counter <= counter_in + 10*poly(f,g,P)*poly(f,g,P);
    reveal counter_is_polynomial();
  }
  
  assert R == verification(f, g, P, k, a, b, Q, questionsToVerify);
  }





// Given a set "candidates", takes one candidate out of the set and calculates if the candidates that would have answered in the same way to the questions in "questionsToVerify" are equally fit and that no private information has been inferred
method body_loop
(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>,
candidates_:SetMap<Question, Answer>, candidates_empty_:bool, i_:nat, ghost counter_in:nat, ghost counter_:nat, R_:bool)
returns (candidates:SetMap<Question, Answer>, candidates_empty:bool, i:nat, R:bool, ghost counter:nat)

  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

  requires no_termination_body(candidates_empty_)
  requires invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_)
  requires counter_loop(f, g, P, i_, counter_in, counter_)
  
  requires candidates_.Model() <= f.Model().Keys

  ensures decreases_body(candidates_, candidates)
  ensures invariant_loop(f, g, P, Q, candidates, candidates_empty, i)
  ensures counter_loop(f, g, P, i, counter_in, counter)
  
  ensures candidates.Model() < candidates_.Model()
  ensures reveal problem_requirements(); verification_body(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates, R_, R)
{
  counter := counter_;
  candidates := candidates_;
  i := i_;
  candidates_empty := candidates_empty_;

  var candidate:Map<Question, Answer>;
  candidate, counter := candidates.Pick(counter) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_); reveal no_termination_body(candidates_empty_); }
  var person:Map<Question, Answer>;

  var f':MapMap<Question, Answer, bool>;
  var g':MapMap<Question, Answer, int>;
  
  f', counter := those_who_would_answer_the_same(f, candidate, questionsToVerify, counter) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_); reveal problem_requirements(); }
  g', counter := those_who_would_answer_the_same(g, candidate, questionsToVerify, counter) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_); reveal problem_requirements(); }
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 3) by {
    reveal counter_loop();
    assert counter <= (counter_in + poly(f,g,P)*(3 + 7*i)) + candidates.maximumSizeElements() + f.Size() + g.Size();
    assert candidates.maximumSizeElements() <= poly(f,g,P) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_); reveal problem_requirements(); }
    assert counter <= (counter_in + poly(f,g,P)*(3 + 7*i)) + 3*poly(f,g,P);
  }
  var okFit:bool;
  var okPriv:bool;
  okFit, counter := okFitnessMethod(f', counter);
  okPriv, counter := okPrivateMethod(g', P, a, b, Q, counter) by {reveal problem_requirements(); }
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) by {
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 3) + f'.Size() + g'.Size();
    assert f'.Size() <= poly(f,g,P) && g'.Size() <= poly(f,g,P) by {
      reveal problem_requirements();
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
  //ghost var candidates_ := candidates;
  R := R_ && okFit && okPriv;
  assert candidate.Model() in candidates.Model();
  candidates, counter := candidates.Remove(candidate, counter);

  assert f'.Model() == map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person] by { reveal problem_requirements(); }
  assert g'.Model() == map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person] by { reveal problem_requirements(); }

  assert verification_body(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates, R_, R) by {
    verification_body_lemma(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates_empty_, i_, R_, f', g', candidates, candidate, okFit, okPriv, R);
  }

  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 6) by {
    reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);
    assert candidates.Size() <= candidates_.Size() by {
      assert if candidate.Model() !in candidates_.Model() then |candidates.Model()| == |candidates_.Model()| else |candidates.Model()| == |candidates_.Model()| - 1;
      assert candidates_.Size() == |candidates_.Model()|*candidates_.maximumSizeElements();
      assert candidates.Size() == |candidates.Model()|*candidates_.maximumSizeElements() by {
        assert candidates.Size() == |candidates.Model()|*candidates.maximumSizeElements();
        assert candidates.maximumSizeElements() == candidates_.maximumSizeElements();
      }
      assert |candidates.Model()| <= |candidates_.Model()|;
      mult_preserves_order(|candidates.Model()|, candidates_.maximumSizeElements(), |candidates_.Model()|, candidates_.maximumSizeElements());
      assert |candidates.Model()|*candidates_.maximumSizeElements() <= |candidates_.Model()|*candidates_.maximumSizeElements();
    }
    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) + candidates_.Size();

    assert candidates_.Size() <= poly(f,g,P) by {
      assert candidates_.Size() <= f.Size() by {
        assert candidates_.Model() <= f.Model().Keys;

        assert candidates_.Size() == |candidates_.Model()|*candidates_.maximumSizeElements();
        assert f.Size() == |f.Model()|*f.maximumSizeElements();

        assert |candidates_.Model()| <= |f.Model()| by {
          assert candidates_.Model() <= f.Model().Keys;
          assert candidates_.Model() <= f.Model().Keys;
          smallerSetLessCardinality(candidates_.Model(), f.Model().Keys);
          assert |candidates_.Model()| <= |f.Model().Keys|;
        }
        assert candidates_.maximumSizeElements() <= f.maximumSizeElements();
        mult_preserves_order(|candidates_.Model()|, candidates_.maximumSizeElements(), |f.Model()|, f.maximumSizeElements());
      }
      assert f.Size() <= poly(f,g,P);
    }

    assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 5) + poly(f,g,P);
  }

  candidates_empty, counter := candidates.Empty(counter);
  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i + 7);

  ghost var i' := i;
  i := i + 1;

  assert counter <= counter_in + poly(f,g,P)*(3 + 7*i) by {
    reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);

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

  assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) by {
    reveal invariant_loop();
    assert candidates.Model() <= f.Model().Keys;
    assert candidates_empty == (candidates.Model() == {});
    assert forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys;
    assert |candidates.Model()| == |candidates_.Model()| - 1;
    assert i == |f.Model().Keys| - |candidates.Model()|;
  }
  assert counter_loop(f, g, P, i, counter_in, counter) by {reveal counter_loop(); }
  assert decreases_body(candidates_, candidates) by {reveal decreases_body(); }
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


opaque ghost predicate invariant_loop(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, Q:Set<Question>, candidates:SetMap<Question, Answer>, candidates_empty:bool, i:nat) { //{:opaque}
     (candidates.Model() <= f.Model().Keys)
  && (candidates_empty == (candidates.Model() == {}))
  && (forall candidate | candidate in candidates.Model() :: Q.Model() == candidate.Keys)
  //&& (|candidates.Model()| == |candidates_.Model()| - 1)
  && (i == |f.Model().Keys| - |candidates.Model()|)
}

opaque ghost predicate decreases_body(candidates_:SetMap<Question, Answer>, candidates:SetMap<Question, Answer>) {
  (|candidates.Model()| == |candidates_.Model()| - 1)
}

opaque ghost predicate problem_requirements(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>) {
  (forall m | m in f.Model().Keys :: m.Keys == Q.Model()) &&
  (f.Model().Keys == g.Model().Keys) &&
  (P.Model() <= Q.Model()) &&
  (0.0 <= a <= b <= 1.0) &&
  (0 <= k <= |Q.Model()|) &&
  (questionsToVerify.Model() <= Q.Model())
}

opaque ghost predicate counter_loop(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, i:nat, counter_in:nat, counter_out:nat) {
  counter_out <= counter_in + poly(f,g,P)*(3 + 7*i)
}

opaque ghost predicate no_termination_body(candidates_empty:bool) {
  candidates_empty == false
}

opaque ghost predicate counter_is_polynomial(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, counter_in:nat, counter_out:nat) {
  counter_out <= counter_in + 10*poly(f,g,P)*poly(f,g,P)
}

opaque ghost predicate verification(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>)
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
{
  reveal problem_requirements();
  (|questionsToVerify.Model()| <= k) &&
  (forall candidate:map<Question, Answer> | candidate in f.Model().Keys ::                                                   // para todos los posibles entrevistados que pueden responder la entrevista...
  (
    var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f.Model()[person];
    var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g.Model()[person];
    okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
  ))
}

opaque ghost predicate verification_body(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>, candidates_:SetMap<Question, Answer>, candidates:SetMap<Question, Answer>, R_:bool, R:bool)
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
  requires candidates.Model() <= candidates_.Model() <= f.Model().Keys
{
  reveal problem_requirements();
  R == (R_ && forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) ::                                                   // para el entrevistado que acaba de ser procesado...
  (
    var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
    var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
    okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
  ))
}

opaque ghost predicate verification_loop(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>, candidates:SetMap<Question, Answer>, R:bool)
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
{
  reveal problem_requirements();
  R == (forall candidate:map<Question, Answer> | candidate in (f.Model() - candidates.Model()) :: 
  (
    var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
    var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
    okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
  ))
}

/*
method Restrict(S:Map, s:Set, ghost counter_in:nat) returns (R:Map, ghost counter_out:nat)
  requires s.Model() <= S.Model().Keys
  ensures counter_out == counter_in + S.Size()
  ensures R.Model().Keys == s.Model()
  ensures forall key | key in R.Model().Keys :: R.Model()[key] == S.Model()[key]
  ensures forall i | i in R.Model().Items :: i in S.Model().Items
*/

method those_who_would_answer_the_same<T>(f:MapMap<Question, Answer, T>, candidate:Map<Question, Answer>, questionsToVerify:Set<Question>, ghost counter_in:nat)
returns (f':MapMap<Question, Answer, T>, counter_out:nat)
  requires  forall person:map<Question, Answer> | person in f.Model().Keys ::
              (person.Keys == candidate.Model().Keys)
  requires  questionsToVerify.Model() <= candidate.Model().Keys
  /*
  ensures   forall person:map<Question, Answer> | person in f.Model().Keys ::
              if (forall q | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q])
                then (person in f'.Model().Keys && f'.Model()[person] == f.Model()[person])
              else (person !in f.Model().Keys)
  */
  ensures f'.Model() == map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person]
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

lemma and_identity(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>)
requires (|questionsToVerify.Model()| <= k)
requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

ensures reveal problem_requirements();
  ((|questionsToVerify.Model()| <= k) &&
      (forall candidate:map<Question, Answer> | candidate in f.Model().Keys ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
      )))
  ==
  (forall candidate:map<Question, Answer> | candidate in f.Model().Keys ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
  ))
{
}



lemma verification_body_lemma(f:MapMap<Question, Answer, bool>, g:MapMap<Question, Answer, int>, P:Set<Question>, k:int, a:real, b:real, Q:Set<Question>, questionsToVerify:Set<Question>,
candidates_:SetMap<Question, Answer>, candidates_empty_:bool, i_:nat, R_:bool, f':MapMap<Question, Answer, bool>, g':MapMap<Question, Answer, int>, candidates:SetMap<Question, Answer>, candidate:Map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

requires no_termination_body(candidates_empty_)
requires invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_)
requires candidates_.Model() <= f.Model().Keys

requires candidate.Model() in candidates_.Model()
requires candidates.Model() <= candidates_.Model()
requires forall m | m in g'.Model().Keys :: m in g.Model().Keys
requires okFit == okFitness(f'.Model())
requires reveal problem_requirements(); reveal invariant_loop(); okPriv == okPrivate(g'.Model(), P.Model(), a, b, Q.Model())
requires {candidate.Model()} == (candidates_.Model() - candidates.Model())

requires reveal problem_requirements(); f'.Model() == map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person]
requires reveal problem_requirements(); g'.Model() == map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person]
requires R == (R_ && okFit && okPriv)

ensures reveal problem_requirements(); reveal invariant_loop();
        verification_body(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates, R_, R)

{

    assert R == (R_ && (forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
      var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
      okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
    )))
    by {

      assert okFit == okFitness(f'.Model());
      assert okPriv == okPrivate(g'.Model(), P.Model(), a, b, Q.Model()) by { reveal problem_requirements(); }
      assert R == (R_ && okFit && okPriv);
      assert R == (R_ && okFitness(f'.Model()) && okPrivate(g'.Model(), P.Model(), a, b, Q.Model()));


      assert (okFitness(f'.Model()) && okPrivate(g'.Model(), P.Model(), a, b, Q.Model())) == forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) ::
      (
        var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
      )
      by {
        assert {candidate.Model()} == (candidates_.Model() - candidates.Model());
        
        /* ghost var A := (forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) :: (var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person]; var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person]; okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model()) ));
        ghost var B := (var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person]; var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person]; okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model()));
        ghost var C := (okFit && okPriv); */

        assert (forall candidate:map<Question, Answer> | candidate in (candidates_.Model() - candidates.Model()) ::
        (
          var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: f.Model()[person];
          var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate[q]) :: g.Model()[person];
          okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())
        ))
        ==
        (var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model())) by { reveal problem_requirements(); }

        assert 
        (var f' := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
        var g' := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];
        okFitness(f') && okPrivate(g', P.Model(), a, b, Q.Model()))
        ==
        (okFit && okPriv) by {
          reveal problem_requirements(); reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);

          assert f'.Model() == map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
          assert g'.Model() == map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];

          ghost var f1 := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
          ghost var g1 := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];
          assert (var f0 := f1;
                var g0 := g1;
                okFitness(f0) && okPrivate(g0, P.Model(), a, b, Q.Model()))
                ==
                (okFitness(f1) && okPrivate(g1, P.Model(), a, b, Q.Model()));

          assert (var f0 := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
                var g0 := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];
                okFitness(f0) && okPrivate(g0, P.Model(), a, b, Q.Model()))
                ==
                (okFitness(map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person]) &&
                okPrivate(map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person], P.Model(), a, b, Q.Model()));
          
          assume false;

          assert (var f0 := map person:map<Question, Answer> | person in f.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: f.Model()[person];
                var g0 := map person:map<Question, Answer> | person in g.Model().Keys && (forall q:Question | q in questionsToVerify.Model() :: person[q] == candidate.Model()[q]) :: g.Model()[person];
                okFitness(f0) && okPrivate(g0, P.Model(), a, b, Q.Model()))
                ==
                okFitness(f'.Model()) && okPrivate(g'.Model(), P.Model(), a, b, Q.Model());

          assume false;
        }
        
        
        assume false;
      }
      assume false;
    }
    assume false;
  }




}