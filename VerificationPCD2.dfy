include "Auxiliary.dfy"
include "Problems.dfy"
include "DATDPtoPCDlim.dfy"

abstract module VerificationPCD {
  import opened Auxiliary
  import opened Problems

  // * LA VERIFICACIÓN DE PCDLim ES POLINÓMICA


method verifyPCD'
  (f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, interview:Interview)
  returns (R:bool)
requires (forall m | m in f.Keys :: m.Keys == Q)
requires (f.Keys == g.Keys)
requires (P <= Q)
requires (0.0 <= a <= b <= 1.0)
requires (0 <= k <= |Q|)
{
  if !correctSizeInterview(interview, k) || !correctQuestionsInterview(interview, k, Q) {
    return false;
  }

  var paths:set<set<Question>> := getPaths(interview, k, Q);
  R := true;

  while 0<|paths|
  decreases |paths|
  invariant forall path:set<Question> | path in paths :: path <= Q
  {
    var path:set<Question> :| path in paths;
    var b:bool := verifyPCD(f, g, P, k, a, b, Q, path);
    R := R && b;
    paths := paths - {path};
  }

}


/*
function getSetsQuestionsFunction(interview:Interview, k:nat) : (R:set<set<Question>>)
requires correctSizeInterview(interview, k)
ensures if (interview == Empty) || (|interview.Children|==0) then (R=={}) else
        set children:set<Interview> | children in interview.Children.Values ::
        set child:Interview | child in children ::

predicate allPathsTaken(interview:Interview, k:nat, R:set<set<Question>>)
requires correctSizeInterview(interview, k)
requires forall questions:set<Question> | questions in R :: |questions|<=k
{
  if ((interview == Empty) ||  |interview.Children|==0) then true else
  true // ...
}

predicate isPath(interview:Interview, k:nat, path:set<Question>)
requires correctSizeInterview(interview, k)
{
  if ((interview == Empty) ||  |interview.Children|==0) && |path|==0 then true else

}
*/

method getPaths(interview:Interview, k:nat, Q:set<Question>) returns (R:set<set<Question>>)
decreases k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
ensures forall path:set<Question> | path in R :: path <= Q
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

  R := {};
  if (interview != Empty) && (|interview.Children|!=0) {
    assert k>0;

    var children:set<Interview> := interview.Children.Values;
    var children' := children;

    while 0<|children|
      decreases |children|
      invariant k>0
      invariant children <= interview.Children.Values
      //invariant R ==
      invariant forall path:set<Question> | path in R :: path <= Q
    {
      var child:Interview :| child in children;
      var subsets:set<set<Question>> := getPaths(child, k-1, Q) by {
        subinterviewsSmaller(interview, k);
        assert forall child:Interview | child in interview.Children.Values :: correctSizeInterview(child, k-1);
        assert child in interview.Children.Values;
      }
      ghost var subsets' := subsets;
      var R':set<set<Question>> := {};

      while 0<|subsets|
        decreases |subsets|
        invariant subsets <= subsets'
        invariant R' == set subset:set<Question> | subset in (subsets' - subsets) :: {interview.Key} + subset
        invariant forall path:set<Question> | path in R' :: path <= Q
      {
        var sub:set<Question> :| sub in subsets;

        R' := R' + {{interview.Key} + sub};

        subsets := subsets - {sub};
      }
      assert R' == set subset:set<Question> | subset in subsets' :: {interview.Key} + subset;

      R := R + R';

      children := children - {child};
    }

  }
}



  // Para todas las formas válidas de responder a las preguntas de la entrevista / grupos de tipos de candidatos
  // (<= |f.Keys|), ver si la población restante es apta y/o infiere información privada
  method verifyPCD//(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    (f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    returns (R:bool)
  
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
  ensures R == verification(f, g, P, k, a, b, Q, questionsToVerify)
  {
  R := false;
  var nQuestions:int := |questionsToVerify|;
  if nQuestions <= k {
    R := true;
    var candidates:set<map<Question, Answer>> := f.Keys;
    var candidates_empty:bool := |candidates|  == 0;
    var groups:map<map<Question, Answer>, set<map<Question, Answer>>>;
    var i:nat := 0;
    if candidates_empty != true {
      assert candidates <= f.Keys;
      assert candidates_empty == (candidates == {});
      assert forall candidate | candidate in candidates :: Q == candidate.Keys by {  }
      assert i == |f.Keys| - |candidates|;
    }
    assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) by {
      reveal invariant_loop();
    }
    assert verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R) by { reveal verification_loop();  }
    
    while !candidates_empty 
      decreases |candidates|
      invariant problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
      invariant invariant_loop(f, g, P, Q, candidates, candidates_empty, i)
      invariant verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
    {     
      ghost var R_ := R;
      ghost var candidates_ := candidates;

      assert candidates <= f.Keys by {reveal invariant_loop();}

      candidates, candidates_empty, i, R := body_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, candidates_empty, i, R);
      
      assert |candidates| < |candidates_| by { reveal decreases_body(candidates_, candidates); }
    }
    assert candidates == {} by {reveal invariant_loop();}
    allCandidate(f,g,P,k,a,b,Q,questionsToVerify,candidates,R); 
  }
  else {
    R := false;
    assert !verification(f, g, P, k, a, b, Q, questionsToVerify) by {reveal verification();}
  }
}





// Given a set "candidates", takes one candidate out of the set and calculates if the candidates that would have answered in the same way to the questions in "questionsToVerify" are equally fit and that no private information has been inferred
method body_loop
(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool)
returns (candidates:set<map<Question, Answer>>, candidates_empty:bool, i:nat, R:bool)

  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

  requires !candidates_empty_
  requires invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_)
  requires verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates_, R_)

  requires candidates_ <= f.Keys

  ensures decreases_body(candidates_, candidates)
  ensures invariant_loop(f, g, P, Q, candidates, candidates_empty, i)
  
  ensures candidates < candidates_
  ensures verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
{
  candidates := candidates_;
  i := i_;
  candidates_empty := candidates_empty_;
  label L: assert invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);
  
  var candidate:map<Question, Answer>;
  candidate :| candidate in candidates by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_); }
  var person:map<Question, Answer>;

  var f':map<map<Question, Answer>, bool>;
  var g':map<map<Question, Answer>, int>;
  
  f' := those_who_would_answer_the_same(f, candidate, questionsToVerify) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);  }
  g' := those_who_would_answer_the_same(g, candidate, questionsToVerify) by { reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);  }
  var okFit:bool;
  var okPriv:bool;
  okFit := okFitnessMethod(f');
  okPriv := okPrivateMethod(g', P, a, b, Q);

  R := R_ && okFit && okPriv;
  assert f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]; 
  assert g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person]; 
  assert okFit == okFitness(f');
  assert okPriv == okPrivate(g', P, a, b, Q);

  assert candidate in candidates;
  candidates := candidates - {candidate};

    candidates_empty := |candidates| == 0;

  ghost var i' := i;
  i := i + 1;

  assert invariant_loop(f, g, P, Q, candidates, candidates_empty, i) by {
    reveal invariant_loop();
    assert candidates <= f.Keys;
    assert candidates_empty == (candidates == {});
    assert forall candidate | candidate in candidates :: Q == candidate.Keys;
    assert |candidates| == |candidates_| - 1;
    assert i == |f.Keys| - |candidates|;
  }
  assert decreases_body(candidates_, candidates) by {reveal decreases_body(); }
  assert verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R) by
  { 
   verification_body_lemma(f,g,P,k,a,b,Q,questionsToVerify,candidates_,candidates_empty_,i,R_,f',g',candidates,candidate, okFit,okPriv,R);
  }

}







opaque ghost predicate invariant_loop(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, Q:set<Question>, candidates:set<map<Question, Answer>>, candidates_empty:bool, i:nat) { //{:opaque}
     (candidates <= f.Keys)
  && (candidates_empty == (candidates == {}))
  && (forall candidate | candidate in candidates :: Q == candidate.Keys)
  //&& (|candidates| == |candidates_| - 1)
  && (i == |f.Keys| - |candidates|)
}

opaque ghost predicate decreases_body(candidates_:set<map<Question, Answer>>, candidates:set<map<Question, Answer>>) {
  (|candidates| == |candidates_| - 1)
}

ghost predicate problem_requirements(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>) {
  (forall m | m in f.Keys :: m.Keys == Q) &&
  (f.Keys == g.Keys) &&
  (P <= Q) &&
  (0.0 <= a <= b <= 1.0) &&
  (0 <= k <= |Q|) &&
  (questionsToVerify <= Q)
}


opaque ghost predicate verification(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
{
  (|questionsToVerify| <= k) &&
  (forall candidate:map<Question, Answer> | candidate in f ::
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  ))
}


lemma allCandidate(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>, candidates:set<map<Question, Answer>>, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
requires verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
requires candidates == {} 
requires |questionsToVerify| <= k
ensures R == verification(f, g, P, k, a, b, Q, questionsToVerify)
{
  assert (|questionsToVerify| <= k);
  assert
    (forall candidate:map<Question, Answer> | candidate in f ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )) == verification(f,g, P, k, a, b, Q, questionsToVerify) by {
    reveal verification();
    }


  assert R==
  (forall candidate:map<Question, Answer> | candidate in f ::
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  )) by {
    assert R == (forall candidate:map<Question, Answer> | candidate in (f - candidates) :: 
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      )) by { reveal verification_loop(); }
    
    assert f.Keys == ((f.Keys - candidates) + candidates) by {
      assert candidates <= f.Keys;
      SetMinusSubsetPlusSubsetEqualsSet(f.Keys, candidates);
    }
  }
}


lemma SetMinusSubsetPlusSubsetEqualsSet(S:set<map<Question, Answer>>, s:set<map<Question, Answer>>)
requires s <= S
ensures S == ((S - s) + s)
{
}


opaque ghost predicate verification_loop(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>, candidates:set<map<Question, Answer>>, R:bool)
  requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)
{
  R == (forall candidate:map<Question, Answer> | candidate in (f - candidates) :: 
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  ))
}

method those_who_would_answer_the_same<T>(f:map<map<Question, Answer>, T>, candidate:map<Question, Answer>, questionsToVerify:set<Question>)
returns (f':map<map<Question, Answer>, T>)
  requires  forall person:map<Question, Answer> | person in f.Keys ::
              (person.Keys == candidate.Keys)
  requires  questionsToVerify <= candidate.Keys
  /*
  ensures   forall person:map<Question, Answer> | person in f.Keys ::
              if (forall q | q in questionsToVerify :: person[q] == candidate[q])
                then (person in f'.Keys && f'[person] == f[person])
              else (person !in f.Keys)
  */
  ensures f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]
  ensures f'.Keys <= f.Keys
  ensures |f'| <= |f|
{
  f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
  if_contained_then_smaller(f', f);
  assert |f'.Keys| <= |f.Keys|;
}


method okFitnessMethod(f:map<map<Question, Answer>, bool>) returns (R:bool)
  ensures R == okFitness(f)
{
  var keys := f.Keys;
  var allTrue := true;
  var allFalse := true;

  while ! (|keys| <= 0)
    decreases |keys|
    invariant keys <= f.Keys
    invariant allTrue == (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == true)
    invariant allFalse == (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == false)
  {
    var key :| key in keys;

    allTrue := allTrue && f[key];
    allFalse := allFalse && !f[key];

    keys := keys - {key};
  }
  R := allTrue || allFalse;
  assert (allTrue || allFalse) == okFitness(f) by {
    assert allTrue == (forall b:bool | b in f.Values :: b == true) by {
      assert forall b:bool | b in f.Values :: (exists key | key in f.Keys :: f[key] == b);
      assert (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == true) == (forall b:bool | b in f.Values :: b == true);
    }
    assert allFalse == (forall b:bool | b in f.Values :: b == false) by {
      assert forall b:bool | b in f.Values :: (exists key | key in f.Keys :: f[key] == b);
      assert (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == false) == (forall b:bool | b in f.Values :: b == false);
    }
  }
}


method okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>) returns (R:bool)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires P <= Q
  requires 0.0 <= a <= 1.0
  requires 0.0 <= b <= 1.0
  requires a <= b
  ensures R == okPrivate(g, P, a, b, Q)
/*
{
  var keys := g.Keys;
  var nC := 0;

  while ! (|keys| <= 0)
    decreases |keys|
    invariant keys <= g.Keys
    invariant nC == nCandidates(g, Q)
  {
    var key :| key in keys;

    nC := nC + g[key];

    keys := keys - {key};
  }
}

method {:only} nCandidatesMethod(g:map<map<Question, Answer>, int>, Q:set<Question>) returns (r:int)
  requires forall m | m in g.Keys :: m.Keys == Q
  ensures r == nCandidates(g, Q)
{
  if g.Keys == {} {
    r := 0;
    assert r == nCandidates(g, Q);
  }
  else {
    var c:map<Question, Answer> :| c in g.Keys;
    r := nCandidatesMethod(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q
    );
    r := r + g[c];

    assert var c:map<Question, Answer> := Pick(g.Keys);
        nCandidates(g, Q) == g[c] + nCandidates(
          (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
          Q
        );

    assume false;
  }
}
*/


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

lemma and_identity(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
requires (|questionsToVerify| <= k)
requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

ensures 
  ((|questionsToVerify| <= k) &&
      (forall candidate:map<Question, Answer> | candidate in f.Keys ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      )))
  ==
  (forall candidate:map<Question, Answer> | candidate in f.Keys ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in person.Keys :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
  ))
{
}



lemma verification_body_lemma(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool, f':map<map<Question, Answer>, bool>, g':map<map<Question, Answer>, int>, candidates:set<map<Question, Answer>>, candidate:map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q, questionsToVerify)

requires !candidates_empty_
requires candidates_ <= f.Keys
//requires invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_)

requires candidate in candidates_
requires candidates <= candidates_
requires forall m | m in g'.Keys :: m in g.Keys
requires candidates == candidates_ - {candidate}
requires  f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]
requires  g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person]
requires okFit == okFitness(f')
requires okPriv == okPrivate(g', P, a, b, Q)
requires verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates_,R_)
requires R == (R_ && okFit && okPriv)

ensures verification_loop(f, g, P, k, a, b, Q, questionsToVerify, candidates,R)

/*{

    assert R == (R_ && (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )))
    by {

      assert okFit == okFitness(f');
      assert okPriv == okPrivate(g', P, a, b, Q) by {  }
      assert R == (R_ && okFit && okPriv);
      assert R == (R_ && okFitness(f') && okPrivate(g', P, a, b, Q));
      
      assert forall q | q in questionsToVerify :: q in candidate.Keys by {  }
      assert forall person:map<Question, Answer> | person in f.Keys :: person.Keys == Q by {  }
      assert forall person:map<Question, Answer> | person in g.Keys :: person.Keys == Q by {  }


      assert (okFitness(f') && okPrivate(g', P, a, b, Q)) == forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      )
      by {
        assert {candidate} == (candidates_ - candidates);

        assert (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
        (
          var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
          var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
          okFitness(f') && okPrivate(g', P, a, b, Q)
        ))
        ==
        (var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)) by {  }

        assert 
        (var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q))
        ==
        (okFit && okPriv) by {
           reveal invariant_loop(f, g, P, Q, candidates_, candidates_empty_, i_);

          assert f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
          assert g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];

          ghost var f1 := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
          ghost var g1 := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
          assert (var f0 := f1;
                var g0 := g1;
                okFitness(f0) && okPrivate(g0, P, a, b, Q))
                ==
                (okFitness(f1) && okPrivate(g1, P, a, b, Q));

          assert (var f0 := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
                var g0 := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
                okFitness(f0) && okPrivate(g0, P, a, b, Q))
                ==
                (okFitness(map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]) &&
                okPrivate(map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person], P, a, b, Q));

          /*
          assert (var f0 := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
                var g0 := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
                okFitness(f0) && okPrivate(g0, P, a, b, Q))
                ==
                (okFitness(f') && okPrivate(g', P, a, b, Q));
          */
        }
        
        /*
        assert forall q | q in questionsToVerify :: q in candidate.Keys by {  }
        assert forall person:map<Question, Answer> | person in f.Keys :: person.Keys == Q by {  }
        assert forall person:map<Question, Answer> | person in g.Keys :: person.Keys == Q by {  }
        */
      }
    }
    
    assert verification_body(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates, R_, R) by {
      reveal verification_body();
      
      assert R == (R_ && forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      ));
    }
  }*/


  lemma if_contained_then_smaller<A, B>(f':map<A, B>, f:map<A, B>)
    requires forall key:A | key in f' :: key in f
    ensures |f'| <= |f|
  {
    if |f'| == 0 {
      
    }
    else {
      var key:A :| key in f'.Keys;
      assert key in f.Keys;
      
      var new_f' := f' - {key};
      var new_f := f - {key};
      if_contained_then_smaller(new_f', new_f);
    }
  }


}
