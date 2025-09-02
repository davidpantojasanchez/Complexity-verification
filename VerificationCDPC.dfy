include "Auxiliary.dfy"
include "Problems.dfy"
include "DATDPtoCDPClim.dfy"

abstract module VerificationCDPC {
  import opened Auxiliary
  import opened Problems

  // * LA VERIFICACIÓN DE CDPCLim ES POLINÓMICA

method verifyCDPC
  (f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, A:set<Answer>, interview:Interview)
  returns (R:bool)
requires problem_requirements(f, g, P, k, a, b, Q)

requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)

ensures reveal requires_of_the_postcondition(); postcondition(f, g, P, k, a, b, Q, A, interview, R)
{
 /* 
  if !correctSizeInterview(interview, k) || !correctQuestionsInterview(interview, k, Q) {
    assert postcondition(f, g, P, k, a, b, Q, A, interview, R) by { reveal postcondition(); }
    assert (forall path:set<Question> | path in pathsInterview(interview, k) :: path <= Q);
    return false;
  }
  */
  var paths:set<set<Question>> := getPaths(interview, k, Q);
  R := true;
  

  while 0<|paths|
  decreases |paths|
  invariant forall path:set<Question> | path in paths :: path <= Q
  invariant paths <= pathsInterview(interview, k, Q)
  invariant R == (forall path:set<Question> | path in (pathsInterview(interview, k, Q) - paths) :: verification(f, g, P, k, a, b, Q, path))
  {
    var path:set<Question> :| path in paths;
    var r:bool := verifyPathCDPC(f, g, P, k, a, b, Q, path);
    R := R && r;
    assert R == ((forall p:set<Question> | p in (pathsInterview(interview, k, Q) - paths) :: verification(f, g, P, k, a, b, Q, p)) && r);
    ghost var old_paths := paths;
    paths := paths - {path};

    assert R == ((forall p:set<Question> | p in (pathsInterview(interview, k, Q) - (paths + {path})) :: verification(f, g, P, k, a, b, Q, p)) && r) by {
      assert R == ((forall p:set<Question> | p in (pathsInterview(interview, k, Q) - old_paths) :: verification(f, g, P, k, a, b, Q, p)) && r);
      assert path in old_paths;
      assert old_paths == (paths + {path}) by { assert path in old_paths; }
      assert (path in (pathsInterview(interview, k, Q) - old_paths)) == (path in (pathsInterview(interview, k, Q) - (paths + {path})));
    }

    assert R == (forall path:set<Question> | path in (pathsInterview(interview, k, Q) - paths) :: verification(f, g, P, k, a, b, Q, path)) by {
      assert r == verification(f, g, P, k, a, b, Q, path);
      assert R == (forall p:set<Question> | p in ((pathsInterview(interview, k, Q) - (paths + {path})) + {path}) :: verification(f, g, P, k, a, b, Q, p));
    }
  }

  assert R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: verification(f, g, P, k, a, b, Q, path));
  assert (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: path <= Q);

  assert requires_of_the_postcondition(f, g, P, k, a, b, Q, A, interview, R) by {
    assert (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: path <= Q);
    reveal requires_of_the_postcondition();
  }
  assert postcondition(f, g, P, k, a, b, Q, A, interview, R) by { reveal postcondition(); }
}


opaque ghost predicate postcondition(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, A:set<Answer>, interview:Interview, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q)
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)

requires requires_of_the_postcondition(f, g, P, k, a, b, Q, A, interview, R) //(forall path:set<Question> | path in pathsInterview(interview, k) :: path <= Q)
{
  
  R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: verification(f, g, P, k, a, b, Q, path))
}

opaque ghost predicate requires_of_the_postcondition(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, A:set<Answer>, interview:Interview, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q)
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
{
  
  (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: path <= Q)
}


method getPaths(interview:Interview, k:nat, Q:set<Question>) returns (R:set<set<Question>>)
decreases k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
ensures forall path:set<Question> | path in R :: path <= Q
ensures R == pathsInterview(interview, k, Q)
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
  if (interview == Empty) || (|interview.Children|==0) {
    assert R == pathsInterview(interview, k, Q);
    return R;
  }
  
  assert k>0;

  var children:set<Interview> := interview.Children.Values;
  var children' := children;

  assert R == union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) by {
    assert R == {};
    assert union({}) == {};
    assert (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) == {};
    assert  union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) == {};
  }

  while 0<|children|
    decreases |children|
    invariant k>0
    invariant children <= interview.Children.Values
    invariant children' == interview.Children.Values
    invariant forall path:set<Question> | path in R :: path <= Q
    invariant R == union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q))
  {
    var child:Interview :| child in children;
    var subsets:set<set<Question>> := getPaths(child, k-1, Q) by {
      subinterviewsSmaller(interview, k);
      assert forall child:Interview | child in interview.Children.Values :: correctSizeInterview(child, k-1);
      assert child in interview.Children.Values;
    }

    R, children := getPaths_body_loop(interview, k, Q, R, children, children', child, subsets);
  }

  assert R == union (set child:Interview | child in children' :: pathsInterviewPlusElement(child, k-1, interview.Key, Q)) by {
    assert R == union (set child:Interview | child in (children' - children) :: pathsInterviewPlusElement(child, k-1, interview.Key, Q));
    assert |children|==0;
    assert (children' - children) == children';
    assert R == union (set child:Interview | child in children' :: pathsInterviewPlusElement(child, k-1, interview.Key, Q));
  }
  
  assert pathsInterview(interview, k, Q) == (union (set child:Interview | child in children' :: pathsInterviewPlusElement(child, k-1, interview.Key, Q))) by {
    pathsInterview_equals_union_pathsInterviewPlusElement_lemma(interview, children', k, Q);
  }

  assert R == pathsInterview(interview, k, Q);
}


lemma pathsInterview_equals_union_pathsInterviewPlusElement_lemma(interview:Interview, children':set<Interview>, k:int, Q:set<Question>)
requires (interview != Empty)
requires (|interview.Children|!=0)
requires children' == interview.Children.Values
requires 0<=k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
ensures pathsInterview(interview, k, Q) == (union (set child:Interview | child in children' :: pathsInterviewPlusElement(child, k-1, interview.Key, Q)))
{
  if_empty_pathsInterview_equals_union(interview, k, Q);
  assert pathsInterview(interview, k, Q) ==
    (union (set child:Interview | child in interview.Children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset)));
  assert forall child:Interview | child in children' :: (pathsInterviewPlusElement(child, k-1, interview.Key, Q) == (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset));
  assert (set child:Interview | child in children' :: pathsInterviewPlusElement(child, k-1, interview.Key, Q)) ==
         (set child:Interview | child in children' :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset));
}

lemma if_empty_pathsInterview_equals_union(interview:Interview, k:int, Q:set<Question>)
decreases k
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
requires k>=0
requires (interview != Empty) && (|interview.Children|!=0)
ensures pathsInterview(interview, k, Q) ==
        (union (set child:Interview | child in interview.Children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset)))
{
  var u := (set child:Interview | child in interview.Children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset));

  assert 
    (match interview
    case Empty => {}
    case Node (key, children) =>
      if |interview.Children|==0 then {} else
      union (set child:Interview | child in children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset)))
    ==
    (match interview
    case Empty => {}
    case Node (key, children) =>
      if |interview.Children|==0 then {} else
      union (u))
  by {
    assert u == (set child:Interview | child in interview.Children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset));
  }

  assert 
    pathsInterview(interview, k, Q)
    ==
    (match interview
    case Empty => {}
    case Node (key, children) =>
      if |interview.Children|==0 then {} else
      union (u))
  by {
    assert u == (set child:Interview | child in interview.Children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset));
  }


  assert pathsInterview(interview, k, Q) ==
  (match interview
  case Empty => {}
  case Node (key, children) =>
    if |interview.Children|==0 then {} else
    union (set child:Interview | child in children.Values :: (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset)));
}



method getPaths_body_loop(interview:Interview, k:nat, Q:set<Question>, R_:set<set<Question>>, children_:set<Interview>, children':set<Interview>, child:Interview, subsets_:set<set<Question>>) returns (R:set<set<Question>>, children:set<Interview>)
  requires correctSizeInterview(interview, k)
  requires correctQuestionsInterview(interview, k, Q)

  requires (interview != Empty) && (|interview.Children.Values| != 0)
  requires 0<|children_|
  requires children' == interview.Children.Values
  requires children_ <= children'
  requires child in children_
  requires subsets_ == pathsInterview(child, k-1, Q)

  requires k>0
  requires children_ <= interview.Children.Values
  requires children' == interview.Children.Values
  requires forall path:set<Question> | path in R_ :: path <= Q
  requires R_ == union (set c:Interview | c in (children' - children_) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q))

  ensures |children_| == |children| + 1

  ensures k>0
  ensures children <= interview.Children.Values
  ensures children' == interview.Children.Values
  ensures forall path:set<Question> | path in R_ :: path <= Q
  ensures R == union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q))
{
  R := R_;
  children := children_;
  var subsets:set<set<Question>> := subsets_;

  ghost var subsets' := subsets;
  var R':set<set<Question>> := {};

  while 0<|subsets|
    decreases |subsets|
    invariant subsets <= subsets'
    invariant children' == interview.Children.Values
    invariant R' == set subset:set<Question> | subset in (subsets' - subsets) :: {interview.Key} + subset
    invariant forall path:set<Question> | path in R' :: path <= Q
  {
    var sub:set<Question> :| sub in subsets;

    R' := R' + {{interview.Key} + sub};

    subsets := subsets - {sub};
  }
  assert R' == set subset:set<Question> | subset in subsets' :: {interview.Key} + subset;
  assert R' == (set subset:set<Question> | subset in pathsInterview(child, k-1, Q) :: {interview.Key} + subset);
  assert R' == pathsInterviewPlusElement(child, k-1, interview.Key, Q);

  R := R + R';
  
  assert pathsInterviewPlusElement(child, k-1, interview.Key, Q) <= R;
  ghost var Child := {child};
  if_only_element_has_pathsInterviewPlusElement_set_has_pathsInterviewPlusElement(Child, child, k-1, interview.Key, R, Q);
  assert forall child:Interview | child in Child :: pathsInterviewPlusElement(child, k-1, interview.Key, Q) <= R;
  
  assert  R == union (set child:Interview | child in (children' - children) :: pathsInterviewPlusElement(child, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q);
  
  ghost var prev_children := children;
  children := children - {child};
  assert (children' - prev_children) == (children' - children - {child});
  assert 0 <= |(children' - children - {child})| <= |children'|;

  assert R == union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) by {
    assert  R == union (set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q);

    assert children' == interview.Children.Values;
    assert correctQuestionsInterview(interview, k, Q);
    union_lemma(interview, children, children', child, k, Q);

    assert union (set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) ==
            union (set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q);
  }
}












lemma if_only_element_has_pathsInterviewPlusElement_set_has_pathsInterviewPlusElement(Child:set<Interview>, child:Interview, k:int, key:Question, R:set<set<Question>>, Q:set<Question>)
requires Child == {child}
requires correctSizeInterview(child, k)
requires correctQuestionsInterview(child, k, Q)
requires k>=0
requires key in Q
requires pathsInterviewPlusElement(child, k, key, Q) <= R
ensures forall c | c in Child :: pathsInterviewPlusElement(c, k, key, Q) <= R
{
}


lemma union_lemma(interview:Interview, children:set<Interview>, children':set<Interview>, child:Interview, k:int, Q:set<Question>)

requires correctSizeInterview(interview, k)
requires correctSizeInterview(child, k-1)
requires correctQuestionsInterview(interview, k, Q)
requires correctQuestionsInterview(child, k-1, Q)
requires k>=0
requires interview != Empty
requires forall c:Interview | c in children' :: correctSizeInterview(c, k-1)
requires child !in children 
requires child in children'
requires children <= children'

requires forall c:Interview | c in children' :: correctQuestionsInterview(c, k-1, Q)

ensures union(set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) ==
        (union(set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q))

{
  assert ((children' - children - {child}) + {child}) == (children' - children);
  
  calc == {
    ((set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + (set c:Interview | c in ({child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)));
    ((set c:Interview | c in ((children' - children - {child}) + {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)));
    ((set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)));
  }

  calc == {
    (union(set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q));
    (union(set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + union({pathsInterviewPlusElement(child, k-1, interview.Key, Q)}));
    (union((set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + {pathsInterviewPlusElement(child, k-1, interview.Key, Q)}));
    (union((set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + (set c:Interview | c in ({child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q))));
    (union(set c:Interview | c in ((children' - children - {child}) + {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)));
    (union(set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)));
  }
  assert union(set c:Interview | c in (children' - children) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) ==
        (union(set c:Interview | c in (children' - children - {child}) :: pathsInterviewPlusElement(c, k-1, interview.Key, Q)) + pathsInterviewPlusElement(child, k-1, interview.Key, Q));
}




  // Para todas las formas válidas de responder a las preguntas de la entrevista / grupos de tipos de candidatos
  // (<= |f.Keys|), ver si la población restante es apta y/o infiere información privada
  method verifyPathCDPC//(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    (f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
    returns (R:bool)
  
  requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
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
    assert auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates, candidates_empty, i) by {
      reveal auxiliary_invariant_verifyPathCDPC();
    }
    assert verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, R) by { reveal verification_invariant_verifyPathCDPC();  }
    
    while !candidates_empty 
      decreases |candidates|
      invariant problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
      invariant auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates, candidates_empty, i)
      invariant verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
    {
      ghost var candidates_ := candidates;
      assert candidates <= f.Keys by {reveal auxiliary_invariant_verifyPathCDPC();}

      candidates, candidates_empty, i, R := body_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, candidates_empty, i, R);
      
      assert |candidates| < |candidates_| by { reveal decreases_body(candidates_, candidates); }
    }
    assert candidates == {} by {reveal auxiliary_invariant_verifyPathCDPC();}
    allCandidate(f,g,P,k,a,b,Q,questionsToVerify,candidates,R); 
  }
  else {
    R := false;
    assert !verification(f, g, P, k, a, b, Q, questionsToVerify) by {reveal verification();}
  }
}





// Given a set "candidates", takes one candidate out of the set and calculates if the candidates that would have answered in the same way to the questions in "questionsToVerify" are equally fit and that no private information has been inferred
method body_verifyPathCDPC
(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool)
returns (candidates:set<map<Question, Answer>>, candidates_empty:bool, i:nat, R:bool)

  requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)

  requires !candidates_empty_
  requires auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_)
  requires verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates_, R_)

  requires candidates_ <= f.Keys

  ensures decreases_body(candidates_, candidates)
  ensures auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates, candidates_empty, i)
  
  ensures candidates < candidates_
  ensures verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
{
  candidates := candidates_;
  i := i_;
  candidates_empty := candidates_empty_;
  label L: assert auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_);
  
  var candidate:map<Question, Answer>;
  candidate :| candidate in candidates by { reveal auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_); }
  var person:map<Question, Answer>;

  var f':map<map<Question, Answer>, bool>;
  var g':map<map<Question, Answer>, int>;
  
  f' := those_who_would_answer_the_same(f, candidate, questionsToVerify) by { reveal auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_);  }
  g' := those_who_would_answer_the_same(g, candidate, questionsToVerify) by { reveal auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_);  }
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

  assert auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates, candidates_empty, i) by {
    reveal auxiliary_invariant_verifyPathCDPC();
    assert candidates <= f.Keys;
    assert candidates_empty == (candidates == {});
    assert forall candidate | candidate in candidates :: Q == candidate.Keys;
    assert |candidates| == |candidates_| - 1;
    assert i == |f.Keys| - |candidates|;
  }
  assert decreases_body(candidates_, candidates) by {reveal decreases_body(); }
  assert verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, R) by
  { 
    verification_body_lemma(f,g,P,k,a,b,Q,questionsToVerify,candidates_,candidates_empty_,i,R_,f',g',candidates,candidate, okFit,okPriv,R);
  }

}





opaque ghost predicate auxiliary_invariant_verifyPathCDPC(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, Q:set<Question>, candidates:set<map<Question, Answer>>, candidates_empty:bool, i:nat) { //{:opaque}
     (candidates <= f.Keys)
  && (candidates_empty == (candidates == {}))
  && (forall candidate | candidate in candidates :: Q == candidate.Keys)
  && (i == |f.Keys| - |candidates|)
}
/*
opaque ghost predicate invariant_body_loop(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool, f':map<map<Question, Answer>, bool>, g':map<map<Question, Answer>, int>, candidates:set<map<Question, Answer>>, candidate:map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
{
 (!candidates_empty_) &&
 (candidates_ <= f.Keys) &&
 (candidate in candidates_) &&
 (candidates <= candidates_) &&
 (forall m | m in g'.Keys :: m in g.Keys) &&
 (candidates == candidates_ - {candidate}) &&
 (f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]) &&
 (g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person]) &&
 (okFit == okFitness(f')) &&
 (okPriv == okPrivate(g', P, a, b, Q))
}*/


opaque ghost predicate decreases_body(candidates_:set<map<Question, Answer>>, candidates:set<map<Question, Answer>>) {
  (|candidates| == |candidates_| - 1)
}

ghost predicate problem_requirements(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>) {
  (forall m | m in f.Keys :: m.Keys == Q) &&
  (f.Keys == g.Keys) &&
  (P <= Q) &&
  (0.0 <= a <= b <= 1.0) &&
  (0 <= k <= |Q|)
}

ghost predicate problem_requirements_path(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>) {
  (forall m | m in f.Keys :: m.Keys == Q) &&
  (f.Keys == g.Keys) &&
  (P <= Q) &&
  (0.0 <= a <= b <= 1.0) &&
  (0 <= k <= |Q|) &&
  (questionsToVerify <= Q)
}


opaque ghost predicate verification(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>)
  requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
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
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
requires verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates, R)
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
      )) by { reveal verification_invariant_verifyPathCDPC(); }
    
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


opaque ghost predicate verification_invariant_verifyPathCDPC(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>, candidates:set<map<Question, Answer>>, R:bool)
  requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
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
      assert (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == false) == (forall b:bool | b in f.Values :: b == false) by {
        assert allFalse == (forall key:map<Question, Answer> | key in (f.Keys - keys) :: f[key] == false);
      }
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

{
  var P' := P;
  R := true;

  assert R ==
    forall i:Question | i in (P - P') ::
      var nC:real := nCandidates(g, Q) as real;
      var nP:real := nPrivate(g, Q, i, T) as real;
      if nC == 0.0 then
        true
      else
        a <= nP / nC <= b
  by {
    assert (P - P') == {};
  }

  assert R == okPrivate(g, (P - P'), a, b, Q) by {
    reveal okPrivate();

    assert R ==
      forall i:Question | i in (P - P') ::
        var nC:real := nCandidates(g, Q) as real;
        var nP:real := nPrivate(g, Q, i, T) as real;
        if nC == 0.0 then
          true
        else
          a <= nP / nC <= b
    by {
      assert (P - P') == {};
    }
  }

  while P' != {}
  decreases P'
  invariant P' <= P
  invariant R == okPrivate(g, (P - P'), a, b, Q)
  {
    ghost var old_P' := P';

    var P'_out;
    P'_out, R := body_okPrivateMethod(g, P, a, b, Q, P', R) by {
      reveal preconditions_okPrivateMethod();
      reveal termination_okPrivateMethod();
      reveal invariant_entry_okPrivateMethod();
    }
    assert R == okPrivate(g, (P - P'_out), a, b, Q) by {
      reveal invariant_exit_okPrivateMethod();
    }
    
    assert P'_out < P' by {
      reveal decreases_okPrivateMethod();
    }
    P' := P'_out;

    assert R == okPrivate(g, (P - P'), a, b, Q) by {
      reveal preconditions_okPrivateMethod();
      reveal termination_okPrivateMethod();
      reveal invariant_entry_okPrivateMethod();
    }
    
  }

}


opaque ghost predicate preconditions_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool)
{
  (forall m | m in g.Keys :: m.Keys == Q)
  && (P <= Q)
  && (0.0 <= a <= 1.0)
  && (0.0 <= b <= 1.0)
  && (a <= b)
}
opaque ghost predicate termination_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool)
{
  P' != {}
}
opaque ghost predicate invariant_entry_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool)
requires preconditions_okPrivateMethod(g, P, a, b, Q, P', R)
{
  reveal preconditions_okPrivateMethod();
  (P' <= P)
  && (R ==
    forall i:Question | i in (P - P') ::
      var nC:real := nCandidates(g, Q) as real;
      var nP:real := nPrivate(g, Q, i, T) as real;
      if nC == 0.0 then
        true
      else
        a <= nP / nC <= b)
}
opaque ghost predicate invariant_exit_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool, P'_out:set<Question>, R_out:bool)
requires preconditions_okPrivateMethod(g, P, a, b, Q, P', R)
{
  reveal preconditions_okPrivateMethod();
  (P'_out <= P)
  && (R_out == okPrivate(g, (P - P'_out), a, b, Q))
}
opaque ghost predicate decreases_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool, P'_out:set<Question>, R_out:bool)
{
  P'_out < P'
}

method body_okPrivateMethod(g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>, P':set<Question>, R:bool) returns (P'_out:set<Question>, R_out:bool)
  requires preconditions_okPrivateMethod(g, P, a, b, Q, P', R)
  requires termination_okPrivateMethod(g, P, a, b, Q, P', R)
  requires invariant_entry_okPrivateMethod(g, P, a, b, Q, P', R)
  ensures invariant_exit_okPrivateMethod(g, P, a, b, Q, P', R, P'_out, R_out)
  ensures decreases_okPrivateMethod(g, P, a, b, Q, P', R, P'_out, R_out)
{

  P'_out := P';
  R_out := R;

  var i:Question :| i in P' by { reveal termination_okPrivateMethod(); }
  var nC:int := nCandidatesMethod(g, Q) by { reveal preconditions_okPrivateMethod(); }
  var nP:int := nPrivateMethod(g, Q, i, T) by { reveal preconditions_okPrivateMethod(); reveal invariant_entry_okPrivateMethod(); }
  var real_nC:real := nC as real;
  var real_nP:real := nP as real;

  if real_nC == 0.0  {}
  else {
    R_out := R && (a <= real_nP / real_nC <= b);
  }

  P'_out := P' - {i};

  assert invariant_exit_okPrivateMethod(g, P, a, b, Q, P', R, P'_out, R_out) by {
    reveal preconditions_okPrivateMethod();
    reveal termination_okPrivateMethod();
    reveal invariant_entry_okPrivateMethod();
    reveal invariant_exit_okPrivateMethod();
  }
  assert decreases_okPrivateMethod(g, P, a, b, Q, P', R, P'_out, R_out) by { reveal decreases_okPrivateMethod(); }
}


method nCandidatesMethod(g:map<map<Question, Answer>, int>, Q:set<Question>) returns (r:int)
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

    nCandidatesLemma(g, Q);
  }
}

method nPrivateMethod(g:map<map<Question, Answer>, int>, Q:set<Question>, privateQuestion:Question, selectedAnswer:Answer) returns (r:int)
requires forall m | m in g.Keys :: m.Keys == Q
requires privateQuestion in Q
  ensures r == nPrivate(g, Q, privateQuestion, selectedAnswer)
{
  if g.Keys == {} {
    r := 0;
    assert r == nPrivate(g, Q, privateQuestion, selectedAnswer);
  }
  else {
    var c:map<Question, Answer> :| c in g.Keys;
    r := nPrivateMethod(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q,
      privateQuestion,
      selectedAnswer
    );
    r := r + (if c[privateQuestion] == selectedAnswer then g[c] else 0);

    assert var c:map<Question, Answer> := Pick(g.Keys);
        nPrivate(g, Q, privateQuestion, selectedAnswer) == (if c[privateQuestion] == selectedAnswer then g[c] else 0) + nPrivate(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q,
      privateQuestion,
      selectedAnswer
    );

    nPrivateLemma(g, Q, privateQuestion, selectedAnswer);
  }
}

lemma nCandidatesLemma(g:map<map<Question, Answer>, int>, Q:set<Question>)
//decreases |g.Keys|
requires forall m | m in g.Keys :: m.Keys == Q
ensures forall c:map<Question, Answer> | c in g.Keys ::
  nCandidates(g, Q) == g[c] + nCandidates(
    (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
    Q
  )
{
  if g.Keys == {} {}
  else {
    
    assert var c:map<Question, Answer> := Pick(g.Keys);
      nCandidates(g, Q) == g[c] + nCandidates(
        (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
        Q
      );

    assume false;

    assert var c:map<Question, Answer> :| c in g.Keys;
      nCandidates(g, Q) == g[c] + nCandidates(
        (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
        Q
      );  
    
    forall c:map<Question, Answer> | c in g.Keys
      ensures nCandidates(g, Q) == g[c] + nCandidates(
          (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
          Q
        )
    {
    }
    
  }
}

lemma nPrivateLemma(g:map<map<Question, Answer>, int>, Q:set<Question>, privateQuestion:Question, selectedAnswer:Answer)
//decreases |g.Keys|
requires forall m | m in g.Keys :: m.Keys == Q
requires privateQuestion in Q
ensures forall c:map<Question, Answer> | c in g.Keys ::
  nPrivate(g, Q, privateQuestion, selectedAnswer) == (if c[privateQuestion] == selectedAnswer then g[c] else 0) + nPrivate(
    (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
    Q,
    privateQuestion,
    selectedAnswer
  )
{
  if g.Keys == {} {}
  else {
    assert var c:map<Question, Answer> := Pick(g.Keys);
      nPrivate(g, Q, privateQuestion, selectedAnswer) == (if c[privateQuestion] == selectedAnswer then g[c] else 0) + nPrivate(
      (map m:map<Question, Answer> | m in g.Keys && m != c :: g[m]),
      Q,
      privateQuestion,
      selectedAnswer
    );
    assume false;
  }
}





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
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)

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



lemma verification_loop_recover(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>, candidates:set<map<Question, Answer>>, R:bool)
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
requires R == (forall candidate:map<Question, Answer> | candidate in (f - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))
ensures verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates,R)
{reveal verification_invariant_verifyPathCDPC();}

lemma verification_body_lemma(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool, f':map<map<Question, Answer>, bool>, g':map<map<Question, Answer>, int>, candidates:set<map<Question, Answer>>, candidate:map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)

requires !candidates_empty_
requires candidates_ <= f.Keys
requires candidate in candidates_
requires candidates <= candidates_
requires forall m | m in g'.Keys :: m in g.Keys
requires candidates == candidates_ - {candidate}
requires  f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]
requires  g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person]
requires okFit == okFitness(f')
requires okPriv == okPrivate(g', P, a, b, Q)

requires verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates_,R_)
requires R == (R_ && okFit && okPriv)

ensures verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates,R)
{
  // Hipótesis 
  assert 
    R_ == (forall candidate:map<Question, Answer> | candidate in (f - candidates_) :: 
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )) by { reveal verification_invariant_verifyPathCDPC(); }


  // Este lema demuestra que se cumple que el cuerpo del bucle es correcto. Es decir, demuestra que los cambios que han ocurrido desde el inicio del cuerpo (desde el valor anterior de R; R_) han tenido el efecto deseado
  start_of_loop_values_match_with_end_of_loop_values_body_lemma(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates_empty_, i_, R_, f', g', candidates, candidate, okFit, okPriv, R) by {
    //reveal invariant_body_loop();
  }


  assert (f.Keys - candidates) == (f.Keys - candidates_) + (candidates_ - candidates) by {
    //reveal invariant_body_loop();
    assert candidates == candidates_ - {candidate};
    assert (candidates_ - candidates) == {candidate};
    assert (f.Keys - candidates) == (f.Keys - candidates_) + {candidate};
  }

  // Junta la hipótesis inductiva y el lema anterior, demostrando que si el forall se cumple para (f.Keys - candidates_) y para (candidates_ - candidates)
  // entonces, como (f.Keys - candidates) == (f.Keys - candidates_) + (candidates_ - candidates), se cumple para (f.Keys - candidates)
  forall_of_two_sets_equals_forall_of_combined_sets_body_lemma(f, g, P, k, a, b, Q, questionsToVerify, candidates_, candidates_empty_, i_, R_, f', g', candidates, candidate, okFit, okPriv, R);

  // Se aserta la poscondición del lema, que es justo lo que queremos obtener
  assert
    ((forall candidate:map<Question, Answer> | candidate in (f - candidates_) :: 
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))
    &&
    (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )))
    ==
    (forall candidate:map<Question, Answer> | candidate in (f - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ));
  
  /*calc{
    R;
   R_ && okFit && okPriv;
   
   (forall candidate:map<Question, Answer> | candidate in (f - candidates_) :: 
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )) && okFitness(f') && okPrivate(g', P, a, b, Q);
    (forall candidate:map<Question, Answer> | candidate in (f - candidates_) :: 
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    )) && (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ));
    (forall candidate:map<Question, Answer> | candidate in (f - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ));
  }*/
  verification_loop_recover(f,g,P, k, a, b, Q, questionsToVerify, candidates,R);  
}



lemma forall_of_two_sets_equals_forall_of_combined_sets_body_lemma(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool, f':map<map<Question, Answer>, bool>, g':map<map<Question, Answer>, int>, candidates:set<map<Question, Answer>>, candidate:map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)
requires (f.Keys - candidates) == (f.Keys - candidates_) + (candidates_ - candidates)
ensures
  ((forall candidate:map<Question, Answer> | candidate in (f.Keys - candidates_) :: 
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  ))
  &&
  (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  )))
  ==
  (forall candidate:map<Question, Answer> | candidate in (f.Keys - candidates) ::
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  ))
{
  assert
  (
    (forall candidate:map<Question, Answer> | candidate in (f.Keys - candidates_) :: 
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))
    &&
    (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))
  )
    ==
    (forall candidate:map<Question, Answer> | candidate in ((f.Keys - candidates_) + (candidates_ - candidates)) ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))
    ;
  assert (f.Keys - candidates) == (f.Keys - candidates_) + (candidates_ - candidates);
}


lemma start_of_loop_values_match_with_end_of_loop_values_body_lemma(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, questionsToVerify:set<Question>,
candidates_:set<map<Question, Answer>>, candidates_empty_:bool, i_:nat, R_:bool, f':map<map<Question, Answer>, bool>, g':map<map<Question, Answer>, int>, candidates:set<map<Question, Answer>>, candidate:map<Question, Answer>, okFit:bool, okPriv:bool, R:bool)
requires problem_requirements_path(f, g, P, k, a, b, Q, questionsToVerify)

requires !candidates_empty_
requires candidates_ <= f.Keys
//requires auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_)

requires candidate in candidates_
requires candidates <= candidates_
requires forall m | m in g'.Keys :: m in g.Keys
requires candidates == candidates_ - {candidate}
requires  f' == map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person]
requires  g' == map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person]
requires okFit == okFitness(f')
requires okPriv == okPrivate(g', P, a, b, Q)
requires verification_invariant_verifyPathCDPC(f, g, P, k, a, b, Q, questionsToVerify, candidates_,R_)
requires R == (R_ && okFit && okPriv)

ensures R == (R_ && (forall candidate:map<Question, Answer> | candidate in (candidates_ - candidates) ::
  (
    var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: f[person];
    var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in questionsToVerify :: person[q] == candidate[q]) :: g[person];
    okFitness(f') && okPrivate(g', P, a, b, Q)
  )))
{
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

    assert {candidate} == (candidates_ - candidates) by {
      assert candidates == candidates_ - {candidate};
    }

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
        reveal auxiliary_invariant_verifyPathCDPC(f, g, P, Q, candidates_, candidates_empty_, i_);

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
    }
  }
}

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



lemma lemma_equal_definition(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, A:set<Answer>, interview:Interview, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q)
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
requires requires_of_the_postcondition(f, g, P, k, a, b, Q, A, interview, R)    //(forall path:set<Question> | path in pathsInterview(interview, k) :: path <= Q)
requires postcondition(f, g, P, k, a, b, Q, A, interview, R)
ensures R == CDPCLim(f, g, P, k, a, b, Q)
{
  assert R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: verification(f, g, P, k, a, b, Q, path)) by { reveal postcondition();  }

  reveal verification();
  
  assert R ==
    (forall path:set<Question> | path in pathsInterview(interview, k, Q) ::
      ((|path| <= k) &&
      (forall candidate:map<Question, Answer> | candidate in f ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      )))
    );



  assert R == CDPCLim(f, g, P, k, a, b, Q)
  by {

    assert R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: 
      ((|path| <= k) &&
      (forall candidate:map<Question, Answer> | candidate in f ::
      (
        var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: f[person];
        var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: g[person];
        okFitness(f') && okPrivate(g', P, a, b, Q)
      ))))
    by {
      assert postcondition(f, g, P, k, a, b, Q, A, interview, R);

      assert R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: verification(f, g, P, k, a, b, Q, path));

      assert (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: verification(f, g, P, k, a, b, Q, path)) ==
              (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: 
              ((|path| <= k) &&
              (forall candidate:map<Question, Answer> | candidate in f ::
              (
                var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: f[person];
                var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: g[person];
                okFitness(f') && okPrivate(g', P, a, b, Q)
              ))));
    }


    assert R == (okPrivate(g, P, a, b, Q) &&
      if k == 0 then
        okFitness(f)
      else
        okFitness(f) ||
        exists i:Question | i in Q ::
          forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
            CDPCLim(
              restrictMap(f, i, o),
              restrictMap(g, i, o),
              P, k - 1, a, b, Q
            ))
    by {
      assert R == (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: 
        ((|path| <= k) &&
        (forall candidate:map<Question, Answer> | candidate in f ::
        (
          var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: f[person];
          var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: g[person];
          okFitness(f') && okPrivate(g', P, a, b, Q)
        ))));
      lemma_equals_aux(f, g, P, k, a, b, Q, A, interview, R);
      assume false;
    }
    
    assert
      CDPCLim(f, g, P, k, a, b, Q)
      ==
      (okPrivate(g, P, a, b, Q) &&
      if k == 0 then
        okFitness(f)
      else
        okFitness(f) ||
        exists i:Question | i in Q ::
          forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
            CDPCLim(
              restrictMap(f, i, o),
              restrictMap(g, i, o),
              P, k - 1, a, b, Q
            ))
      by {
        
        //reveal CDPCLim();
        assert problem_requirements(f, g, P, k, a, b, Q);
        assert forall m | m in g.Keys :: m.Keys == Q;
        assert f.Keys == g.Keys;
        assert P <= Q;
        assert 0.0 <= a <= b <= 1.0;
        assert 0 <= k <= |Q|;
        lemma_unwrap_CDPCLim(f, g, P, k, a, b, Q);

        assume false;
      }

    assert R == CDPCLim(f, g, P, k, a, b, Q);

    assume false;
  }

}



lemma lemma_unwrap_CDPCLim(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  requires problem_requirements(f, g, P, k, a, b, Q)
  ensures
    CDPCLim(f, g, P, k, a, b, Q)
    ==
    (okPrivate(g, P, a, b, Q) &&
    if k == 0 then
      okFitness(f)
    else
      okFitness(f) ||
      exists i:Question | i in Q ::
        forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
          CDPCLim(
            restrictMap(f, i, o),
            restrictMap(g, i, o),
            P, k - 1, a, b, Q
          ))
{
  reveal CDPCLim();
  assume false;
}


lemma lemma_equals_aux(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>, A:set<Answer>, interview:Interview, R:bool)
requires problem_requirements(f, g, P, k, a, b, Q)
requires correctSizeInterview(interview, k)
requires correctQuestionsInterview(interview, k, Q)
requires requires_of_the_postcondition(f, g, P, k, a, b, Q, A, interview, R)
requires postcondition(f, g, P, k, a, b, Q, A, interview, R)
ensures
  (forall path:set<Question> | path in pathsInterview(interview, k, Q) :: 
    ((|path| <= k) &&
    (forall candidate:map<Question, Answer> | candidate in f ::
    (
      var f' := map person:map<Question, Answer> | person in f.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: f[person];
      var g' := map person:map<Question, Answer> | person in g.Keys && (forall q:Question | q in path :: person[q] == candidate[q]) :: g[person];
      okFitness(f') && okPrivate(g', P, a, b, Q)
    ))))
  ==
  (okPrivate(g, P, a, b, Q) &&
    if k == 0 then
      okFitness(f)
    else
      okFitness(f) ||
      exists i:Question | i in Q ::
        forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
          CDPCLim(
            restrictMap(f, i, o),
            restrictMap(g, i, o),
            P, k - 1, a, b, Q
          ))
{
  assume false;
}


}
