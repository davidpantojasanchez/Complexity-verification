include "Auxiliary.dfy"
include "Problems.dfy"

// * LA TRANSFORMACIÓN ES CORRECTA

abstract module ReductionCDPClim {
  import opened Auxiliary
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



// ATDP-Intermediate ==> CDPC-Limit

lemma {:induction false} DATDPintermediateImpliesCDPCLim(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>,k: int, I: set<Question>)
  decreases k
  requires PredDATDPintermediate(C, f, k, I)
  ensures 
    reveal PredDATDPintermediate(); CDPCLim(f, quantity(C, I), {}, k, 0.0, 1.0, I)
{
  if (k==0) {
    reveal PredDATDPintermediate();
    assert CDPCLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) by { reveal DATDPintermediate(); reveal CDPCLim(); }
  }
  else {
    assert f.Keys == C by { reveal PredDATDPintermediate(); }
    assert 0 <= k <= |I| by { reveal PredDATDPintermediate(); }
    assert (forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I) by { reveal PredDATDPintermediate(); }
    assert DATDPintermediate(C, f, k, I) by { reveal PredDATDPintermediate(); }
    assert okPrivate(quantity(C, I), {}, 0.0, 1.0, I);

    if (okFitness(f)) {
      // Si okFitness(f), CDPCLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) es trivialmente cierto
    }
    else {
      //Por definicion de DATDPintermediate(C, f, k, i), sé que existe un i :
      reveal DATDPintermediate();
      var i: Question :| i in I &&
        forall o: Answer | o in (set m: map<Question, Answer> | m in C :: m[i]) ::
          DATDPintermediate(restrictSet(C, i, o), restrictMap(f, i, o), k - 1, I);
      // Vamos a demostrar CDPCLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) usando dicho i
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) 
      ensures CDPCLim(restrictMap(f, i, o), restrictMap(quantity(C, I), i, o), {}, k - 1, 0.0, 1.0, I)
      {
        var C1 := restrictSet(C, i, o);
        var f1 := restrictMap(f, i, o);

        assert PredDATDPintermediate(C1, f1, k - 1, I) by { reveal PredDATDPintermediate(); }
        DATDPintermediateImpliesCDPCLim(C1,f1,k-1,I);
        assert CDPCLim(f1, quantity(C1, I),{},k-1, 0.0, 1.0, I);

        assert restrictMap(quantity(C, I), i, o) == quantity(C1, I);
      }
    }
    assert CDPCLim(f, quantity(C, I), {}, k, 0.0, 1.0, I) by { reveal CDPCLim(); }
  }
}


// DATDP-Intermediate <== CDPCLimit


ghost predicate {:opaque} PredCDPCLim(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>) {
  (forall m | m in g.Keys :: m.Keys == Q)
  && f.Keys == g.Keys
  && P <= Q
  && 0.0 <= a <= b <= 1.0
  && 0 <= k <= |Q|
  && CDPCLim(f, g, P, k, a, b, Q)
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

lemma {:induction false} CDPCLimImpliesDATDPintermediate(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  decreases k
  requires PredCDPCLim(f, g, P, k, a, b, Q)
  requires P == {}
  ensures 
    reveal PredCDPCLim(); DATDPintermediate(g.Keys, f, k, Q)
{
  if (k==0) {
    reveal PredCDPCLim();
    assert forall m:map<Question, Answer> | m in f.Keys :: f[m] in f.Values;
    assert separatedMixed(g.Keys, f) == okFitness(f);
    assert DATDPintermediate(g.Keys, f, k, Q) by { reveal CDPCLim(); reveal DATDPintermediate(); }
  }
  else {
    assert  (forall m | m in g.Keys :: m.Keys == Q)
            && f.Keys == g.Keys
            && P <= Q
            && 0.0 <= a <= b <= 1.0
            && 0 <= k <= |Q| by { reveal PredCDPCLim(); }
    assert CDPCLim(f, g, P, k, a, b, Q) by {
      reveal PredCDPCLim();
    }
    assert okPrivate(g, P, 0.0, 1.0, Q);
    
    if (okFitness(f)) {
      // Vamos a demostrar que okFitness(f) implica separatedMixed(g.Keys, f)
      var C := g.Keys;
      reveal PredCDPCLim();
      assert f.Keys == C;
      assert forall m:map<Question, Answer> | m in f.Keys :: f[m] in f.Values;
      assert (forall m:map<Question, Answer> | m in C :: f[m]) || (forall m:map<Question, Answer> | m in C :: !f[m]);
      assert separatedMixed(C, f);
      // Todas las instancias de D-ATDP-intermediate en las que separatedMixed() es cierto son ciertas
      separationPersists(C, f, k, Q);
      // Por lo tanto, DATDPintermediate(g.Keys, f, k, Q) es cierto
    }
    else {
      //Por definicion de CDPCLim(f, g, P, k, a, b, Q), sé que existe un i :
      reveal CDPCLim();
      var i: Question :| i in Q &&
        forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
          CDPCLim(
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

        assert PredCDPCLim(f1, g1, P, k - 1, a, b, Q) by { reveal PredCDPCLim(); }
        CDPCLimImpliesDATDPintermediate(f1, g1, P, k - 1, a, b, Q);
        assert DATDPintermediate(g1.Keys, f1, k - 1, Q);

        assert restrictSet(g.Keys, i, o) == g1.Keys;
      }
    }
    assert DATDPintermediate(g.Keys, f, k, Q) by { reveal DATDPintermediate(); }
  }
}


// DATDP reduces to CDPC-Limit


lemma DATDPreducesToCDPCLim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>)
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  ensures DATDP(C, E, k, I) == CDPCLim(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
{
  //reveal PredDATDP();
  //reveal PredDATDPintermediate();
  //reveal PredCDPCLim();
  if (DATDP(C, E, k, I)) {
    reveal PredDATDP();
    reveal PredDATDPintermediate();
    reveal PredCDPCLim();
    DATDPimpliesDATDPintermediate(C, E, k, I);
    assert DATDPintermediate(C, fitness(C, E, I), k, I);
    DATDPintermediateImpliesCDPCLim(C, fitness(C, E, I), k , I);
  }
  else if CDPCLim(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I) {
    CDPCLimImpliesDATDPintermediate(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I) by {
      reveal PredCDPCLim();
    }
    assert DATDPintermediate(quantity(C, I).Keys, fitness(C, E, I), k, I) by {
      reveal PredDATDPintermediate();
    }
    assert C == quantity(C, I).Keys;
    DATDPintermediateimpliesDATDP(C, fitness(C, E, I), k, I) by {
      reveal PredDATDP();
      reveal PredDATDPintermediate();
    }
    assert DATDP(C, correctSpecifications(C, fitness(C, E, I), I), k, I);

    assert correctSpecifications(C, fitness(C, E, I), I) == E by {
      //reveal DATDPintermediate();
      assert correctSpecifications(C, fitness(C, E, I), I) == set candidate | candidate in fitness(C, E, I).Keys && (fitness(C, E, I)[candidate]) :: candidate;
      //assert (set candidate | candidate in fitness(C, E, I).Keys && (fitness(C, E, I)[candidate]) :: candidate)
      //    == (set candidate | candidate in fitness(C, E, I).Keys && candidate in E :: candidate);
      assert fitness(C, E, I).Keys == C;  // ?
      assert forall candidate | candidate in fitness(C, E, I).Keys :: candidate in C;
      assert (set candidate | candidate in fitness(C, E, I).Keys && candidate in E :: candidate)
          == (set candidate | candidate in E :: candidate);
    }

    assert DATDP(C, E, k, I);
  }
}


function DATDP_to_CDPClim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>) : (r:(map<map<Question, Answer>, bool>, map<map<Question, Answer>, int>, set<Question>, int, real, real, set<Question>))
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  ensures DATDP(C, E, k, I) == CDPCLim(fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
{
  DATDPreducesToCDPCLim(C, E, k, I);
  (fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
}



}