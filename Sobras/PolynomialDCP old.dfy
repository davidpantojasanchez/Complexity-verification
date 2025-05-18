
include "reduction.dfy"
include "SetOperations.dfy"


function DATDP_to_PCDLim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>) :
(r:(map<map<Question, Answer>, bool>, map<map<Question, Answer>, int>, set<Question>, int, real, real, set<Question>))
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
{
  (fitness(C, E, I), quantity(C, I), {}, k, 0.0, 1.0, I)
}

method method_DATDP_to_PCDLim(C: set<map<Question, Answer>>, E: set<map<Question, Answer>>, k: int, I: set<Question>)
returns (r:(map<map<Question, Answer>, bool>, map<map<Question, Answer>, int>, set<Question>, int, real, real, set<Question>), counter:int)
  requires E <= C
  requires 0 <= k <= |I|
  requires (forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I)
  ensures r == DATDP_to_PCDLim(C, E, k, I)
  //ensures counter <= (|E| + 1) * |C|
  ensures counter <= (|E| + 2) * |C|
{
  counter := 0;
  var P:set<Question> := {};
  var a:real := 0.0;
  var b:real := 1.0;

  var f:map<map<Question, Answer>, bool> := map[];
  var g:map<map<Question, Answer>, int> := map[];

  var C2 := C;

  ghost var prev_C := C;
  ghost var prev_f := f;
  ghost var prev_C2 := C2;
  while 0 < |C2|
    decreases |C2|
    invariant f.Keys == (C - C2)
    invariant prev_f.Keys <= f.Keys
    invariant forall c | c in prev_f.Keys :: f[c] == prev_f[c]
    invariant forall c | c in (C - C2) :: f[c] == (c in E)

    invariant prev_C == C
    invariant C2 <= C

    invariant counter == (|E| + 1) * (|C| - |C2|)
    //invariant counter == (|E| + 2) * (|C| - |C2|) //+ (|C| - |C2|)
  {
    ghost var prevCounter := counter;
    prev_C2 := C2;
    prev_f := f;
    counter := counter + 1;

    //var c :| c in C2;
    var c, counter := pick(C2, counter);

    //ghost var prevCounter := counter;

    assert !(c in prev_f.Keys);
    f := f[c := false];
    g := g[c := 0];
    var E2 := E;

    assert C2 <= C;
    assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];

    assert counter == prevCounter + 2 + |E| - |E2|;

    while 0 < |E2|
      decreases |E2|

      invariant E2 <= E
      invariant c in f
      invariant c in E ==> (c in E2 || f[c])
      invariant f[c] ==> c in E

      invariant c in g
      invariant f[c] == (g[c] == 1)

      invariant f.Keys == (C - C2) + {c}

      invariant forall c | c in prev_f.Keys :: f[c] == prev_f[c]

      invariant C2 <= C

      invariant counter == prevCounter + 2 + |E| - |E2|

      invariant forall c | c in (C - C2) :: f[c] == (c in E)
    {
      counter := counter + 1;

      var e :| e in E2;
      E2 := E2 - {e};
      if c == e {
        f := f[c := true];
        g := g[c := 1];
      }
    }
    assert counter == prevCounter + 2 + |E|;

    assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];

    assert f[c] == (c in E);
    assert f.Keys == (C - C2) + {c};
    ghost var prevC2 := C2;
    assert f.Keys == (C - prevC2) + {c};

    assert C2 <= C;

    

    C2 := C2 - {c};
    assert c in C;
    assert c in (C - C2);
    assert f.Keys == (C - prevC2) + {c};
    assert prevC2 == C2 + {c};
    assert f.Keys == (C - (C2 + {c})) + {c};
    
    assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];

    assert (C - (C2 + {c})) == (C - C2 - {c});
    assert f.Keys == C - C2 - {c} + {c};
    assert c in (C - C2);
    assert f.Keys == (C - C2);
    
    
    
    assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];      // repetido varias veces, para recordárselo a Dafny

    assert C2 <= C;
    
    
    assert f.Keys == (C - C2);
    assert prev_f.Keys <= f.Keys;


    assert forall c | c in prev_f.Keys :: f[c] == prev_f[c];

    
    assert forall c | c in (C - C2) :: f[c] == (c in E);
    assert prev_C == C;
    assert C2 <= C;
    
    //assert counter == (|E| + 1) * (|C| - |C2|);
    assert counter == (|E| + 2) * (|C| - |C2|);// + (|C| - |C2|);
  }
  //assume false;
  assert counter == (|E| + 2) * |C|;

  assert f == fitness(C, E, I);
  r := (f, quantity(C, I), P, k, a, b, I);
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
