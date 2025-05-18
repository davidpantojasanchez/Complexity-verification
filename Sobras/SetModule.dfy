
module SetMod {

  method pick<T>(S:set<T>, ghost sizeT:int, ghost counter_in:int) returns (r:T, ghost counter_out:int)
    requires |S| > 0
    ensures counter_out == counter_in + sizeT
    ensures r in S
  {
    var v :| v in S;
    return v, counter_in + sizeT;
  }
  ghost function time_pick<T>(S:set<T>, sizeT:int) : int { sizeT }

  method add<T>(S:set<T>, e:T,ghost sizeT:int, ghost counter_in:int) returns (r:set<T>, ghost counter_out:int)
    ensures counter_out == counter_in + |S|*sizeT
    ensures  r == S + {e}
  {
    r := S + {e};
    return r, counter_in + |S|*sizeT;
  }
  ghost function time_add<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


  method remove<T>(S:set<T>, e:T, ghost sizeT:int, ghost counter_in:int) returns (r:set<T>, ghost counter_out:int)
    ensures counter_out == counter_in + |S|*sizeT
    ensures  r == S - {e}
  {
    r := S - {e};
    return r, counter_in + |S|*sizeT;
  }
  ghost function time_remove<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


  method contains<T>(S:set<T>, e:T, ghost sizeT:int, ghost counter_in:int) returns (r:bool, ghost counter_out:int)
    ensures counter_out == counter_in + |S|*sizeT
    ensures  r == (e in S) 
  {
    r := e in S;
    return r, counter_in + |S|*sizeT;
  }
  ghost function time_contains<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


}
