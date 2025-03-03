
method pick<T>(S:set<T>, counter_in:int) returns (r:T, counter_out:int)
  requires |S| > 0
  ensures counter_out == counter_in + 1
  ensures r in S
{
  var v :| v in S;
  return v, counter_in + 1;
}

method add<T>(S:set<T>, e:T, counter_in:int) returns (r:set<T>, counter_out:int)
  ensures counter_out == counter_in + |S|
  ensures  r == S + {e}
{
  r := S + {e};
  return r, counter_in + |S|;
}

method remove<T>(S:set<T>, e:T, counter_in:int) returns (r:set<T>, counter_out:int)
  ensures counter_out == counter_in + |S|
  ensures  r == S - {e}
{
  r := S - {e};
  return r, counter_in + |S|;
}
