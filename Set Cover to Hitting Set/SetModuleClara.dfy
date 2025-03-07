
module SetMod {

  method Pick<T>(S:set<T>, ghost sizeT:nat, ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires S != {}
    ensures counter_out == counter_in + time_Pick(S,sizeT)
    ensures e in S
  

  ghost function time_Pick<T>(S:set<T>, sizeT:nat) : int { sizeT }

  method Empty<T>(S:set<T>, ghost counter_in:nat) returns (b: bool, ghost counter_out:nat)
    ensures b == (S == {})
    ensures counter_out == counter_in + 1
  

  method Size<T>(S:set<T>, ghost counter_in:nat) returns (size: int, ghost counter_out:nat)
    ensures  size == |S|
    ensures counter_out == counter_in + 1
  


  method Add<T>(S:set<T>, e:T,ghost sizeT:nat, ghost counter_in:nat) returns (R:set<T>, ghost counter_out:nat)
    ensures  R == S + {e}
    ensures if e in S then |R| == |S|
            else |R| == |S| + 1
    ensures counter_out == counter_in + time_add(S,sizeT)


  ghost function time_add<T>(S:set<T>, sizeT:nat) : int { |S|*sizeT }


  method Remove<T>(S:set<T>, e:T, ghost sizeT:nat, ghost counter_in:nat) returns (R:set<T>, ghost counter_out:nat)
    ensures  R == S - {e}
    ensures if e !in S then |R| == |S|
            else |R| == |S| - 1
    ensures counter_out == counter_in + time_Remove(S,sizeT);
  

  ghost function time_Remove<T>(S:set<T>, sizeT:nat) : int { |S|*sizeT }


  method Contains<T>(S:set<T>, e:T, ghost sizeT:nat, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    ensures  b == (e in S) 
    ensures counter_out == counter_in + time_Contains(S,sizeT)

  ghost function time_Contains<T>(S:set<T>, sizeT:nat) : int { |S|*sizeT }


}
