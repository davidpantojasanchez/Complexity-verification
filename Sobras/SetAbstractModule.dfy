
abstract module ASet {

  type T 
  type ASet<T(!new)>
  ghost function sizeT(): nat
  ghost function size<T(!new)>(S: ASet<T>): nat
  ghost function Model<T(!new)>(S: ASet<T>): set<T>


  method pick<T(!new)>(S:ASet<T>, ghost counter_in:int) returns (e:T, ghost counter_out:int)
    requires size<T>(S) > 0
    ensures counter_out == counter_in + sizeT()
    ensures e in Model(S)
  
  ghost function time_pick<T>(S:set<T>, sizeT:int) : int { sizeT }

  method add<T(!new)>(S:ASet<T>, e:T, ghost counter_in:int) returns (R:ASet<T>, ghost counter_out:int)
    ensures counter_out == counter_in + size<T>(S) * sizeT()
    ensures  Model(R) == Model(S) + {e}
  
  ghost function time_add<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


  method remove<T(!new)>(S:ASet<T>, e:T, ghost counter_in:int) returns (R:ASet<T>, ghost counter_out:int)
    ensures counter_out == counter_in + size<T>(S)*sizeT()
    ensures  Model(R) == Model(S) - {e}
  
  ghost function time_remove<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


  method contains<T(!new)>(S:ASet<T>, e:T, ghost counter_in:int) returns (b:bool, ghost counter_out:int)
    ensures counter_out == counter_in + size<T>(S)*sizeT()
    ensures  b == (e in Model(S)) 
  
  ghost function time_contains<T>(S:set<T>, sizeT:int) : int { |S|*sizeT }


}


module SetOfInt refines ASet{

type T = int 
datatype ASet<T(!new)> = TS (s:set<int>)
 ghost function sizeT(): nat {1}
 ghost function size<T(!new)>(S: ASet<T>): nat {match S case TS(s) => |s|}
 ghost function Model<T(!new)>(S:ASet<T>): set<T> 





}