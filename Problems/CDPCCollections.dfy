include "CDPCRepresentation.dfy"
include "../Collections/Set.dfy"
include "../Collections/Map.dfy"

// These aliases imply neither CDPCValidInstance nor reduction correspondence.
// The compound-label representation still needs its pending label adapter.
type CDPCAtomicInstance<Q(!new)> = (Set<Q>, Map_Map_T<Q, bool, bool>,
  Map_Map_T<Q, bool, nat>, Set<Q>, Rational, Rational, Rational, Rational)
type CDPCSetIntInstance = (SetSet<int>, Map_MapSet_T<int, bool, bool>,
  Map_MapSet_T<int, bool, nat>, SetSet<int>, Rational, Rational, Rational, Rational)
