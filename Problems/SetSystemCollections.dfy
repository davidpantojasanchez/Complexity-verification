include "SetCover.dfy"
include "HittingSet.dfy"
include "../Collections/Set.dfy"

// Representation aliases carry no validity guarantee. Compound labels retain
// specialized interfaces; these aliases do not supply a label adapter.
type SetCoverIntInstance = (Set<int>, SetSet<int>, nat)
type HittingSetIntInstance = (Set<int>, SetSet<int>, nat)
type SetCoverSetIntInstance = (SetSet<int>, SetSetSet<int>, nat)
