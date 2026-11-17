// Shared native instance data for Set Cover and Hitting Set.
datatype SetSystemModel<T> = SetSystemModel(universe:set<T>, sets:set<set<T>>, k:nat)

ghost predicate SetSystemMembersWithinUniverse<T>(universe:set<T>, sets:set<set<T>>)
{
  forall s | s in sets :: s <= universe
}
