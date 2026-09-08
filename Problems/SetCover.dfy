
// Convencion del dominio: una instancia de Set Cover solo es valida si la familia
// completa puede cubrir el universo. Por tanto, una familia que no lo cubre queda
// fuera del dominio; no representa una instancia valida negativa. SetCover decide
// si, dentro de ese dominio, existe una cobertura de cardinalidad a lo sumo k.
// k puede ser cualquier natural; no se exige una cota superior.
ghost predicate SetCover<T>(universe:set<T>, sets: set<set<T>>, cardinality:nat)
  requires SetCoverValidInstance(universe, sets)
{
  exists C:set<set<T>> | C <= sets :: SetCoverCertificate(universe, sets, cardinality, C)
}

ghost predicate SetCoverValidInstance<T>(universe:set<T>, sets:set<set<T>>)
{
  (forall s | s in sets :: s <= universe) && isCover(universe, sets)
}

// Admissibility bounds individual sets, but does not assert inclusion or coverage.
ghost predicate SetCoverAdmissibleCertificate<T>(universe:set<T>, cover:set<set<T>>)
{
  forall s | s in cover :: |s| <= |universe|
}

ghost predicate SetCoverCertificate<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
{
  cover <= sets && isCover(universe, cover) && |cover| <= cardinality
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}
  
