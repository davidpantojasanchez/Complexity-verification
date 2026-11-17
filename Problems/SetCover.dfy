include "../Foundations/CollectionLaws.dfy"
include "SetSystem.dfy"

type SetCoverModel<T> = SetSystemModel<T>


// Convencion del dominio: una instancia de Set Cover solo es valida si la familia
// completa puede cubrir el universo. Por tanto, una familia que no lo cubre queda
// fuera del dominio; no representa una instancia valida negativa. SetCover decide
// si, dentro de ese dominio, existe una cobertura de cardinalidad a lo sumo k.
// k puede ser cualquier natural; no se exige una cota superior.
ghost predicate SetCover<T>(instance:SetCoverModel<T>)
  requires SetCoverValidInstance(instance)
{
  exists cover:set<set<T>> | cover <= instance.sets :: SetCoverCertificate(instance, cover)
}

ghost predicate SetCoverValidInstance<T>(instance:SetCoverModel<T>)
{
  SetCoverFamilyValid(instance.universe, instance.sets)
}

ghost predicate SetCoverFamilyValid<T>(universe:set<T>, sets:set<set<T>>)
{
  SetSystemMembersWithinUniverse(universe, sets) && IsCover(universe, sets)
}

ghost predicate SetCoverCertificate<T>(instance:SetCoverModel<T>, cover:set<set<T>>)
{
  cover <= instance.sets && IsCover(instance.universe, cover) && |cover| <= instance.k
}

ghost predicate IsCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}

lemma set_cover_certificate_cardinality_bounds<T>(instance:SetCoverModel<T>, cover:set<set<T>>)
  requires SetCoverValidInstance(instance)
  requires SetCoverCertificate(instance, cover)
  ensures |cover| <= |instance.sets|
  ensures forall s | s in cover :: |s| <= |instance.universe|
{
  subset_cardinality_bound_set(cover, instance.sets);
  forall s | s in cover ensures |s| <= |instance.universe| {
    subset_cardinality_bound_set(s, instance.universe);
  }
}
