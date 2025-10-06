
  
ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
requires forall s | s in S :: s <= U // los sets son subsets del universo
requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

/*
method verifySetCover_no_modular<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool)   
requires forall s | s in S :: s <= U
ensures b == (I <= S && isCover(U, I) && |I| <= k)
{
  var U' := U;
  var b1:= true;

  while (U' != {} && b1)
    invariant U' <= U 
    invariant b1 == isCover(U-U',I)
  {
   ghost var prevU' := U';
   var u :| u in U'; 
   U' := U' - {u};  

   var I' := I; var b2:= false;
   while (I' != {} && !b2)
     invariant I' <= I
     invariant b2 == (exists i' | i' in I - I' :: u in i')
   { 
      var i :| i in I'; 
      b2 := u in i;
      I':= I' - {i};
   }
   b1 := b1 && b2;
   assert U - U' == U - prevU' + {u}; 
  }
  assert b1 ==> U' == {} &&  U-U' == U;
  b := b1 && I <= S && |I| <= k ;
}
*/

