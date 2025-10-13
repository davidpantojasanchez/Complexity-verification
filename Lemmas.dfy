
lemma mult_preserves_order(a:int, b:int, a':int, b':int)  // Creo que ya no se usa
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{
}


lemma identity_substraction_lemma<T>(S:set<T>, E:set<T>)
requires E == {}
ensures S - E == S
{}


lemma if_smaller_then_less_cardinality<T>(A:set<T>, B:set<T>)
requires A <= B
ensures |A| <= |B|
{
  if (A == {}) {
  }
  else {
    var a :| a in A && a in B;
    if_smaller_then_less_cardinality(A - {a}, B - {a});
  }
}

