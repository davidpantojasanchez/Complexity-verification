
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


