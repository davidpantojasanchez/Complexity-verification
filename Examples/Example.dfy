
ghost function Fib(n:int) : int
  decreases n
  requires 0 <= n
{
  if (n == 0) then 0
  else if (n == 1) then 1
  else Fib(n-1) + Fib(n-2)
}

/*lemma {:induction n} fib_odd_odd_even(n:int)
  requires 1 <= n && n % 3 == 1
  ensures Fib(n) % 2 == 1 &&  Fib(n + 1) % 2 == 1 && Fib(n + 2) % 2 == 0
{}*/
lemma fib_odd_odd_even(n:int)
  decreases n
  requires 1 <= n && n % 3 == 1
  ensures Fib(n) % 2 == 1 &&  Fib(n + 1) % 2 == 1 && Fib(n + 2) % 2 == 0
{
  if n == 1 {
    assert Fib(1) == 1 && Fib(2) == 1 && Fib(3) == 2;
  }
  else {
    assert 4 <= n;
    assert (n - 3) % 3 == 1;
    fib_odd_odd_even(n - 3);
  }
}

method Fibonacci(n:int) returns (r:int)
  requires 0 <= n
  ensures r == Fib(n)
{
  var i := 0; var x := 0; var y := 1;
  while i < n
    decreases n - i
    invariant 0 <= i <= n 
    invariant x == Fib(i)
    invariant y == Fib(i+1)
  {
    x, y := y, x + y;
    assert x == Fib(i+1);
    i := i + 1;
  }
  r := x;
}
