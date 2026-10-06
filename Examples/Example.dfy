
ghost function Fib(n:int) : int
  decreases n
  requires n >= 0
{
  if (n == 0) then 0
  else if (n == 1) then 1
  else Fib(n-1) + Fib(n-2)
}

/*lemma {:induction n} FibOddOddEven(n:int)
  requires n >= 1 && n % 3 == 1
  ensures Fib(n) % 2 == 1 &&  Fib(n + 1) % 2 == 1 && Fib(n + 2) % 2 == 0
{}*/
lemma FibOddOddEven(n:int)
  decreases n
  requires n >= 1 && n % 3 == 1
  ensures Fib(n) % 2 == 1 &&  Fib(n + 1) % 2 == 1 && Fib(n + 2) % 2 == 0
{
  if n == 1 {
    assert Fib(1) == 1 && Fib(2) == 1 && Fib(3) == 2;
  }
  else {
    assert n >= 4;
    assert (n - 3) % 3 == 1;
    FibOddOddEven(n - 3);
  }
}

method Fibonacci(n:int) returns (r:int)
  requires n >= 0
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
