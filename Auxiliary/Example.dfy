ghost function fib ( n : int ): int
decreases n
requires n >= 0
{ if (n == 0) then 0
  else if (n == 1) then 1
  else fib(n-1) + fib(n-2)
}

lemma {:induction n} fibOddOddEven(n : int)
requires n >= 1 && n % 3 == 1
ensures fib(n) % 2 == 1 &&  fib(n + 1) % 2 == 1 && fib(n + 2) % 2 == 0
{}

method Fibonacci( n : int) returns ( r : int)
requires n >= 0
ensures r == fib(n)
{
    var i := 0; var x := 0; var y := 1;
    while i < n
     decreases n - i
     invariant 0 <= i <= n 
     invariant x == fib(i)
     invariant y == fib(i+1)
     { x, y := y, x + y;
       assert x == fib(i+1);
       i := i + 1;
     }
    r := x;

}