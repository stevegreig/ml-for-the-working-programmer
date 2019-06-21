## Chapter 2

__2.1.__ The command for invoking ML is operating-system dependent. Most compilers offer the use command, but it is not part of the language.

__2.2.__ Advantages of a single type of numbers: eliminates overloaded operators; fewer concepts to remember. Disadvantages: confuses (exact) integers with (inexact) reals; type conversions at run time may be unpredictable; probably less efficient at run-time.

__2.3.__ Only g needs one, since ~ and * are both overloaded for types int and real. The constant 2 constrains the type of double while Math.sin constrains that of f.

Now that ML supports default overloading, even the declaration of g is accepted. It is assumed to use type int.

__2.4.__ The first version returns #"/" and #":", which are the characters just outside the range of digits in the ASCII character set. The second version reports an error, by raising exception Subscript.

__2.5.__

```
1<=d andalso 
(m = "January"   andalso d<=31  orelse
 m = "February"  andalso d<=28  orelse
 m = "March"     andalso d<=31  orelse
 m = "April"     andalso d<=30  orelse
 m = "May"       andalso d<=31  orelse
 m = "June"      andalso d<=30  orelse
 m = "July"      andalso d<=31  orelse
 m = "August"    andalso d<=31  orelse
 m = "September" andalso d<=30  orelse
 m = "October"   andalso d<=31  orelse
 m = "November"  andalso d<=30  orelse
 m = "December"  andalso d<=31)
 ```
 
 __2.6.__ This is just lexicographic ordering on triples.

```
fun earlier ((h1, m1, apm1), (h2:int, m2:int, apm2)) =
  apm1 = "AM" andalso apm2 = "PM"
  orelse apm1=apm2 andalso (h1<h2 orelse h1=h2 andalso m1<m2);
```

__2.7.__ Variable l stands for pounds and d stands for pence.

```
fun quorem (m,n) = (m div n, m mod n);

fun addMoney ((l1,s1,d1), (l2,s2,d2)) =
    let val (dcarry,d) = quorem(d1 + d2, 12)
        val (scarry,s) = quorem(dcarry + s1 + s2, 20)
    in  (scarry + l1 + l2, s, d)  end;
```

Tom Maynard points out that this solution uses let, which has not been introduced yet. Here is an alternative definition of addMoney:

```
fun addPounds (l1, l2, (scarry, s), d) = (scarry + l1 + l2, s, d);

fun addShillings (l1, l2, s1, s2, (dcarry,d)) =
    addPounds (l1, l2, quorem(dcarry + s1 + s2, 20), d);

fun addMoney ((l1,s1,d1), (l2,s2,d2)) =
    addShillings (l1, l2, s1, s2, quorem(d1 + d2, 12));
```

__2.8.__ A type constraint is required because - is overloaded: 

```
fun lifetime({name,born,died,quote,crowned}) : int = died - born;
```

Its type is {born:int,crowned:'a,died:int,name:'b,quote:'c} -> int.

The declaration does not constrain the other fields; their types are polymorphic.

__2.9.__ The selector #born applies to any record containing the field born. Function born_at applies to records that contain just that field and no others.

__2.10.__ The reduction steps for powoftwo(8) are

```
powoftwo(8) ==> (8=1) orelse (even(8) andalso ...)
  	    ==> even(8)  andalso  powoftwo(8 div 2) 
            ==> powoftwo(4) 
	    ==> (4=1) orelse (even(4) andalso ...)  
	    ==> even(4)  andalso  powoftwo(4 div 2) 
            ==> powoftwo(2) 
	    ==> (2=1) orelse (even(2) andalso ...)  
	    ==> even(2)  andalso  powoftwo(2 div 2) 
            ==> powoftwo(1) 
	    ==> (1=1) orelse (even(1) andalso ...)  
	    ==> true
```

__2.11.__ Yes, as shown by the reduction steps. This is because andalso and orelse are conditional operators rather than functions.

__2.12.__ The reduction steps for power(2,29), ignoring the k=1 test, are

```
power(2,29) ==> if 29 mod 2 = 0 then ... else ...
	    ==> 2 * power(2*2, 29 div 2)
	    ==> 2 * power(4,14)
	    ==> 2 * (if 14 mod 2 = 0 then ... else ...)
	    ==> 2 * (power(4*4, 14 div 2))
	    ==> 2 * (power(16,7))
	    ==> 2 * (if 7 mod 2 = 0 then ... else ...)
	    ==> 2 * (16 * power(16*16, 7 div 2))
	    ==> 2 * (16 * power(256,3))
	    ==> 2 * (16 * (if 3 mod 2 = 0 then ... else ...))
	    ==> 2 * (16 * (256 * power(256*256, 3 div 2)))
	    ==> 2 * (16 * (256 * power(65536, 1)))
	    ==> 2 * (16 * (256 * 65536))
	    ==> 536870912
```

Real numbers are written without the trailing .0 to avoid clutter.

__2.13.__ The worst case is when k has the form 2^n-1, for n>0. Then k remains odd in all the recursive calls and 2n-2 multiplications are performed.

__2.14.__ Function power could start with "if k=0 then 1.0...", but the last recursive call would always be x*power(x*x,0), reducing to x. Two needless multiplications would be performed, of which x*x could easily cause overflow. An exponentiation function should handle zero and negative exponents, calling power only for positive k.

__2.15.__ Both computations result in repeated function evaluations, but for different reasons. Lazy evaluation does not help. Memo functions, which store previous results, can compute factorial efficiently.

__2.16.__ For "steps", count the number of calls to F. It's easy to check that F(0) and F(1) involves one call, and that F(n+2)=F(n)+(F(n-1)+F(n)), so F(n+2) involves more than twice as many calls as F(n). By induction, F(2n) makes at least 2^n calls. Thus F(n) makes at least sqrt(2)^n calls. But fib(n) makes just n calls of itfib.

__2.17.__ itfib(n,F(k-1),F(k)) = F(k+n-1). See page 222 for the proof.

__2.18.__ This is a challenge rather than an exercise. I do not know of any easy solution, which is precisely the point. David Eger contributes this solution, using an explicit stack to handle the recursion.

```
int introot(int n) {
   int rf, stack[20];

   for(rf=0; stack[rf] = n; rf++, n=n/4) {}
   while(rf-->0) {
      if( (2*stack[rf+1]+1)*(2*stack[rf+1]+1) > stack[rf] )
         stack[rf] = 2*stack[rf+1];
      else
         stack[rf] = 2*stack[rf+1]+1;
   }
   return stack[0];
}
```

Michael Winking contributes this solution.

```
uint64_t increase(uint64_t k, uint64_t n) {
  return (k+1) * (k+1) > n ? k : k + 1;
}

uint64_t introot(uint64_t n) {
  int m;
  uint64_t k;
  for(m = 0, k = n; k; m += 2, k >>= 2) {}
  for(k = 0; m != 0; m -= 2, k = increase(2 * k, n >> m)) {}

  return k;
}
```

__2.19.__ This exercise is from Hoare (1987), page 380, who remarks that experts in complexity theory do not know whether this is the best GCD algorithm. It is certainly longer to code than Euclid's Algorithm. To ensure termination, both arguments must be positive.

```
fun GCD(m,n) =
    if m=n then m
    else if m mod 2 = 0 then 
	     if n mod 2 = 0 then 2 * GCD(m div 2, n div 2)
		       	    else GCD(m div 2, n) 
    else (*m odd*) 
	 if n mod 2 = 0 then GCD(m, n div 2)
         else (*both odd*)
	     if m<n then GCD((n-m) div 2, m) else GCD((m-n) div 2, n);
```

__2.20.__ Nested function declarations can be harder to read. But if they refer to identifiers declared in the local context, they can make do with fewer parameters. The nested function findroot refers to sqroot's argument. Nesting itfib within fib would only introduce confusion between the two variables called n.

__2.21.__

```
fun introotpair n =
  if n<4 then (1,n-1)
  else 
    let val (e,re) = introotpair(n div 4)
        val ri = 4*re + n mod 4    (*remainder if root=2*k*)
        val rj = ri - (4*e + 1)    (*remainder if root=2*k+1*)
    in  if rj<0 then (2*e, ri)  else (2*e+1, rj)
    end;
```

__2.22.__ This exchanges the bindings of pi and log2. It is equivalent to

```
val pi=log2 and log2=pi;
```

__2.23.__ We can express P using the mutual recursion as follows:

```
fun P n = 1 + sumup(n-1)
and sumup k = if k<1 then 0 
	             else P(k) + sumup(k-1);
```

This version is exponential, by similar reasoning as in exercise 2.16. But it is easy to verify by induction that P(n) = 2^(n-1), which gives faster ways of computing it.

__2.24.__ Please note that the Basis Library provides an entirely different structure of the same name!

```
structure Real : ARITH =
  struct
  type t = real;
  val zero = 0.0;
  fun sum   (x,y) = x+y: t;
  fun diff  (x,y) = x-y: t;
  fun prod  (x,y) = x*y: t;
  fun quo   (x,y) = x/y: t;
  end;
```

__2.25.__ (Correction by Ralf Steinbrueggen.)

```
structure Rational : ARITH =
  struct
  type t = int*int;
  val zero = (0, 1);
  fun gcd(m,n) =
    if m=0 then  n  else gcd(n mod m, m);
  fun canon (m,n) = 
      let val d = gcd(abs m, n)
      in  (m div d, n div d)  end
  fun sum   ((m,n), (m',n')) = canon(m*n' + m'*n, n*n');
  fun diff  ((m,n), (m',n')) = canon(m*n' - m'*n, n*n');
  fun prod  ((m,n), (m',n')) = canon(m*m', n*n');
  fun recip (m,n): t = if m<0 then (~n,~m) else (n,m)
  fun quo   (x,x') = prod(x, recip x');
  end;
```

__2.26.__ The constant 1 has type int, so n-1 means integer subtraction and n has type int. The result type of itfib is given as int by the type constraint; since curr is returns as the result, curr has type int. Therefore prev+curr means integer addition and prev has type int. Finally, all types agree in the recursive call and the conditional.

__2.27.__ Type checking fails because f's argument pattern is a pair, whose type must have the form T1*T2; but f is called with an argument of type int.

