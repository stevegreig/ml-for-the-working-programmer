## Chapter 3

__3.1.__ Note that the final tl l represents an optimization of the computation suggested by the pattern-matching.

```
fun maxl l : int =
    if null(tl l) then hd l
    else if hd l > hd(tl l) then maxl(hd l :: tl(tl l))
                            else maxl(tl l);
```
                            
__3.2.__ It has to be recursive (or rather, iterative).

```
fun last [x]    = x
  | last(_::xs) = last xs;
```

__3.3.__ If i>length(l), then take and drop behave just as they would for i=length(l), rather than raising an exception. If i<0 then the result is the same as for i=0.

```
fun nth(l,n) = hd(drop(l,n));
```

__3.5.__ Simply insert an equation for this case:

```
infix @;
fun   xs    @ [] = xs
  |   []    @ ys = ys
  | (x::xs) @ ys = x :: (xs@ys);
```

__3.6.__ This sort of error is common in Lisp. If we define

```
fun nrev  []    = []
  | nrev(x::xs) = (nrev xs) @ x;
```

then nrev will have type `'a list list -> 'a list`. For example, `nrev[[1],[2],[3],[4]] = [4,3,2,1]`.

__3.7.__

```
nrev[1,2,3,4] ==> nrev[2,3,4] @ [1]
              ==> (nrev[3,4] @ [2]) @ [1]
              ==> ((nrev[4] @ [3]) @ [2]) @ [1]
              ==> (((nrev[] @ [4]) @ [3]) @ [2]) @ [1]
              ==> ((([] @ [4]) @ [3]) @ [2]) @ [1]
              ==> (([4] @ [3]) @ [2]) @ [1]
              ==> ((4 :: ([] @ [3])) @ [2]) @ [1]
              ==> ((4 :: [3]) @ [2]) @ [1]
              ==> ([4,3] @ [2]) @ [1]
              ==> (4 :: ([3] @ [2])) @ [1]
              ==> (4 :: 3 :: ([] @ [2])) @ [1]
              ==> (4 :: 3 :: [2]) @ [1]
              ==> (4 :: [3,2]) @ [1]
              ==> [4,3,2] @ [1]
              ==> ...
```

__3.8.__ This function has the same type and delivers the same result as concat. But it builds its result using one deep recursion (which might cause stack overflow).

__3.9.__ Testing explicitly for the empty list eliminates the dependence on the order of pattern-matching.

```
fun zip ([], _)      = []
  | zip (_, [])      = []
  | zip(x::xs,y::ys) = (x,y) :: zip(xs,ys);
```

__3.10.__ `rev(rtake(i,l,[]))` performs twice as many :: operations as `take(i,l)`, due to the cost of rev. But it requires constant stack space, while take(i,l) requires stack proportional to the length of the result. If sufficient stack space is available, take(i,l) is faster.

__3.11.__ It is the same idea as making change.

```
fun roman (numpairs, 0)         = ""
  | roman ((s,v)::numpairs, amount) =
      if amount<v then roman(numpairs, amount)
      else s ^ roman((s,v)::numpairs, amount-v);
```

These lists determine whether 4 is shown as IIII or IV.

```
val rompairs1 =
    [("M",1000), ("D",500), ("C",100), ("L",50), ("X",10), ("V",5), ("I",1)]
and rompairs2 =
    [("M",1000), ("CM",900), ("D",500), ("CD",400), 
     ("C",100),  ("XC",90),  ("L",50),  ("XL",40), 
     ("X",10),   ("IX",9),   ("V",5),   ("IV",4), 
     ("I",1)];
```

__3.12.__ Larger coins that come too late in the list are ignored. Non-positive coin values cause looping, as they increase the amount for which we are trying to make change.

__3.13.__ coinvals becomes a list of pairs. The second component says how many coins of that value are available.

```
fun allChangef (coins, coinvals, 0)         = [coins]
  | allChangef (coins, [],    amount)       = []
  | allChangef (coins, (c,0)::coinvals, amount) = 
      allChangef(coins, coinvals, amount)
  | allChangef (coins, (c,n)::coinvals, amount) =
      if amount<0 then []
      else allChangef(c::coins, (c,n-1)::coinvals, amount-c) @
           allChangef(coins, coinvals, amount);
```

__3.14.__ In my tests the new version was nearly three times faster than the old.

```
fun allChange2 (coins, coinvals, 0, coinslist)       = coins::coinslist
  | allChange2 (coins, [],  amount, coinslist)       = coinslist
  | allChange2 (coins, c::coinvals, amount, coinslist) =
      if amount<0 then coinslist
      else allChange2(c::coins, c::coinvals, amount-c, 
                       allChange2(coins, coinvals, amount, coinslist));
```

__3.15.__

```
fun bcarry (false, ps) = ps
  | bcarry (true, []) = [true]
  | bcarry (true, p::ps) = not p :: bcarry(p, ps);

(*Carry if at least two bits are true*)
fun carry3(a,b,c) = (a andalso b) orelse (a andalso c) orelse (b andalso c);

(*Binary sum: since b=c computes not(b XOR c), the result is a XOR b XOR c*)
fun sum3(a,b,c) = (a=(b=c));

fun bsum (c, [], qs) = bcarry (c,qs)
  | bsum (c, ps, []) = bcarry (c,ps)
  | bsum (c, p::ps, q::qs) =
      sum3(c,p,q)  ::  bsum(carry3(c,p,q), ps, qs);

fun bprod ([], _) = []
  | bprod (false::ps, qs) = false::bprod(ps,qs)
  | bprod (true::ps, qs) = bsum(false, qs, false::bprod(ps,qs));
```

__3.16__ and __3.17.__ The division function appears in the structure below.

```
structure Bin =
  struct

  type t = int list

  val zero = []

  fun carry (0, ps) = ps
    | carry (1, []) = [1]
    | carry (1, p::ps) = (1-p) :: carry(p, ps);

  fun sumc (c, [], qs) = carry (c,qs)
    | sumc (c, ps, []) = carry (c,ps)
    | sumc (c, p::ps, q::qs) =
        ((c+p+q) mod 2)  ::  sumc((c+p+q) div 2, ps, qs);

  fun sum (ps,qs) = sumc (0,ps,qs);

  fun prod ([], _) = []
    | prod (0::ps, qs) = 0::prod(ps,qs)
    | prod (1::ps, qs) = sum(qs, 0::prod(ps,qs));

  (** Subtraction **)

  (*Build a list of bits, propagating ~1 and suppressing leading zeros*)
  infix $$;
  fun 0 $$ [] = []
    | n $$ [~1] = [~1]
    | n $$ ns = n::ns;

  fun borrow (0, ps) = ps
    | borrow (~1, []) = [~1]
    | borrow (~1, p::ps) = (1-p) $$ borrow(p-1, ps);

  (*EXERCISE.  Difference between two binary numbers, with borrowing*)
  fun diffb (b, ps, []) = borrow (b,ps)
    | diffb (b, [], q::qs) = 
        ((b-q) mod 2)  $$  diffb((b-q) div 2, [], qs)
    | diffb (b, p::ps, q::qs) =
        ((b+p-q) mod 2)  $$  diffb((b+p-q) div 2, ps, qs);

  fun diff (ps,qs) = diffb (0,ps,qs);

  (** EXERCISE.  Division **)

  fun divide (ps,ds,n,qs) =
    if n=0 then (qs,ps)
    else
      let val rs = diff (ps,ds)
      in  if rs = [~1] then divide(0::ps, ds, n-1, 0::qs)
                       else divide(0::rs, ds, n-1, 1::qs)
      end;

  (*Scan down list counting bits in k; get position of last "1" (in n)*)
  fun lastone (n,k,[]) = n
    | lastone (n,k,0::ps) = lastone(n,k+1,ps)
    | lastone (n,k,1::ps) = lastone(k,k+1,ps);

  fun addzeros (0,ds) = ds
    | addzeros (k,ds) = 0::addzeros(k-1,ds);

  fun quorem (ps,ds) =
    let val n = lastone(0,1,ps) - lastone(0,1,ds)
    in  if n<0 then ([0],ps)
        else let val (qs,rs) = divide(ps, addzeros(n,ds), n+1, [])
             in  if length rs < n+1 then (qs,rs)
                 else (qs, List.drop(rs,n+1))
             end
    end;

  fun quo (ps,qs) = #1(quorem(ps,qs))
  and rem (ps,qs) = #2(quorem(ps,qs));

  fun gcd(ms,ns) =
      if lastone(0,1,ms)=0 then  ns  else  gcd(rem(ns,ms), ms);

  end;
```

__3.18.__ As might be expected, the list of digits is kept in reverse order.

```
fun binary_of_int 0 = []
  | binary_of_int n = (n mod 2) :: binary_of_int (n div 2);

val ten = binary_of_int 10;

fun binary_of_decimal [] = []
  | binary_of_decimal(d::ds) = 
        binsum(0,  binary_of_int d,  binprod(ten, binary_of_decimal ds));

fun double (0,[]) = []
  | double (c,[]) = [c]
  | double (c,d::ds) = 
      let val next = c + 2*d
      in (next mod 10) :: double(next div 10, ds)  end;

fun decimal_of_binary [] = []
  | decimal_of_binary (p::ps) = double(p, decimal_of_binary ps);


fun binfact n =
    if n=0 then [1]  else  binprod(binary_of_int n, binfact(n-1));

rev (decimal_of_binary (binfact 100));

[9,3,3,2,6,2,1,5,4,4,3,9,4,4,1,5,2,6,8,1,6,9,9,2,3,8,8,5,6,2,6,6,7,0,0,
 4,9,0,7,1,5,9,6,8,2,6,4,3,8,1,6,2,1,4,6,8,5,9,2,9,6,3,8,9,5,2,1,7,5,9,
 9,9,9,3,2,2,9,9,1,5,6,0,8,9,4,1,4,6,3,9,7,6,1,5,6,5,1,8,2,8,6,2,5,3,6,
 9,7,9,2,0,8,2,7,2,2,3,7,5,8,2,5,1,1,8,5,2,1,0,9,1,6,8,6,4,0,0,0,0,0,0,
 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
```

Thus, the factorial of 100 is 9332621544394415268169923885626670049071596826438162146859296389521759 9993229915608941463976156518286253697920827223758251185210916864000000 000000000000000000

__3.19.__ They do not handle the pattern []::rows, since they expect each row to be nonempty; transp handles this pattern. All rows are assumed to be as long as the first. If other rows are longer then the surplus elements are ignored; if shorter then exception Match is raised, indicating failure of pattern-matching.

__3.20.__ transp loops given the empty list, as it works by shortening each of its rows. The empty matrix has no rows to shorten, so it calls itself again with the empty list!

__3.21.__ Note the similarity between zip_lists and zip.

```
fun zip_lists([], [])      = []
  | zip_lists(x::xs, [])   = [x] :: zip_lists(xs,[])
  | zip_lists(x::xs,y::ys) = (x::y) :: zip_lists(xs,ys);

fun transp2 [] = []
  | transp2(row::rows) = zip_lists(row, transp2 rows);
```

__3.22.__

```
fun rowneg []      = [] : real list
  | rowneg (x::xs) = ~x :: rowneg xs;

fun matneg [] = []
  | matneg (row::rows) = rowneg row :: matneg rows;
```

__3.23.__

```
fun rowsum ([],[]) = [] : real list
  | rowsum (x::xs,y::ys) = x+y :: rowsum (xs,ys);

fun matsum ([],[]) = []
  | matsum (Arow::rowsA, Brow::rowsB) =
      rowsum (Arow,Brow) :: matsum (rowsA,rowsB);
```

__3.24.__ This is a general property of Gaussian elimination. The only division in gausselim is by p, which is the head of the row returned by pivotrow. This can only be zero if the matrix contains a column of all zeroes, which cannot occur if the equations are linearly independent. Scaling the remaining columns by the pivot row preserves the property of linear independence. When solutions is applied to the result of gausselim, its only division is by the heads of pivot rows.

A formal proof of this property, using the methods of Chapter 6, would be a substantial exercise in verification.

All this assumes that the machine detects underflow. In fact, it is more likely to replace very small values by zero.

__3.25.__ The >= test in pivotrow ensures that it takes the first row having the greatest absolute value, in case there are several such rows. Function delrow clearly finds (and deletes) the first row having a given head value. It would not do for pivotrow to return one row and for delrow to delete a different one!

__3.26.__ The determinant of a triangular matrix equals the product of the entries on the main diagonal. However, each non-trivial pivot step in the Gaussian elimination re-orders the rows, which changes the determinant's sign. So we must modify gausselim to keep track of the sign changes, and we must include the sign in the product of the diagonal entries.

```
fun signed_gausselim [row] = ([row], 1.0)
  | signed_gausselim rows =
      let val p::prow = pivotrow rows
          val samerow = Real.== (abs (hd (hd rows)), abs p)
          fun elimcol [] = []
            | elimcol ((x::xs)::rows) =
                  vectorsum(xs, scalarprod(~x/p, prow))
                  :: elimcol rows
          val (g_rows, odd) = signed_gausselim(elimcol(delrow(p,rows)))
      in  ((p::prow) :: g_rows,
           if samerow then odd else ~odd)
      end;

fun diagprod ([], e: real)     = e
  | diagprod((x::xs)::rows, e) = diagprod (rows, x*e);

fun det rows = diagprod(signed_gausselim rows);
```

__3.27.__ Function inverse joins an n by n identity matrix to the right of its argument and performs one Gaussian elimination. To extract the answer, it performs n back substitutions, selecting columns n+1, ..., 2n in succession. Faster code could undoubtedly be written.

```
fun zeroes 0 = []
  | zeroes n = 0.0 :: zeroes(n-1);

fun rsolutions (endrow, []) = endrow
  | rsolutions (endrow, (x::xs)::rows) =
      let val solns = rsolutions(endrow,rows)
      in ~(dotprod(solns,xs)/x) :: solns  end;

fun inverse rows =
    let val n = length rows
        fun idrow(x,k) = zeroes(k-1) @ [x] @ zeroes(n-k)
        fun newrows ([], k) = []
          | newrows (row::rows, k) =
                (row @ idrow(1.0,k)) :: newrows(rows, k+1)
        val ge = gausselim (newrows(rows,1))
        fun newcols k =
              if k>n then []
              else take(n, rsolutions (idrow(~1.0,k), ge)) :: newcols(k+1)
    in  transp (newcols 1)  end;
```

__3.28.__ It is best to avoid using names like matsum and matprod, instead declaring sum and prod within the structure brackets. The code for the omitted sections appears either above or in the text.

```
structure Matrix : ARITH =
  struct
  type t = real list list;
  val zero = [];
  fun sum    ...
  fun neg    ...
  fun diff (rowsA,rowsB) = sum (rowsA, neg rowsB);
  fun prod   ...
  fun inverse ...
  fun quo  (rowsA,rowsB) = prod (rowsA, inverse rowsB);
  end;
```

__3.29.__

```
nextperm [2,3,1,4] ==> next ([2], [3,1,4])
                   ==> next (3::[2], [1,4])
                   ==> swap [3,2]            (where y=1 and ys=[4])
                   ==> 3 :: swap [2]         (where y=1 and ys=[4])
                   ==> 3 :: 1 :: 2 :: [4]
                   ==> [3,1,2,4]             
```

__3.30.__ The modified version is incorrect if there are repeated elements. It takes [2,2,3,1] to itself rather than to [3,2,1,2]. Refer to Steps 1 and 2 on page 95. The elements to the left of y now form a strictly increasing sequence, and y may equal the rightmost of them. Exchanging y with something equal to it has no effect.

__3.31.__ It raises exception Match. To correct this, add a test for [] to next:

```
fun next(xlist, [])    : int list = xlist
  | next(xlist, y::ys) : int list = ...
```

__3.32.__ Calling 1 mem upto(1,500) performs only one equality test, since orelse behaves like a conditional and does not make the recursive call 1 mem [2,...,500].

And setof(upto(1,500)) performs 0+1+...+499=124750 equality tests, since all the elements are distinct.

__3.33.__ Calling union([x1,...,xn],ys) computes newmem(x1,...newmem(xn,ys)...) while itunion([x1,...,xn],ys) computes newmem(xn,...newmem(x1,ys)...). Assuming that x1,...,xn are arbitrary, we can expect both orders of insertion to be equally efficient. Therefore itunion is slightly more efficient because it is iterative, although the difference is small in practice.

__3.34.__ The simplest solution is to call powset and then take only the subsets containing k elements. However, powset(upto(1,30)) has 1073741824 subsets! The following version generates only subsets containing k elements.

```
fun choosing (0, _, base) = [base]
  | choosing (k, [], base) = []
  | choosing (k, x::xs, base) = 
      if k > length (x::xs) then []
      else  choosing(k, xs, base) @ choosing(k-1, xs, x::base);

fun choose(k, xs) = choosing(k, rev xs, []);
```

__3.35.__ The depth of recursive calls is much greater for cprod. If length(xs)=m and length(ys)=n then cartprod generates m+n nested calls while cprod generates m*n nested calls.

__3.36.__ The contorted declaration of sortnew below could be replaced by a case expression; see Chapter 4.

```
fun pathsort2 graph =
  let fun sort ([], path, visited) = [visited]
        | sort (x::xs, path, visited) =
            if x mem path then []
            else if x mem visited then sort(xs,path,visited)
            else
              let fun sortnew [] = []  (*propagate cycle detection*)
                    | sortnew [vis] = sort(xs,path,x::vis)
              in  sortnew (sort(nexts(x,graph), x::path, visited))
              end
      val (xs,_) = ListPair.unzip graph
  in sort(xs, [], []) end;
```

__3.37.__ Every node with an outgoing arc is visited, and every visited node is finally included in the list visited. It may seem that visited can block the detection of some cycles, but this list only contains nodes that have been thoroughly searched below. Therefore cys will indeed contain a member of each cycle.

__3.38.__ This version is significantly quicker.

```
fun quicka ([], sorted) = sorted
  | quicka ([x], sorted) = x::sorted
  | quicka (a::bs, sorted) =  (*"a" is the pivot*)
      let fun partition (left,right,[]) : real list =
                quicka (left, a :: quicka(right,sorted))
            | partition (left,right, x::xs) =
                if x<=a then partition (x::left, right, xs)
                        else partition (left, x::right, xs)
      in  partition([],[],bs)  end;
```

__3.39.__ Note that find(xs,0) returns the smallest element of xs.

```
fun find (a::bs, i) =  (*the head "a" is the pivot*)
  let fun partition (left,right,[]) : real = 
            let val l = length left 
            in  if i < l then find(left, i)
                else if i=l then a
                else find (right, i-l-1)
            end
        | partition (left,right, x::xs) =
            if x<=a then partition (x::left, right, xs)
                    else partition (left, x::right, xs)
  in  partition([],[],bs)  end;
```

__3.40.__ As above, the first element of the list is number 0.

```
fun findrange ([],    i, j) = []
  | findrange (a::bs, i, j) =  (*the head "a" is the pivot*)
      let fun partition (left,right,[]) : real list = 
                let val l = length left 
                in  findrange (left, i, Int.min(j,l-1)) @
                              (if i<=l andalso l<=j then [a] else []) @
                    findrange (right, Int.max(0,i-l-1), j-l-1)
                end
            | partition (left,right, x::xs) =
                        if x<=a then partition (x::left, right, xs)
                        else partition (left, x::right, xs)
  in  if i>j then [] else partition([],[],bs)  end;
```

__3.41.__ My tests were inconclusive. It was no faster under Poly/ML, but slightly faster under SML/NJ (270 msec).

__3.42.__ Under SML/NJ this version took 240 msec, still slower than tmergesort'.

__3.43.__ If the list xs is empty then sorting raises an exception. Function mergepairs expects, and returns, a non-empty list of lists.

__3.44.__ One approach is to define two separate runs-counting functions and to modify Samsort to call the correct one by looking at the next two elements to be sorted. This version runs about 9% faster on the standard 10000 random numbers. It finds only 4102 runs, while nextrun finds 5014 runs.

```
fun next_irun(run, []) =       (rev run, []: real list)
  | next_irun(run, x::xs) =
      if  x < hd run then  (rev run, x::xs)
      else  next_irun(x::run, xs);

fun next_drun(run, []) =       (run, []: real list)
  | next_drun(run, x::xs) =
        if  x > hd run then  (run, x::xs)
                          else  next_drun(x::run, xs);

fun samsorting2([],  ls, k) = hd(mergepairs(ls,0))
  | samsorting2([x], ls, k) = hd(mergepairs([x]::ls,0))
  | samsorting2(x::y::xs, ls, k) = 
       let val (run, tail) = if x<=y then next_irun([y,x], xs)
	                            else next_drun([y,x], xs)
       in  samsorting2(tail, mergepairs(run::ls, k+1), k+1)
       end;  
```

__3.45.__

```
fun diff ([], us)               = termprod((0,~1.0), us)
  | diff (ts, [])               = ts
  | diff ((m,a)::ts, (n,b)::us) =
                   if m>n then (m,a)  :: diff (ts,  (n,b)::us)
              else if n>m then (n,~b) :: diff ((m,a)::ts,  us)
              else (*m=n*) 
                   if Real.== (a-b,0.0) then diff (ts, us)
                                        else (m, a-b) :: diff (ts, us);
```

__3.46.__

```
fun coeffShow a = if Real.==(a,1.0) then "" else Real.toString a;        
fun termShow (0,a) = Real.toString a
  | termShow (1,a) = coeffShow a ^ "x"
  | termShow (m,a) = coeffShow a ^ "x^" ^ Int.toString m;

fun showing [] = ""
  | showing((m,a)::ts) =
        if a<0.0 then " - " ^ termShow(m,~a) ^ showing ts
                         else " + " ^ termShow(m, a) ^ showing ts;
                        
fun show [] = "0"
  | show((m,a)::ts) =
                if a<0.0 then " - " ^ termShow(m,~a) ^ showing ts
                         else         termShow(m, a) ^ showing ts;  
```

Recall that polynomials are represented by lists of (exponent, coefficient) pairs with the exponents in strictly decreasing order and the coefficients non-zero. We may assume that the arguments to our functions already respect this representation.
We can see that sum tests for zero coefficients and omits them, and compares exponents to ensure that they appear in decreasing order. To be more formal we could prove this by induction, as in the proof of merge sort found in Chapter 6.

For prod we note that take and drop yield valid polynomials, may assume inductively that the recursive calls yield valid polynomials, and finally appeal to the correctness (just proved) of sum.

__3.48.__ One could say that sum itself amounts to a definition of polynomial addition, but this reduces our problem to a triviality. Moreover it refers to a particular representation of polynomials: it is too concrete.

We could adopt a more abstract definition of polynomials, such as sets of (exponent, coefficient) pairs with non-zero coefficients. We could define addition of such sets quite easily. Then the correctness of sum is analogous to the correctness of union discussed in Section 3.22.
