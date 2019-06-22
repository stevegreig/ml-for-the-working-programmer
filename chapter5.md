## Chapter 5

__5.1.__ Note that square's type constraint must be moved. Regarding cons, there is no fn shorthand for curried functions (see next section).

```
fn x => x*x : real
fn x => fn y => x::y
fn [] => true | _::_ => false
```

__5.2.__

```
val area = fn r => pi*r*r;
	               val title = fn name => "The Duke of " ^ name;
val lengthvec = fn (x,y) => sqrt(x*x + y*y);
```

__5.3.__

(plus i) is the function that adds i to its argument.
(cmin a) is a sort of bounded identity function: it limits its result to not exceed a.
(pair x) is the function that pairs x with its argument.
(equals x) is the function that recognizes x: it returns true whenever it is applied to the value x.

__5.4.__ If (f x) is to be applied to many different values of y, then the second version is more efficient. Binding (f x) to an ML identifier evaluates h(g x) just once. Then the identifier can be called many times without evaluating h(g x) any more.

With the first version of f, calling (f x) immediately returns a function over y, without evaluating h(g x). Every time the resultant function is called, it will evaluate h(g x).

The two declarations also differ in their treatment of exceptions and non-termination. If h(g x) raises an exception or fails to terminate, then (f x) will exhibit the same behaviour under the second declaration. With the first declaration, the behaviour will not occur until (f x) is applied to some y.

__5.5.__ The occurrence of Dict.lookup has type

```
(string * (real->real)) Dict.t * string -> (real->real)
```

__5.6.__ Nesting merge inside tmergesort reduces the number of copies of lessequal that must be passed around.

```
fun tmergesort lessequal [] = []
  | tmergesort lessequal [x] = [x]
  | tmergesort lessequal xs =
      let val k = length xs div 2
	  fun merge ([],ys) = ys
	    | merge (xs,[]) = xs
	    | merge (x::xs, y::ys) =
	       if lessequal(x,y) then x::merge (xs,  y::ys)
	                         else y::merge (x::xs,  ys)
      in  merge (tmergesort lessequal (List.take(xs,k)),
                 tmergesort lessequal (List.drop(xs,k)))
      end;
```

__5.7.__ This version checks for the empty interval.

```
exception Minimum;

fun minimum f 0 = raise Minimum
  | minimum f m = 
    let fun min2 (x,y): real = if x<y then x else y
	fun minn (i,z) =
            if  i=m  then  z   else  minn (i+1, min2(z, f i))
    in  minn(1, f 0)  end;

fun minimum2 g m n = minimum (fn i=> minimum (fn j => g(i,j)) n) m;
```

__5.8.__ Sections and curried functions both permit partial application. But sections apply to paired functions rather than curried functions, and secr permits partial application to a function's second argument.

__5.9.__

secr op@ ["Richard"] takes a list of strings and appends "Richard" as the last element.
secr take ["heed", "of", "yonder", "dog!"], when applied to an integer k from 0 to 4, returns a list consisting of the first k strings of the list above.
secl 3 take, when applied to a list, returns the first 3 elements.
secl ["his", "venom", "tooth"] inter, when applied to a list of strings, returns just those present in the list above.

__5.10.__ With lazy evaluation (or with proper combinators), the second step would be omitted:

```
S K K 17 ==> K 17 (K 17) ==> K 17 (fn y=>17) ==> 17
```

__5.11.__ Define [x]E, the abstraction of E over x, by

```
    [x]x      =  I
    [x](M+N)  =  (+N) o ([x]M)       where the occurrence of x is in M
    [x](M+N)  =  (M+) o ([x]N)       where the occurrence of x is in N
```

These are the only cases, since E contains exactly one occurrence of x.

__5.12.__ Replace according to the following law (proved on page 235):

```
map f (map g xs) = map (f o g) xs
```

__5.13.__ Note that pred1 and pred2 are exchanged in the function body, since pred2 must be applied before pred1.

```
infix andf;
fun (pred1 andf pred2) x = pred2 x andalso pred1 x;
```

__5.14.__

```
fun union (xs,ys) = foldr newmem ys xs;
```

__5.15.__ The new declaration of dotprod is less efficient and arguably less readable than the original one.

```
fun dotprod pairs = foldl op+ 0.0 (ListPair.map op* pairs);

fun matprod(rowsA,rowsB) = 
  let val colsB = transp rowsB 
  in    map (fn row => map (fn col => dotprod(row,col)) colsB) rowsA
  end;
```

__5.16.__ Lazy evaluation is required to solve this exercise fully, since foldl and foldr (in ML) always traverse the entire list, while exists stops as soon as a true element is found.

```
fun exists pred = foldr (fn (x,e)=> pred x orelse e) false;
```

__5.17.__ This version performs no needless copying.

```
fun posDiffs (xs,ys) : int list = 
    foldr (fn (x,l) =>
	       foldr (fn (y,l) => if y<x then x-y :: l else l)
	            l ys)
	  [] xs;
```

__5.18.__

```
fun prefold f e Lf = e
  | prefold f e (Br(u,t1,t2)) = f(u, prefold f (prefold f e t2) t1);
```

__5.19.__ Use nextfib from page 50. Function fibpair could have been defined (iteratively!) by

```
fun fibpair (n) = repeat nextfib (n-1) (0,1);
```

__5.20.__ This performs function exponentiation; funny f n = repeat f n. Compare with power on page 49. But this saves only on composition operations; funny f n x and repeat f n still perform n calls to f.

__5.21.__ Applying this function to the binary tree t returns a function, similar to preord, that can generate a preorder list of the tree's labels. (See section 4.11 for a description of preord.)

__5.22.__

```
fun nfuns (Var _) = 0
  | nfuns (Fun(_,args)) = sum (map nfuns args) + 1;

fun accum_nfuns (Var _, k)       = k
  | accum_nfuns (Fun(_,args), k) = foldr accum_nfuns (k+1) args;

fun nfuns (Var _)       = 0
  | nfuns (Fun(_,args)) = nfuns_list args + 1
and nfuns_list []       = 0
  | nfuns_list (t::ts)  = nfuns t + nfuns_list ts;
```

__5.23.__ The foldr version makes this trivial -- replace :: by newmem.

```
fun accumvars2 (Var a, bs)       = newmem(a,bs)
  | accumvars2 (Fun(_,args), bs) = foldr accumvars2 bs args;
```

__5.24.__ It goes into a loop immediately; cons is never entered.

```
    badfrom(30) ==> cons(30, badfrom(31))
                ==> cons(30, cons(31, badfrom(32)))
```

__5.25.__

```
datatype 'a seq = Nil
                | Cons of unit -> 'a * 'a seq;

fun from k = Cons(fn()=> (k, from(k+1)));

fun take (xq, 0) = []
  | take (Nil, n) = raise Subscript
  | take (Cons f, n) = 
      let val (x,xq) = f()
      in  x :: take (xq, n-1)  end;
```

__5.26.__ This code is much more complex, particularly because it needs the function force.

```
fun force (Seq xf) = xf();

fun from k = Seq(fn()=> Cons(k, from(k+1)));

fun take (xq, 0) = []
  | take (xq, n) = case force xq of
        Nil            => raise Subscript
      | Cons(x,xtailq) => x :: take (xtailq, n-1);
```

__5.27.__

```
fun null (Cons _) = false
  | null Nil      = true;

fun drop (xq, 0)         = xq
  | drop (Nil, n)        = raise Subscript
  | drop (Cons(x,xf), n) = drop (xf(), n-1);

fun toList Nil = []
  | toList (Cons(x,xf)) = x :: toList (xf());
```

__5.28.__ Observe how instances of "fn()=>..." accumulate!

```
add(from 5, squares (from 9))
  ==> add(Cons(5, fn()=> from(5+1)), squares (from 9))
  ==> add(Cons(5, fn()=> from(5+1)), squares (Cons(9, fn()=> from(9+1))))
  ==> add(Cons(5, fn()=> from(5+1)), 
           Cons(81, fn()=> squares((fn()=> from(9+1))())))
  ==> Cons(86, fn()=> add((fn()=> from(5+1))()),
                          (fn()=> squares((fn()=> from(9+1))()))())
  ==> ...
```

__5.29.__

```
fun repelt k Nil          = Nil
  | repelt k (Cons(x,xf)) =
      let fun rp 0 = repelt k (xf())
	    | rp k = Cons(x, fn() => rp (k-1))
      in  rp k  end;
```

__5.30.__

```
fun addaj Nil : int seq = Nil
  | addaj (Cons(m,mf))  =
      case mf() of Nil => Cons(m,mf)
                 | Cons(n,nf) => Cons(m+n, fn() => addaj (nf()));
```

__5.31.__ Sequence versions of exists and all would, in some cases, have to search infinitely many elements.

```
fun takewhile pred Nil          = Nil
  | takewhile pred (Cons(x,xf)) =
        if pred x then Cons(x, fn()=> takewhile pred (xf()))
                  else Nil;

fun dropwhile pred Nil          = Nil
  | dropwhile pred (Cons(x,xf)) =
        if pred x then dropwhile pred (xf())
                  else (Cons(x,xf));
```

__5.32.__ Calling within is rather silly, when successive terms are created by summing a series, but it does work.

```
(*running sums of a sequence*)
fun sums z Nil = Nil : real seq
  | sums z (Cons(x,xf)) = Cons(z, fn()=> sums (z+x) (xf()));

(*for generating a term of exp's Taylor series Seq.from its predecessor*)
fun expterm x (n,t) = (n+1, t*x/(real n));

fun sexp x = within 1E~6 (sums 0.0
                          (Seq.map #2 (Seq.iterates (expterm x) (1,1.0))));
```

__5.33.__ The fancy test given on page 201 combines the virtues of absolute and relative difference.

```
fun within2 (eps:real) (Cons(x,xf)) =
      let val Cons(y,yf) = xf() 
      in  if abs(x-y)/((abs x + abs y)/2.0 + 1.0) < eps then y
	  else within2 eps (Cons(y,yf))
      end;

fun qroot2 a = within2 1E~12 (iterates (nextApprox a) 1.0);
```

__5.34.__ It loops because the input is an infinite sequence of Nils.

__5.35.__ Viewing the sequences generated by next_listq might be instructive.

```
fun next_listq lq = Seq.map op:: (enumerate (makeqq (Seq.from 1, lq)));
val all_lists = enumerate (Seq.iterates next_listq (Seq.cons([],Nil)));
```

__5.36.__ Write k in binary notation as 1BB...B100...0, where the Bs are zeros or ones. This makes it obvious that k = 2**i' * j', where i' is the number of trailing zeros and j' is the number 1BB...B1. Let i=i'+1 and j=(j'+1)/2. Clearly i and j are positive integers and are uniquely determined by k, and pack(i,j) = pack(i'+1, (j'+1)/2) = 2**i' * j' = k.

__5.37.__

```
datatype 'a binseq = 
                Leaf
              | Brch of 'a * (unit -> 'a binseq) * (unit -> 'a binseq);

fun itr k = Brch(k, fn()=> itr(2*k), fn()=> itr(2*k+1));
```

__5.38.__ Preorder, inorder and postorder are equally unsuitable for infinite trees because it is impossible to traverse the entire left subtree before the right subtree. Replacing append (@) by interleave corrects this problem. Here is a form of preorder. Compare Seq.take(preorder (itr 1), 15) with the binary tree on page 155:

```
fun preorder Leaf = Nil
  | preorder (Brch(v,tf1,tf2)) =
      Cons(v, fn()=> Seq.interleave (preorder(tf1()), preorder(tf2())));
```

And here is the inverse function.

```
(*Return/discard alternating elements of a sequence*)
fun altq Nil = Nil
  | altq (Cons(x,xf)) = Cons(x, fn()=> altq_tl(xf()))
and altq_tl Nil = Nil
  | altq_tl (Cons(x,xf)) = altq(xf());

(*inverse of the function "preorder"*)
fun getPreorder Nil = Leaf
  | getPreorder(Cons(v,vf)) =
        Brch(v, fn()=> getPreorder(altq(vf())),
                fn()=> getPreorder(altq_tl(vf())));
```

__5.39.__ These versions were presented in the book's first edition.

```
fun depthFirst' (next,pred) x =
    let fun dfs [] = Nil
	  | dfs(y::ys) = 
	      if pred y then Cons(y, fn()=> dfs(next y @ ys))
	               else dfs(next y @ ys)
    in  dfs [x]  end;

fun breadthFirst' (next,pred) x =
    let fun bfs [] = Nil
	  | bfs(y::ys) = 
	      if pred y then Cons(y, fn()=> bfs(ys @ next y))
	               else bfs(ys @ next y)
    in  bfs [x]  end;
```

__5.40.__ This is a simple form of best-first search, using a polymorphic distf function for distances. It adds the (known!) distance from the root to the estimated distance to a solution. The estimate must not be greater than the actual distance, or else the search could be incomplete.

```
fun bestFirst (distf: 'a->int) next x =
  let fun ins (xtrip, []) = [xtrip]
	| ins (xtrip as (kx,dx,_), (ytrip as (ky,dy,_)) :: ps) = 
	    if kx+dx < (ky+dy: int) then xtrip::ytrip::ps
	    else ytrip :: ins (xtrip, ps)
      fun insx k (x,ps) = ins((k+1, distf x, x), ps)
      fun bfs [] = Nil
        | bfs ((ky,_,y)::ps) = 
	    Cons(y, fn()=> bfs (foldr (insx ky) ps (next y)))
  in  bfs [(0, distf x, x)]  end;
```

Here we apply it to the palindrome example.

```
fun dist2Palin xs = if isPalin xs then 0 else 1 + dist2Palin (tl xs);
Seq.filter isPalin (bestFirst dist2Palin nextChar []);
map implode (Seq.take(it,50));
```

__5.41.__ This version terminates the sequence, but is 50% slower than the one presented in the book. Probably the call to Seq.@ is to blame. I'd be grateful to hear of an efficient version that can recognize when there are no more solutions.

```
fun depthIter' next x =
 let fun dfs k (y, sf) = 
          if k=0 then fn()=> Cons(y,sf)
          else foldr (dfs (k-1)) sf (next y)
     fun deepen k = case dfs k (x, fn()=>Nil) () of
                        Nil => Nil
	             | q   => Seq.@ (q, deepen(k+1))
 in  deepen 0  end;
```

__5.42.__ The resulting sequence begins in depth-first fashion, but fully enumerates to depth d before going on to further depths.

```
fun depthIterative (d,next) x =
 let fun dfs i (y, sf) () = 
          if i<0 then sf()
          else if i<d then Cons(y, foldr (dfs (i-1)) sf (next y))
          else foldr (dfs (i-1)) sf (next y) ()
     fun deepen k = dfs k (x, fn()=> deepen (k+d)) ()
 in  deepen 0  end;
```

Here we apply it to the palindrome example, depth 5. Observe the output carefully.

```
Seq.filter isPalin (depthIterative (5, nextChar) []);
map implode (Seq.take(it,20));
```

__5.43.__ Here is the datatype:

```
datatype 'a finseq = Branch of 'a * (unit -> 'a finseq) list;

fun finseq_of next x =
    Branch(x, map (fn y => fn () => finseq_of next y) (next x));
```

A next function cannot represent any tree where two distinct subtrees are headed by the same label. An example is

```
Branch(1, [fn()=>Branch(1, [])])
```
