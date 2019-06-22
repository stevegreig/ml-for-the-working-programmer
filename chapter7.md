## Chapter 7

__7.1.__ It is quadratic in n. Calling enq(q,x)costs length(q)+1 cons operations. We get the recurrence equations T(0)=0 and T(n+1) = n+1+T(n). The solution is T(n) = n(n+1)/2.

__7.2.__ The first representation gives quick access to the front of the queue, while the second one gives quick access to the rear. Neither point is much of an advantage, since in normal use the front and rear are used equally often. With Representation 1, deq takes constant time, but with Representation 3, it occasionally takes time linear in the length of the queue. Representation 1 can only be more efficient than Representation 3 if usage is non-single-threaded: that is, if the result of deq is discarded instead of taken as the new queue.

__7.3.__

```
structure Queue2a = 
  struct
  type 'a t = 'a list;
  exception E;

  val empty = [];

  fun enq(q,x) = x::q;

  fun null(x::q) = false
    | null [] = true;

  fun hd [x] = x
    | hd (_::q) = hd q
    | hd [] = raise E;

  fun deq [x] = []
    | deq (x::q) = x :: deq q
    | deq [] = raise E;
  end;
```

__7.4.__ Note that the head is always stored at subscript 0 because lorem shifts down the array elements. With this version, each operation takes logarithmic time in the length of the queue, while occasionally Representation 3 can require linear time for a single deq operation. However, over the lifetime of a queue, Representation 3 will be more efficient, since virtually all operations will take constant time.

```
structure Queue4 = 
  struct
  type 'a t = 'a Flex.array;

  exception E;

  val empty = Flex.empty;

  fun enq(q, x) = Flex.hiext(q,x);

  fun null(q) = (Flex.length q = 0);

  fun hd q = Flex.sub(q,0) 
             handle Subscript => raise E;

  fun deq q = Flex.lorem(q) 
              handle Size => raise E;
  end;
```

__7.5.__ If an upper bound on the length of the queue is fixed in advance then ordinary functional arrays can be used to replace imperative arrays. However, having to fix the bound is unattractive when the other representations allow unbounded queues. If instead we allow the first and last subscripts to grow indefinitely, then functional arrays will become increasingly inefficient. The flexible array approach (above) would be better.

__7.6.__ Starting with the empty queue, insert 1 and then 2. The result is represented by the pair ([1], [2]). Starting with the empty queue, insert 3, then 1, then 2; finally, remove the head using deq. The result is represented by the pair ([1,2], []).

__7.7.__ Signature QUEUE gains two additional lines. Note the equality type variables in the type of equals.

```
val length: 'a t -> int          (*length of queue*)
val equal: ''a t * ''a t -> bool (*equality between queues*)
Two lines are added to Queue1. The use of List.length prevents confusion with the new version of length.
val length = List.length;
fun equal(q1, q2) = (q1=q2);
For Queue2, the new length function is recursive.
fun length (enq(q,_)) = length q + 1
  | length empty = 0;
	               
	               
fun equal(q1,q2) = (q1=q2);
For Queue3, the given equality function is inefficient because it simply converts the queues into lists in order to compare them. See if you can do better.
fun length (Queue(heads,tails)) = List.length heads + List.length tails;

fun equal(Queue(heads1,tails1),Queue(heads2,tails2)) = 
    heads1 @ rev tails1 = heads2 @ rev tails2;
```

__7.8.__ The two representations are lists and a new datatype. Exception handling is omitted.

```
abstype 'a stack1 = S1 of 'a list
  with
  val empty = S1 [];

  fun push(x, S1 st) = S1 (x::st);

  fun snull(S1(x::st)) = false
    | snull _ = true;

  fun top(S1(x::st)) = x;

  fun pop(S1(x::st)) = S1 st;
  end;

abstype 'a stack2 = Empty 
	         | Push of 'a * 'a stack2
  with
  val empty = Empty
  and push   = Push

  fun snull (Push _) = false
    | snull Empty = true;

  fun top (Push(x,st)) = x;

  fun pop (Push(x,st)) = st;
  end;
```

__7.9.__ First, here is the abstype declaration.

```
abstype rat = Rat of int*int
  with
    local
      fun gcd(m,n) =
	       if m=0 then  n  else gcd(n mod m, m);
      fun canon (m,n) = 
	       let val d = gcd(abs m, n)
	       in  Rat (m div d, n div d)  end
      fun recip (Rat(m,n)) = if m<0 then Rat(~n,~m) else Rat(n,m)
    in
      val rat_zero = Rat(0, 1);
      fun rat_sum   (Rat(m,n), Rat(m',n')) = canon(m*n' + m'*n, n*n');
      fun rat_diff  (Rat(m,n), Rat(m',n')) = canon(m*n' - m'*n, n*n');
      fun rat_prod  (Rat(m,n), Rat(m',n')) = canon(m*m', n*n');
      fun rat_quo   (x,x') = rat_prod(x, recip x');
    end
  end;
```

This version replaces the local declaration with signature matching.

```
structure Rational : ARITH =
  struct
  abstype t = Rat of int*int
    with
      fun gcd(m,n) =
	if m=0 then  n  else gcd(n mod m, m);
      fun canon (m,n) = 
	  let val d = gcd(abs m, n)
	  in  Rat (m div d, n div d)  end
      fun recip (Rat(m,n)) = if m<0 then Rat(~n,~m) else Rat(n,m)
      val zero = Rat(0, 1);
      fun sum   (Rat(m,n), Rat(m',n')) = canon(m*n' + m'*n, n*n');
      fun diff  (Rat(m,n), Rat(m',n')) = canon(m*n' - m'*n, n*n');
      fun prod  (Rat(m,n), Rat(m',n')) = canon(m*m', n*n');
      fun quo   (x,x') = prod(x, recip x');
    end
  end;
```

__7.10.__

```
abstype date = D of int * int
  with
    local
      val months = [31,28,31,30,31,30,31,31,30,31,30,31];
      fun days m = List.nth (months, m-1);
      fun date_ok (d,m) =
	  1 <= m andalso m <= 12 andalso 1 <= d andalso d <= days m;
    in
      exception Date;

      fun today (d,m) = if date_ok (d,m) then D(d,m) else raise Date;

      fun day   (D(d,m)) = d
      and month (D(d,m)) = m;

      fun tomorrow (D(d,m)) =
	  if date_ok (d+1,m) then D(d+1,m)
	  else if m<12 then D(1,m+1)
	  else raise Date;

      fun yesterday (D(d,m)) =
	  if date_ok (d-1,m) then D(d-1,m)
	  else if m>1 then D(days (m-1), m-1)
	  else raise Date;
    end
  end;
```

__7.11.__ Structure Queue2a from the solution to 7.3 has that signature.

__7.12.__ For example, modify Queue1 to have the following definition of enq. The resulting structure implements a stack rather than a queue.

```
  fun enq(q,x) = q @ [x];
```

__7.13.__ This exercise is up to you. Java is a suitable language to choose because modularity can be expressed using objects.

__7.14.__ It is very poor because it only tests one pattern of usage, where all calls to enq come before all calls to deq.

__7.15.__ The trick is to use type option.

```
structure PathZSP =
  struct
  type t = int option;
  val zero = NONE;
  fun sum (SOME m, SOME n) = SOME (Int.min(m,n))
    | sum (NONE, on) = on
    | sum (om, NONE) = om
  fun prod (SOME m, SOME n) = SOME (m+n) : t
    | prod _ = NONE
  end;
```

__7.16.__ Vectors are related to Basis Library arrays, which are introduced in Section 8.6.

```
functor VMatrixZSP (Z: ZSP) : ZSP =
  let open Vector
  in
  struct

  type t = Z.t vector vector;

  val zero = fromList [];

  fun sum (rowvA,rowvB) = 
      if length rowvA = 0 then rowvB
      else if length rowvB = 0 then rowvA
      else tabulate
	     (length rowvA, 
	      fn i => 
	        let val rowA = sub(rowvA,i)
                    and rowB = sub(rowvB,i)
	        in  tabulate
	                (length rowA, 
	                fn j => Z.sum (sub (rowA,j),
	                               sub (rowB,j)))
                end);

  fun prod (rowvA,rowvB) = 
        if length rowvA = 0 orelse length rowvB = 0 then zero
	else 
	   tabulate
	    (length rowvA, 
	     fn i => 
	      let val rowA = sub(rowvA,i)
	      in  tabulate
	          (length (sub(rowvB,0)),
	           fn j =>
	            let fun adding k = 
	                  if k<0 then Z.zero
	                  else Z.sum (adding (k-1),
	                              Z.prod (sub(rowA,k),
	                                      sub(sub(rowvB,k),j)))
	            in  adding (length rowA - 1)  end)
              end);

  end
  end;
```

__7.17.__ The abstype constructor, called D below, complicates the code slightly and necessitates separating the external versions of insert and update from the ones that do the actual work.

```
functor Dictionary (Key: ORDER) : DICTIONARY = 
  struct
  type key  = string;
  abstype 'a t = D of (key * 'a) list
    with
    
    exception E of key;
  
    val empty = D[];
  
    fun lookup (D((a,x)::pairs), b) =
        (case String.compare(a,b) of
             GREATER => raise E b
           | EQUAL   => x
           | LESS    => lookup(D pairs, b))
      | lookup (D [], b) = raise E b;
  
    fun inserting ((a,x)::pairs, b, y) =
        (case String.compare(a,b) of
             GREATER => (b,y)::(a,x)::pairs
           | EQUAL   => raise E b
           | LESS    => (a,x)::inserting(pairs, b, y))
      | inserting ([], b, y) = [(b,y)];
  
    fun insert (D pairs, b, y) = D (inserting (pairs, b, y));
   
    fun updating ((a,x)::pairs, b, y) =
        (case String.compare(a,b) of
             GREATER => (b,y)::(a,x)::pairs
           | EQUAL   => (b,y)::pairs
           | LESS    => (a,x)::updating(pairs, b, y))
      | updating ([], b, y) = [(b,y)];
  
    fun update (D pairs, b, y) = D (updating (pairs, b, y));
 
    end
  end;
```

__7.18.__ Declaring fresh constructors lets us copy the binary tree code into the abstype body.

```
  abstype t = Lf
            | Br of Item.t * t * t
  with

    val empty = Lf;

    fun null Lf = true
      | null (Br _) = false;

    fun min (Br(v,_,_)) = v;

    fun insert(w, Lf) = Br(w, Lf, Lf)
      | insert(w, Br(v, t1, t2)) =
	  if w <= v then Br(w, insert(v, t2), t1)
	           else Br(v, insert(w, t2), t1);

    fun leftrem (Br(v,Lf,_)) = (v, Lf)
      | leftrem (Br(v,t1,t2)) = 
	  let val (w, t) = leftrem t1
	  in  (w, Br(v,t2,t))  end;

    fun siftdown (w, Lf, _) = Br(w,Lf,Lf)
      | siftdown (w, t as Br(v,_,_), Lf) =
	  if w <= v then Br(w, t, Lf)
	           else Br(v, Br(w,Lf,Lf), Lf)
      | siftdown (w, t1 as Br(v1,p1,q1), t2 as Br(v2,p2,q2)) =
	  if w <= v1 andalso w <= v2 then Br(w,t1,t2)
	  else if v1 <= v2 then Br(v1, siftdown(w,p1,q1), t2)
	     (* v2 < v1 *) else Br(v2, t1, siftdown(w,p2,q2));

    fun delmin Lf = raise Size
      | delmin (Br(v,Lf,_)) = Lf
      | delmin (Br(v,t1,t2)) = 
	  let val (w,t) = leftrem t1
	  in  siftdown (w,t2,t)  end;

    fun heapify (0, vs) = (Lf, vs)
      | heapify (n, v::vs) =
	  let val (t1, vs1) = heapify (n div 2, vs)
	      val (t2, vs2) = heapify ((n-1) div 2, vs1)
	  in  (siftdown (v,t1,t2), vs2)  end;

    fun fromList vs = #1 (heapify (length vs, vs));

    fun toList (t as Br(v,_,_)) = v :: toList(delmin t)
      | toList Lf = [];

    fun sort vs = toList (fromList vs);

    end
```

A dummy constructor allows existing code for binary trees to be invoked. The abstype body looks something like this.

```
  abstype t = PQ of Item.t tree
  with

    val empty = PQ Lf;

    fun null (PQ Lf) = true
      | null  _      = false;

    fun min (PQ(Br(v,_,_))) = v;

    fun insert'(w, Lf) = Br(w, Lf, Lf)
      | insert'(w, Br(v, t1, t2)) =
	  if w <= v then Br(w, insert'(v, t2), t1)
	           else Br(v, insert'(w, t2), t1);

    fun insert (w, PQ t) = PQ (insert' (w, t));

    ...

    end
```

__7.19.__ Needless to say, increasing lists are inherently inefficient. Insertions can take linear time.

```
functor PriorityQueue (Item: ORDER) : PRIORITY_QUEUE = 
  struct
  structure Item = Item;
  fun x <= y = (Item.compare(x,y) <> GREATER);

  abstype t = PQ of Item.t list
  with

    val empty = PQ [];

    fun null (PQ vs) = List.null vs;

    fun min (PQ(v::_)) = v;

    fun insert'(w, [])    = [w]
      | insert'(w, v::vs) =
	  if w <= v then w::v::vs else v :: insert'(w,vs);

    fun insert (w, PQ t) = PQ (insert' (w, t));

    fun delmin (PQ [])      = raise Size
      | delmin (PQ (v::vs)) = PQ vs;

    fun fromList' [] = []
      | fromList' (w::ws) = insert' (w, fromList' ws);

    fun fromList vs = PQ (fromList' vs);

    fun toList (PQ vs) = vs;

    fun sort vs = toList (fromList vs);

    end
  end;
```

__7.20.__ Existing sorting functions can be dropped right into the functor body. Then replace references to specific types (originally real) by the type of sorting function supplied in the functor argument, namely Item.t. The functor body defines its own version of <= for use in the sorting functions. The advantage of implementing two sorting functions is that each has its merits. However, it would actually be better to provide two separate functors. That would be more modular, allowing each to be maintained separately.

```
functor Sorting (Item: ORDER) = 
  struct
  fun x <= y = (Item.compare(x,y) <> GREATER);

  fun quick [] = []
    | quick [x] = [x]
    | quick (a::bs) =  (*the head "a" is the pivot*)
        let fun partition (left,right,[]) : Item.t list = 
                  (quick left) @ (a :: quick right)
              | partition (left,right, x::xs) =
                  if x<=a then partition (x::left, right, xs)
                          else partition (left, x::right, xs)
        in  partition([],[],bs)  end;
  
  fun merge([],ys) = ys : Item.t list
    | merge(xs,[]) = xs
    | merge(x::xs, y::ys) =
        if x<=y then x::merge(xs,  y::ys)
                else y::merge(x::xs,  ys);
  
  fun tmergesort [] = []
    | tmergesort [x] = [x]
    | tmergesort xs =
        let val k = length xs div 2
        in  merge (tmergesort (List.take(xs,k)),
                   tmergesort (List.drop(xs,k)))
        end;
  end;
```

__7.21.__ This solution relies on the convention that multiple arguments in a functor heading are regarded as implicitly defining a signature. We could instead have defined a signature, say EQTYPE, specified by those arguments.

```
functor AssocList (type key; val eq: key*key -> bool) : DICTIONARY = 
  struct
  type key = key;
  exception E of key;

  abstype 'a t = Nil
               | Cons of key * 'a * 'a t

    with

    val empty = Nil;

    fun lookup (Cons(a,x,al), b) =
	  if eq(a,b) then  x  else  lookup(al, b)
      | lookup (Nil, b) = raise E b;

    fun insert (Cons(a,x,al), b, y) =
	  if eq(a,b) then  raise E b  else  Cons (a, x, insert(al, b, y))
      | insert (Nil, b, y) = Cons(b,y,Nil);

    fun update (al, b, y) = Cons(b,y,al)

    end
  end;
```

__7.22.__ This version defines new constructors in order to avoid the annoyance of programming with a dummy constructor.

```
functor AssocList (eqtype key) : DICTIONARY = 
  struct
  type key = key;
  exception E of key;

  abstype 'a t = Nil
               | Cons of key * 'a * 'a t

    with

    val empty = Nil;

    fun lookup (Cons(a,x,al), b) =
	  if a=b then  x  else  lookup(al, b)
      | lookup (Nil, b) = raise E b;

    fun insert (Cons(a,x,al), b, y) =
	  if a=b then  raise E b  else  Cons (a, x, insert(al, b, y))
      | insert (Nil, b, y) = Cons(b,y,Nil);

    fun update (al, b, y) = Cons(b,y,al)

    end
  end;
```

__7.23.__ The lexicographic ordering compares the second components only if the first components are equal.

```
signature PORDER = 
  sig
  type t
  val compare: t*t -> order option
  end;

functor LexPOrder (structure PO1: PORDER and PO2: PORDER) : PORDER =
  struct
  type t = PO1.t * PO2.t;
  fun compare ((x1,y1), (x2,y2)) = 
      (case PO1.compare (x1,x2) of
	   SOME EQUAL => PO2.compare (y1,y2) 
	 | ord => ord)
  end;
```

__7.24.__ This ordering is an inverse image construction. If f(x)=f(y) then we must regard x and y as unrelated.

```
functor InvPOrder (type t; structure PO: PORDER; val f: t -> PO.t) : PORDER =
  struct
  type t = t;
  fun compare (x,y) = 
      (case PO.compare (f x, f y) of
	   SOME EQUAL => NONE
	 | ord => ord)
  end;
```

__7.25.__ All structures are instances of the empty signature.

__7.26.__ ML accepts the declarations of signature TYPE and functor Funny, whose two arguments are required to share. The declarations of structures S1 and S2 are also acceptable. Now S1=DT1 and S2=DT2. Because S1 and S2 denote distinct structures, namely DT1 and DT2, respectively, the attempted declaration of S3 fails due to a violation of the functor's sharing constraint.

__7.27.__ These declarations are correct.

```
structure In =  Inputs (structure PQueue = StringPQueue) 
and       Out = Outputs (structure PQueue = StringPQueue);

structure System = Main (structure In = In and Out = Out);
```

However, if the call to Inputs instead supplied IntegerPQueue, the sharing constraint would be violated.

__7.28.__ The sharing constraint will be violated: new abstract types never share.

__7.29.__ It is identical to the structure declaration except in its first line.

```
functor Queue () : QUEUE = 
  struct
  abstype 'a t = Queue of ('a list * 'a list)
    with
    exception E;
    val empty = Queue([],[]);
    ...
    fun deq(Queue(x::heads,tails)) = norm(Queue(heads,tails))
      | deq(Queue([],_)) = raise E;
    end
  end;
```

__7.30.__ Compared with the signature SEQUENCE presented in Chapter 5, the following signature includes a specification of the sequence type itself.

```
signature SEQUENCE = 
  sig
  exception Empty
  type 'a seq
  val Nil : 'a seq
  val Cons : 'a * (unit -> 'a seq) -> 'a seq
  val cons : 'a * 'a seq -> 'a seq
  val null : 'a seq -> bool
  val hd : 'a seq -> 'a
  val tl : 'a seq -> 'a seq
  ...
  end;

functor Sequence () :> SEQUENCE =
  struct
  exception Empty;

  datatype 'a seq = Nil
                  | Cons of 'a * (unit -> 'a seq);

  fun hd (Cons(x,xf)) = x
    | hd Nil = raise Empty;

  fun tl (Cons(x,xf)) = xf()
    | tl Nil = raise Empty;

  fun cons(x,xq) = Cons(x, fn()=>xq);

  fun null (Cons _) = false
    | null Nil      = true;
  ...
  end;
  
  
functor Search (structure S : SEQUENCE and Q: QUEUE) =
  struct
  fun depthFirst next x =
      let fun dfs [] = S.Nil
          | dfs(y::ys) = S.Cons(y, fn()=> dfs(next y @ ys))
      in  dfs [x]  end;
  
  (*enqueue a list of items*)
  fun enql (q, []) = q
    | enql (q, x::xs) = enql(Q.enq(q,x), xs);
  
  fun breadthFirst next x =
      let fun bfs q = 
            if Q.null q then S.Nil
            else S.Cons(Q.hd q, fn()=> bfs(enql(Q.deq q, next(Q.hd q))))
      in  bfs (Q.enq(Q.empty, x))  end;

  end;
```

__7.31.__ All of these signatures are self-contained.

```
QUEUE1: the types bool and list
QUEUE2: the type bool
QUEUE3: the types bool and list
DICTIONARY: none
FLEXARRAY: the type int
```

__7.32.__ Structure UsedTwice is given all the components of both arguments (which fortunately have no names in common) of functor PriorityQueue . Signature matching discards the surplus components.

__7.33.__ The second open declaration hides most of Queue3's components, except norm, which is not a component of Queue2.

__7.34.__ The constant 2.0 has type Real.real, which differs from type F.real. We can create a version of the number 2 having the correct type by calling the function F.fromInt.

```
functor MultiplePrecision (F: REAL) =
  struct
  fun half x = F./(x, F.fromInt 2)
  end;
```
