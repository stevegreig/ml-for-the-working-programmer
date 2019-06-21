## Chapter 4

__4.1.__ Comparing numbers is clearly the fastest and simplest way to define this sort of ordering.

```
fun rank King = 4
  | rank (Peer(deg,terr,_)) = 3
  | rank (Knight name)  = 2
  | rank (Peasant name) = 1;

fun super(per1,per2) = rank per1 > rank per2;
```

__4.2.__ Here is yet another way of expressing "superior" -- it is rather hard to read, but the number of cases grows only linearly in the number of constructors.

```
datatype person = King
                | Peer    of string*string*int
                | Knight  of string
                | Esquire of string*string
                | Peasant of string;

fun title King = "His Majesty the King"
  | title (Peer(deg,terr,_)) = "The " ^ deg ^ " of " ^ terr
  | title (Knight name)  = "Sir "^ name
  | title (Esquire(name,village))  = name ^ ", Esq., of " ^ village
  | title (Peasant name) = name;

title (Esquire("John Smith","Bottisham"));

fun superior (_, King) = false
  | superior (King, _) = true
  | superior (_, Peer _) = false
  | superior (Peer _, _) = true
  | superior (_, Knight _) = false
  | superior (Knight _, _) = true
  | superior (_, Esquire _) = false
  | superior (Esquire _, _) = true
  | superior (_, _)         = false;
```

__4.3.__

```
datatype figure = Triangle  of real*real*real
                | Rectangle of real*real
                | Line      of real
                | Circle    of real;

fun area (Triangle(a,b,c)) = 
        let val s = (a+b+c)/2.0 in sqrt(s*(s-a)*(s-b)*(s-c)) end
  | area (Rectangle(a,b)) = a*b
  | area (Line _)         = 0.0
  | area (Circle r)       = 3.14159*r*r;
```

__4.4.__

```
datatype country = England | Scotland | Wales | France | Italy | Spain;

fun capital England     = "London"
  | capital Scotland    = "Edinburgh"
  | capital Wales       = "Cardiff"
  | capital France      = "Paris"
  | capital Italy       = "Rome"
  | capital Spain       = "Madrid";
```

__4.5.__ Each function requires only two cases, rather than four.

```
fun conj(false,_) = false
  | conj(true,p)  = p;

fun disj(true,_)  = true
  | disj(false,p) = p;  
```

__4.6.__ King, Peer, Knight and Peasant have precisely the same types as they had after their datatype declaration, replacing person by the type given at the bottom of page 129.

__4.7.__ If we could not define type ('a,'b)sum, we could use ('a list * 'b list) under the correspondence

```
    ([x], []) ~ Inl(x)
    ([], [y]) ~ Inr(y)             
```

__4.8.__ Changing Peasant _ to Peasant_ anywhere changes some outcomes to true.

__4.9.__

```
fun title per = 
      case per of
            King             => "His Majesty the King"
          | Peer(deg,terr,_) => "The " ^ deg ^ " of " ^ terr
          | Knight name      => "Sir "^ name
          | Peasant name     => name;
```

__4.10.__ Replace each occurrence of

```
   case E of P1 => E1 | ... | Pn => En
```

by the expression

```
   let fun f(P1) = E1 | ... | f(Pn) = En in f(E) end
```

where f is a previously unused identifier. This expression has the same context as the case and performs precisely the same pattern-matching. According to the ML Definition, the case expression above actually expands to (see Chapter 5)

```
  (fn P1 => E1 | ... | Pn => En)(E)
```

__4.11.__ Yes. Equality testing is not possible in general for exception values, since they may carry values of arbitrary types.

__4.12.__ Several examples appear later in the book. In parsing, exceptions can signal syntax errors -- see Section 9.3. In unification, exceptions can signal that the two given expressions cannot be unified -- see Section 10.7. In numerical computing, division by zero is almost impossible to predict; all we can do is catch exception Div and try to recover gracefully (perhaps by attempting a different algorithm).

__4.13.__ The following version is linear in the depth of the tree, since both subtrees share. Thus, you can compute compsame(x,100). Try applying reflect to the result!

```
fun compsame (x,n) =
      if n=0 then Lf
      else let val t = fullsame(x, n-1)
           in  Br(x,t,t)  end; 
```

__4.14.__ Calling bal(t) returns the size of t, raising an exception if it is unbalanced. If you dislike exceptions, you could signal an unbalanced tree by returning ~1 instead of its size.

```
exception Unbalanced;
fun bal Lf = 0
  | bal (Br(_,t1,t2)) = 
       let val b1 = bal t1
           and b2 = bal t2
       in  if abs(b1-b2) <= 1 then b1+b2+1
                              else raise Unbalanced
       end;
```

__4.15.__

The third line handles the case when the two trees have different shapes.

```
fun isrefl (Lf, Lf) = true
  | isrefl (Br(x,t1,t2), Br(y,u1,u2)) =
               x=y andalso isrefl(t1,u2) andalso isrefl(t2,u1)
  | isrefl _ = false; 
```

__4.16.__ The following gives us everything except the [x1,x2,...] notation.

```
infixr 5 ::;
datatype 'a list = nil 
                 | :: of 'a * 'a list;
```

__4.17.__

```
datatype ('a,'b) ltree = 
       Leaf of 'b
     | Branch of 'a * ('a,'b) ltree * ('a,'b) ltree;
```

__4.18.__ See pages 164–165 for examples of functions that operate on datatypes that involve recursion over the list type.

```
datatype 'a mtree = Lf
                  | Br of 'a * ('a mtree) list;
```
                
__4.19.__ This is a bit sketchy but tries to indicate how much time is wasted performing appends. inorder(birnam) performs 9 cons operations while inord(birnam,[]) performs only 4.

```
inorder(Br("The",Br("wood",Lf,Br #),Lf))
==> inorder(Br("wood",Lf,Br("of",Br #,Lf))) @ ["The"] @ inorder Lf
==> (inorder Lf @ ["wood"] @ inorder(Br("of",Br #,Lf))) @ ["The"] @ inorder Lf
==> ([] @ ["wood"] @ inorder(Br("of",Br #,Lf))) @ ["The"] @ inorder Lf
==> (["wood"] @ inorder(Br("of",Br #,Lf))) @ ["The"] @ inorder Lf
==> (["wood"] @ (inorder(Br("Birnam",Lf,Lf)) @ ["of"] @ inorder Lf)) @ 
    ["The"] @ inorder Lf
==> (["wood"] @ 
     ((inorder Lf @ ["Birnam"] @ inorder Lf) @ ["of"] @ inorder Lf)) @ 
    ["The"] @ inorder Lf
==> (["wood"] @ (([] @ ["Birnam"] @ inorder Lf) @ ["of"] @ inorder Lf)) @ 
    ["The"] @ inorder Lf
==> (["wood"] @ ((["Birnam"] @ inorder Lf) @ ["of"] @ inorder Lf)) @ 
    ["The"] @ inorder Lf
==> (["wood"] @ ((["Birnam"] @ []) @ ["of"] @ inorder Lf)) @ 
    ["The"] @ inorder Lf
==> (["wood"] @ (["Birnam"] @ ["of"] @ inorder Lf)) @ ["The"] @ inorder Lf
==> (["wood"] @ (["Birnam","of"] @ inorder Lf)) @ ["The"] @ inorder Lf
==> (["wood"] @ (["Birnam","of"] @ [])) @ ["The"] @ inorder Lf
==> (["wood"] @ ("Birnam"::(["of"] @ []))) @ ["The"] @ inorder Lf
==> (["wood"] @ ["Birnam","of"]) @ ["The"] @ inorder Lf
==> ["wood","Birnam","of"] @ ["The"] @ inorder Lf
==> "wood"::(["Birnam","of"] @ ["The"]) @ inorder Lf
==> "wood"::"Birnam"::(["of"] @ ["The"]) @ inorder Lf
==> ["wood","Birnam","of","The"] @ inorder Lf
==> ["wood","Birnam","of","The"] @ []
==> "wood"::(["Birnam","of","The"] @ [])
==> "wood"::"Birnam"::(["of","The"] @ [])
==> "wood"::"Birnam"::("of"::(["The"] @ []))
==> ["wood","Birnam","of","The"]
```

__4.20.__ The last one is proved on pages 231–232.

```
 preorder(reflect(t)) = rev(postorder(t))
  inorder(reflect(t)) = rev(inorder(t))
postorder(reflect(t)) = rev(preorder(t))
```
                
__4.21.__ We exploit the previous exercise. This approach is fastest because any direct method would require access to the last element of the list.

```
fun balpostorder xs = reflect (balpreorder (rev xs));
```

__4.22.__ We use cartprod from Chapter 3. Given a list of length n+1, the left subtree (recursively) gets from 0 to n elements of the tail, while the right subtree gets the remainder.

```
fun allpre []      = [Lf]
  | allpre (x::xs) =
     let fun joinx [] = []
           | joinx ((t1,t2)::pairs) = Br(x,t1,t2) :: joinx pairs
         fun step i = joinx (cartprod (allpre(List.take(xs,i)), 
                                       allpre(List.drop(xs,i))))
         fun build 0 = []
           | build i = step(i-1) @ build(i-1)
     in  build (1 + length xs)  end;
```

__4.23.__ We could then use Lf and Br only as values, not as constructors in patterns.

__4.24.__ Since each tree is linear, the sequence of insertions should be obvious.

```
        M        E
       /          \
      J            F
     /              \
    H                H
   /                  \
  F                    J
 /                      \
E                        M
                        

    M        E
   /          \
  E            M
   \          /
    J        F
   /          \
  F            J
   \          /
    H        H   
```

__4.25.__ The representation is not quite the same as association lists, which are unordered.

```
structure Dict' : DICTIONARY = 
   struct
   type key  = string;
   type 'a t = (key * 'a) list;
   exception E of key;

   val empty = [];

   fun lookup ((a,x)::pairs, b) =
             (case String.compare(a,b) of
                  GREATER => raise E b
                | EQUAL   => x
                | LESS    => lookup(pairs, b))
     | lookup ([], b) = raise E b;

   fun insert ((a,x)::pairs, b, y) =
             (case String.compare(a,b) of
                  GREATER => (b,y)::(a,x)::pairs
                | EQUAL   => raise E b
                | LESS    => (a,x)::insert(pairs, b, y))
     | insert ([], b, y) = [(b,y)];

   fun update ((a,x)::pairs, b, y) =
             (case String.compare(a,b) of
                  GREATER => (b,y)::(a,x)::pairs
                | EQUAL   => (b,y)::pairs
                | LESS    => (a,x)::update(pairs, b, y))
     | update ([], b, y) = [(b,y)];
   end;
```

__4.26.__ A functional array containing 2n*1 elements will contain one element at the root, n elements (all with even subscripts) in the left subtree, and n elements (all with odd subscripts greater than one) in the right subtree.

```
fun array(n,x) =
      if n=0 then Lf
      else Br(x, array(n div 2, x), 
                 array((n-1) div 2, x));  
```

__4.27.__ Even and odd subscripted elements from the two subtrees are interleaved to form a single list.

```
fun interleave(xs, [])       = xs
  | interleave(x::xs, y::ys) = x::y::interleave(xs,ys);
                        
fun listofarray Lf            = []
  | listofarray (Br(v,t1,t2)) =
        v :: interleave(listofarray t1, listofarray t2);
```

__4.28.__ Empty nodes contain []; the label v is represented by the list [v].

```
fun sub (Lf, _) = raise Subscript
  | sub (Br(vs,t1,t2), k) =
       if k=1 then case vs of [v] => v | [] => raise Subscript
       else if k mod 2 = 0 
       then sub (t1, k div 2)
       else sub (t2, k div 2);
                        
fun update (Lf, k, w) = 
       if k = 1 then Br ([w], Lf, Lf)
       else if k mod 2 = 0 
       then Br ([],  update(Lf, k div 2, w),  Lf)
       else Br ([],  Lf,  update(Lf, k div 2, w))
  | update (Br(vs,t1,t2), k, w) =
       if k = 1 then Br ([w], t1, t2)
       else if k mod 2 = 0 
       then Br (vs,  update(t1, k div 2, w),  t2)
       else Br (vs,  t1,  update(t2, k div 2, w));
```

__4.29.__

```
     4
                        
                              4
                             /
                            2
                        
                              6
                             / \
                            2   4
                        
                              6
                             / \
                            2   4
                           /
                          1
                        
                              6
                            /   \
                           2     5
                          /     /
                         1     4
                        
                              8
                             / \
                           /     \
                          6       5
                         / \     /
                        1   2   4 
                        
                              8
                             / \
                           /     \
                          6       5
                         / \     / \
                        1   2   4   5
```

__4.30.__ Functional arrays: convert the subscript to binary, delete the leading 1, and reverse the remaining bits. Change 0 to left and 1 to right. This yields the path from the root to the subscripted node. For instance, subscript 12 = 1100 in binary; reversing 001 yields left, left, right. Conventional heap sort is similar, but do not reverse the bits. Subscript 12 becomes right, left, left.

__4.31.__ This is something of a joke. Removing bits from the left is not easy, requiring repeated division. For n>1, call "left n" to see whether or not to branch to the left, and "chop n" for the subscript to pass in the recursive call.

```
fun left n = if n>3 then left (n div 2) else (n=2);
fun chop n = if n>3 then 2*chop(n div 2) + n mod 2 else 1;
```
                
__4.32.__ The code can be simplified because there is only one operator of each precedence. In general we cannot assume that all operators of a given precedence can be grouped arbitrarily.

```
fun showp (k, Atom a) = a
  | showp (k, Neg p) = "~ " ^ showp(3,p)
  | showp (k, Conj(p,q)) =
       if k>2 then "(" ^ showp(k,p) ^ " & " ^ showp(k,q) ^ ")"
       else       showp(2,p) ^ " & " ^ showp(2,q)
  | showp (k, Disj(p,q)) =
       if k>1 then "(" ^ showp(k,p) ^ " | " ^ showp(k,q) ^ ")"
       else       showp(1,p) ^ " | " ^ showp(1,q);    
```

__4.33.__ Ideally, showp and eval should be curried functions (see Chapter 5).

```
fun eval (trs, Atom a)    = a mem trs
  | eval (trs, Neg p)     = not (eval(trs,p))
  | eval (trs, Conj(p,q)) = eval(trs,p) andalso eval(trs,q)
  | eval (trs, Disj(p,q)) = eval(trs,p) orelse  eval(trs,q);
```

__4.34.__ This code is arguably clearer than that presented in the book!

```
fun ldistrib (ps, []) = []
  | ldistrib (ps, q::qs) = 
         let val rest = ldistrib(ps,qs)
             fun pairall ([], q) = rest
               | pairall (p::ps, q) = (p@q) :: pairall(ps,q)
         in  pairall(ps,q)  end;
                        
 fun lcnf (Conj(p,q)) = lcnf p @ lcnf q
   | lcnf (Disj(p,q)) = ldistrib (lcnf p, lcnf q)
   | lcnf p = [[p]]    (*a literal*) ;
```

__4.35.__ This exercise examines the point, made by some authors, that cases in a function declaration should never overlap. There are two approaches.

Expand distrib by writing out all the possible cases for the arguments not covered by the first pattern, namely (p, Conj(q,r)).
Express the function in terms of conditional expressions and the function is_conj, itself coded according to the no-overlap dogma. This results in loss of clarity.

```
fun is_conj (Atom a)    = false
  | is_conj (Neg p)     = false
  | is_conj (Disj(p,q)) = false
  | is_conj (Conj(p,q)) = true;
```
                
__4.36.__ Simply exchange the roles of Conj and Disj in distrib and the functions defined after it.
