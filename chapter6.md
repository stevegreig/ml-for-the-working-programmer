## Chapter 6

__6.1.__ By induction on n. Base case: If n=0 then q=r=0. For the induction step, assume that n = dq+r where 0<=r<d; we have to prove the theorem for n+1. There are two cases. If r+1<d then n+1 = dq + (r+1): the desired quotient is q and the remainder is r+1. Otherwise r+1=d (since r<d) and n+1 = dq + d = d(q+1): the desired quotient is q+1 and the remainder is 0.

The corresponding ML division function is even less efficient than repeated subtraction!

```
fun divide (n,d) =
  if n=0 then (0,0)
  else let val (q,r) = divide (n-1,d)
       in  if r+1<d then (q,r+1)
           else (q+1,0)
       end;
```

__6.2.__ If we can prove phi(n) by mathematical induction, then we have proofs of the base case, phi(0), and the induction step, that phi(n) implies phi(n+1) for all n. For complete induction, we have to prove phi(n) and may assume phi(k) if k<n. Now consider two cases. If n=0 then use our existing proof of phi(0). If n=k+1 for some k, then since k<n we may assume phi(k); by the induction step, we obtain phi(k+1). In both cases we have proved phi(n).

__6.3.__ If we can prove phi(n) by complete induction, then we have a proof of phi(n) from forall k. k<n --> phi(k). To obtain a proof by mathematical induction, take the formula forall k. k<n --> phi(k). The base case of this induction is forall k. k<0 --> phi(k), which holds trivially because k<0 is contradictory. For the induction step, assume forall k. k<n --> phi(k); we have to show forall k. k<n+1 --> phi(k), which is equivalent to forall k. k<n | k=n --> phi(k) and thus to (forall k. k<n --> phi(k)) & phi(n). Now we are finished, because forall k. k<n --> phi(k) is just the induction hypothesis and phi(n) follows from it by our previous proof that used complete induction.

Now, we have proved forall k. k<n --> phi(k) for all n using only mathematical induction. Now replace n by m+1, and forall k. k<m+1 --> phi(k) obviously implies phi(m). So phi holds for all natural numbers.

__6.4.__ The proof that introot(n) computes the integer square root of n is by complete induction on n. Thus, we may assume the correctness of introot(m) for 0<=m<n. We do a case analysis on n: if n=0 then its square root is 0, which is introot(0). Otherwise, n>0. We write n=4m+r; by the induction hypothesis, introot(m) computers the integer square root of m. The rest of the proof is by the chain of inequalities presented in section 2.16.

__6.5.__ Problems that might be mentioned include the following.

* Newton-Raphson depends upon the calculus, not just on basic arithmetic.
* Computers do not perform real arithmetic exactly, so rounding errors must be taken into account.
* Termination is rather tricky in this context. There is no obvious way to use induction.

__6.6.__ The base case is []@[] = [], which is trivial. For the induction step, assume xs@[] = xs (the induction hypothesis); we must show (x::xs)@[] = x::xs. But (x::xs)@[] = x::(xs@[]) = x::xs by the definition of append and the induction hypothesis.

__6.7.__ Perform induction on l1. The base case is []@(l2@l3) = ([]@l2)@l3, which is trivial as both sides simplify to l2@l3. For the induction step, assume xs@(l2@l3) = (xs@l2)@l3 (the induction hypothesis); we must show (x::xs)@(l2@l3) = ((x::xs)@l2)@l3. Simplifying the left side of this equation, we find (x::xs)@(l2@l3) = x :: (xs@(l2@l3)) = x :: ((xs@l2)@l3) by the definition of append and the induction hypothesis. Simplifying the right side yields ((x::xs)@l2)@l3 = (x::(xs@l2))@l3 = x :: ((xs@l2)@l3) by the definition of append. Both sides of the desired equation are now equal.

__6.8.__ This proof requires Theorem 10 (from the text) as a lemma. The base case, nrev (nrev []) = [], is trivial. For the induction step, assume nrev (nrev xs) = xs (the induction hypothesis); we must show nrev (nrev (x::xs)) = x::xs. But nrev (nrev (x::xs)) = nrev ((nrev xs) @ [x]) = nrev[x] @ nrev (nrev xs) = [x] @ xs = x::xs by the definition of nrev, Theorem 10, the induction hypothesis and the definition of append.

__6.9.__ We must prove a more general property: forall n. n + nlength xs = addlen(n,xs). Since length xs = addlen(0,xs), the desired equation will follow.

The base case is n + nlength[] = addlen(n,[]), which is trivial as both sides simplify to n. For the induction step, assume forall n. n + nlength xs = addlen(n,xs); this induction hypothesis holds for all n, but one fixed list xs. We must show forall n. n + nlength (x::xs) = addlen(n,x::xs). Letting n be fixed, we find n + nlength (x::xs) = n + 1 + nlength xs = addlen(n+1, xs) = addlen(n,x::xs) by the definitions of nlength and addlen, and using the induction hypothesis with the value n+1.

__6.10.__ The theorem statement is Br(x,t,t') <> t. (Free variables are implicitly universally quantified.) The proof is by structural induction on t. The base case, Br(x,Lf,t') <> Lf, holds because no Br can equal any Lf (freeness property of distinct constructors). For the induction step, assume Br(x,t1,t') <> t1 and Br(x,t2,t') <> t2 (the induction hypotheses); we must show Br(x,Br(y,t1,t2),t') <> Br(y,t1,t2). The proof is by contradiction: if Br(x,Br(y,t1,t2),t') <> Br(y,t1,t2) then (by freeness again) we have x=y, t'=t2 and also Br(y,t1,t2) = t1, that is, Br(x,t1,t') = t1, which contradicts an induction hypothesis.

__6.11.__ The base case, size(reflect Lf) = size Lf, is trivial because both sides equal zero. For the induction step, assume size(reflect t1) = size t1 and size(reflect t2) = size t2 (the induction hypotheses); we must show size(reflect (Br(x,t1,t2))) = size (Br(x,t1,t2)).

But size(reflect (Br(x,t1,t2))) = size(Br(x, reflect t2, reflect t1)) = 1 + size(reflect t2) + size(reflect t1) = 1 + size t2 + size t1 = size (Br(x,t1,t2)) by the definitions of size and reflect, commutativity of + and both induction hypotheses. (Isn't this easy?)

__6.12.__ The base case, nlength(preorder Lf) = size Lf, is trivial: both sides equal zero. For the induction step, assume nlength(preorder t1) = size t1 and nlength(preorder t2) = size t2 (the induction hypotheses); we must show nlength(preorder (Br(x,t1,t2))) = size (Br(x,t1,t2)).

But nlength(preorder (Br(x,t1,t2))) = nlength([x] @ preorder t1 @ preorder t2) = 1 + nlength(preorder t1) + nlength(preorder t2) = 1 + size t1 + size t2 = size (Br(x,t1,t2)) by the definitions of nlength, size and preorder, and both induction hypotheses.The proof also uses Theorem 8 (from the text), which concerns nlength and append.

__6.13.__ The base case, nrev(inorder(reflect Lf)) = inorder Lf, is trivial: both sides equal []. For the induction step, assume nrev(inorder(reflect t1)) = inorder t1 and nrev(inorder(reflect t2)) = inorder t2 (the induction hypotheses); we must show nrev(inorder(reflect (Br(x,t1,t2)))) = inorder (Br(x,t1,t2)).

But nrev(inorder(reflect (Br(x,t1,t2)))) = nrev(inorder(Br(x, reflect t2, reflect t1))) = nrev(inorder (reflect t2) @ [x] @ inorder (reflect t1)) = nrev(inorder (reflect t1)) @ nrev[x] @ nrev(inorder (reflect t2)) = inorder t1 @ [x] @ inorder t2 = inorder (Br(x,t1,t2)). The proof uses the definitions of nrev, inorder and reflect, both induction hypotheses and Theorem 10 (from the text), which concerns nrev and append.

__6.14.__ Here is the function:

```
fun leaves Lf = 1
  | leaves (Br(v,t1,t2)) = leaves t1 + leaves t2;
```

The base case, leaves Lf = size Lf + 1, is trivial: both sides equal one. For the induction step, assume leaves t1 = size t1 + 1 and leaves t2 = size t2 + 1 (the induction hypotheses); we must show leaves(Br(x,t1,t2)) = size (Br(x,t1,t2)) + 1.

But leaves(Br(x,t1,t2)) = leaves t1 + leaves t2 = size t1 + 1 + size t2 + 1 = size (Br(x,t1,t2)) + 1 by the definitions of size and leaves, elementary arithmetic and both induction hypotheses.

__6.15.__ Recall the declaration of preord:

```
fun preord (Lf, vs) = vs
  | preord (Br(v,t1,t2), vs) = v :: preord (t1, preord (t2, vs));
```

The theorem statement must be generalized to forall vs. preord(t,vs) = preorder t @ vs.

The base case, preord(Lf,vs) = preorder Lf @ vs, is trivial: both sides equal vs. For the induction step, assume forall vs. preord(t1,vs) = preorder t1 @ vs and forall vs. preord(t2,vs) = preorder t2 @ vs (two quantified induction hypotheses); we must show forall vs. preord(Br(x,t1,t2),vs) = preorder (Br(x,t1,t2)) @ vs.

But preord(Br(x,t1,t2),vs) = x :: preord(t1, preord(t2, vs)) = x :: preord(t1, preorder t2 @ vs) = x :: (preorder t1 @ preorder t2 @ vs) = ([x] @ preorder t1 @ preorder t2) @ vs = preorder (Br(x,t1,t2)) @ vs. The proof uses the definitions of append, preord and preorder. The induction hypothesis for t2 is used with the same value of vs, but the induction hypothesis for t1 is used with the value preorder t2 @ vs.

__6.16.__ This exercise is easy provided you do not get confused by the presence of map. Perform induction on xs. The base case is map f ([] @ ys) = map f [] @ map f ys, which is trivial as both sides simplify to map f ys. For the induction step, assume map f (xs @ ys) = map f xs @ map f ys (the induction hypothesis); we must show map f ((x::xs) @ ys) = map f (x::xs) @ map f ys. But map f ((x::xs) @ ys) = map f (x :: (xs@ys)) = (f x) :: map f (xs@ys) = (f x) :: (map f xs @ map f ys) by the definitions of map and append, followed by the induction hypothesis. Finally we have (f x) :: (map f xs @ map f ys) = ((f x) :: map f xs) @ map f ys = map f (x::xs) @ map f ys and we are done.

__6.17.__ By extensionality, it suffices to prove map f (nrev xs) = nrev (map f xs). Perform induction on xs. The base case is map f (nrev []) = nrev (map f []), when both sides simplify to []. For the induction step, assume the induction hypothesis, map f (nrev xs) = nrev (map f xs). We must show map f (nrev (x::xs)) = nrev (map f (x::xs)). But map f (nrev (x::xs)) = map f (nrev xs @ [x]) = map f (nrev xs) @ map f [x] by the definition of nrev and the previous exercise. Now map f (nrev xs) @ map f [x] = nrev (map f xs) @ [f x] = nrev (f x :: map f xs) = nrev (map f (x::xs)) by the induction hypothesis and the definitions of map and nrev.

__6.18.__ Here is maptree:

```
fun maptree f Lf = Lf
  | maptree f (Br(v,t1,t2)) = 
      Br(f v, maptree f t1, maptree f t2);
```

The first of the requested equations is easy enough for you to prove yourself, given the definition of maptree.

To prove the second equation, it suffices by extensionality to prove map f (preorder t) = preorder (maptree f t). Perform structural induction on t. The base case, map f (preorder Lf) = preorder (maptree f Lf), is trivial: both sides collapse to []. For the induction step, assume the induction hypotheses map f (preorder t1) = preorder (maptree f t1) and map f (preorder t2) = preorder (maptree f t2). We must show map f (preorder (Br(x,t1,t2))) = preorder (maptree f (Br(x,t1,t2))).

Simplifying the left-hand side, we find map f (preorder (Br(x,t1,t2))) = map f ([x] @ preorder t1 @ preorder t2) = map f [x] @ map f (preorder t1) @ map f (preorder t2) = [f x] @ preorder (maptree f t1) @ preorder (maptree f t2) by the definitions of preorder and map, Exercise 6.16 and the induction hypotheses.

Simplifying the right-hand side, we find preorder (maptree f (Br(x,t1,t2))) = preorder (Br(f x, maptree f t1, maptree f t2)) = [f x] @ preorder (maptree f t1) @ preorder (maptree f t2) by the definitions of maptree and preorder. The left and right-hand sides are now identical, completing the proof.

__6.19.__ This exercise is also easy. Perform induction on xs. The base case is foldr (op::) ys [] = []@ys, and both sides simplify to ys. For the induction step, assume foldr (op::) ys xs = xs@ys (the induction hypothesis); we must show foldr (op::) ys (x::xs) = (x::xs)@ys. But foldr (op::) ys (x::xs) = x :: foldr (op::) ys xs = x :: (xs@ys) = (x::xs)@ys by the definitions of foldr and append.

__6.20.__ Perform induction on xs. The base case is foldl f z ([]@ys) = foldl f (foldl f z []) ys, and both sides simplify to foldl f z ys. For the induction step, assume forall z. foldl f z (xs@ys) = foldl f (foldl f z xs) ys, a quantified induction hypothesis. We must show forall z. foldl f z ((x::xs)@ys) = foldl f (foldl f z (x::xs)) ys. Simplifying the left-hand side, we find foldl f z ((x::xs)@ys) = foldl f z (x::(xs@ys)) = foldl f (f(x,z)) (xs@ys) = foldl f (foldl f (f(x,z)) xs) ys by the definitions of append and foldl and the induction hypothesis instantiated with f z.

Simplifying the right-hand side, we find foldl f (foldl f z (x::xs)) ys = foldl f (foldl f (f(x,z)) xs) ys by the definition of foldl. The two sides are equal.

__6.21.__ If F = foldr(op.) then F e [] = e and F e (x::l) = x . (F e l) for all x and l. To show (F e l) . y = F y l, use induction on l. The base case holds because (F e []) . y = e . y = y = F y []. In the induction step, we may assume (F e l) . y = F y l and must show (F e (x::l)) . y = F y (x::l). Here (F e (x::l)) . y = x . (F e l) . y = x . (F y l) = F y (x::l), using the laws for F, associativity and the induction hypothesis.

__6.22.__ If G(l,z) = F z l then G([],z) = z and G(x::l,z) = x . G(l,z) for all z, x and l. The theorem is proved by induction on ls, which is a list of lists. The base case is foldr G e [] = e = F e [] = F e (map (F e) []). For the induction step, assume foldr G e ls = F e (map (F e) ls) in order to show foldr G e (l::ls) = F e (map (F e) (l::ls)). Simplifying the left-hand side, we find foldr G e (l::ls) = G(l, foldr G e ls) = G(l, F e (map (F e) ls)) = F (F e (map (F e) ls)) l using the laws for G and the induction hypothesis.

Simplifying the right-hand side, we find F e (map (F e) (l::ls)) = F e ((F e l) :: map (F e) ls) = F e l . (F e (map (F e) ls) = F (F e (map (F e) ls)) l using the laws for F and Exercise 6.21. The two sides are equal.

__6.23.__ Let phi(p) be a formula in one variable, of type prop. To show that phi(p) holds for all p, it suffices to show the following four facts.

```
phi(Atom a) for all a
phi(p) implies phi(Neg p)
phi(p) and phi(q) imply phi(Conj(p,q))
phi(p) and phi(q) imply phi(Disj(p,q))
```

The justification is that any p of type prop consists of finitely many applications of the constructors Atom, Neg, Conj and Disj. The four cases above cover all possible ways of constructing p, and in each case phi(p) holds.

Now to show nnf p = nnfpos p & nnf (Neg p) = nnfneg p. The atomic case is nnf (Atom a) = nnfpos (Atom a) & nnf (Neg (Atom a)) = nnfneg (Atom a). Simplifying by the definitions of these functions yields (Atom a) = (Atom a) & Neg (Atom a) = Neg (Atom a), which is trivially true.

Next is the Neg case: under the assumption nnf p = nnfpos p & nnf (Neg p) = nnfneg p, we must show nnf (Neg p) = nnfpos (Neg p) & nnf (Neg (Neg p)) = nnfneg (Neg p). This is very easy, as simplification reduces it to nnf (Neg p) = nnfneg p & nnf p = nnfpos p by the definitions of nnf, nnfpos and nnfneg; this is just the induction hypothesis with the conjuncts exchanged.

Next is the Conj case: under the assumptions nnf p = nnfpos p & nnf (Neg p) = nnfneg p and nnf q = nnfpos q & nnf (Neg q) = nnfneg q, we must show nnf (Conj(p,q)) = nnfpos (Conj(p,q)) & nnf (Neg (Conj(p,q))) = nnfneg (Conj(p,q)). Considering the first conjunct, we have nnf (Conj(p,q)) = Conj(nnf p, nnf q) = Conj(nnfpos p, nnfpos q) = nnfpos (Conj(p,q)) by the definitions of nnf and nnfpos, and the induction hypotheses. As for the second conjunct, we have nnf (Neg (Conj(p,q))) = nnf (Disj(Neg p, Neg q)) = Disj(nnf (Neg p), nnf (Neg q))) = Disj(nnfneg p, nnfneg q) = nnfneg (Conj(p,q)) by the definitions of nnf, nnfneg and the induction hypotheses.

The Disj case is very similar to the Conj case and is therefore omitted.

__6.24.__ The function isnnf can be declared as follows.

```
fun isnnf (Atom a) = true
  | isnnf (Neg (Atom a)) = true
  | isnnf (Conj(p,q)) = isnnf p  andalso  isnnf q
  | isnnf (Disj(p,q)) = isnnf p  andalso  isnnf q
  | isnnf _ = false;
```

The proof that isnnf (nnf p) = true follows that of Theorem 17 in the text, using induction on the size of the proposition p. The proof again has seven cases, corresponding to the definition of nnf.

```
isnnf (nnf (Atom a)) = isnnf (Atom a) = true by the definitions of isnnf and nnf.
isnnf (nnf (Neg (Atom a))) = isnnf (Neg (Atom a)) = true similarly.
isnnf (nnf (Conj(r,q))) = isnnf (Conj(nnf r, nnf q)) = isnnf (nnf r) & isnnf (nnf q) = true & true = true. Here the proof uses the induction hypothesis applied to r and q, since they are smaller than Conj(r,q).
isnnf (nnf (Disj(r,q))) holds similarly.
isnnf (nnf (Neg (Conj(r,q)))) = isnnf (nnf (Disj(r,q))) = isnnf (Disj(nnf r, nnf q)) = isnnf (nnf r) & isnnf (nnf q) = true & true = true.
isnnf (nnf (Neg (Disj(r,q)))) holds similarly.
isnnf (nnf (Neg (Neg p))) = isnnf (nnf p) = true using the induction hypothesis applied to p, which is smaller than Neg (Neg p).
```

__6.25.__ The proof that Tr (nnf p) = Tr p again follows that of Theorem 17 in the text, since that is the natural way to reason about nnf. Here, the seven cases are as follows:

```
Tr (nnf (Atom a)) = Tr (Atom a) = true by the definition of nnf.
Tr (nnf (Neg (Atom a))) = Tr (Neg (Atom a)) similarly.
Tr (nnf (Conj(r,q))) = Tr (Conj(nnf r, nnf q)) = Tr (nnf r) & Tr (nnf q) = Tr r & Tr q = Tr (Conj(r,q)). The proof uses the definitions of nnf and Tr and the induction hypothesis applied to r and q.
Tr (nnf (Disj(r,q))) holds similarly.
Tr (nnf (Neg (Conj(r,q)))) = Tr (nnf (Disj(r,q))) = Tr (Disj(nnf r, nnf q)) = Tr (nnf r) | Tr (nnf q) = Tr r | Tr q = ¬ (Tr r & Tr q) = Tr (Neg (Conj(r,q))) by the definitions of nnf and Tr, the induction hypotheses and the de Morgan laws.
Tr (nnf (Neg (Disj(r,q)))) holds similarly.
Tr (nnf (Neg (Neg p))) = Tr (nnf p) = Tr p using the induction hypothesis applied to p, which is smaller than Neg (Neg p).
```

__6.26.__ An example is the relation on pairs of natural numbers (x,y) that orders them on their first component while ignoring the second. Such relations are useful for proving the termination of functions such as revapp and addlen, which recur down their first argument while accumulating results in their second argument. The termination of such functions is determined by the first argument only.

__6.27.__ The desired wf relation is the lexicographic ordering of pairs of natural numbers. In the third case of ack, the recursive call ack(m,n-1) decreases the second argument, while the enclosing call to ack decreases the first argument (while greatly increasing the second argument).

The proof that ack(m,n) > m+n follows (as usual) the function's recursive definition. We may assume the inequality for m', n' such that m'<m or m'=m and n'<n. Now if m=0 then ack(0,n) = n+1 > n. If m>0 and n=0 then ack(m,0) = ack(m-1,1) > (m-1)+1 = m, using the induction hypothesis for the smaller pair (m-1,1). For the general case, it helps to write the induction hypothesis as ack(m,n) >= m+n+1. If m, n > 0 then ack(m,n) = ack(m-1, ack(m,n-1)) >= (m-1) + ack(m,n-1) + 1 >= (m - 1) + m + (n - 1) + 2 = 2m + n. So ack(m,n) >= 2m+n > m+n since m>0.

__6.28.__ The simplest example is the immediate predecessor relation on the natural numbers: i precedes j if j = i+1. "Less than" is the transitive closure of this relation.

Let < be a wf relation and write its transitive closure as <+. If there exists an infinite decreasing chain ... <+ xn <+ ... <+ x2 <+ x1 then we can find an infinite decreasing chain involving < by expanding each inequality x(k+1) <+ xk into a finite chain x(k+1) = ym < ... < y2 < y1 = xk. So if there are no infinite decreasing chains for < then there are none for <+ either.

__6.29.__ The function half is defined by well-founded recursion on the set of even natural numbers. The wf relation is simply "less than" on the even naturals, or equivalently the predecessor relation given by i precedes j if j = i+2.

__6.30.__ If you perform induction using the "tail of" relation to prove phi(l), then it is possible to perform case analysis on the structure of l. If l = [] then l has no predecessors under the "tail of" relation, so phi([]) must be proved outright, just as in structural induction. If l = x::xs then it has one predecessor, namely xs: we are allowed to assume phi(xs) while proving phi(x::xs). This situation again mirrors structural induction.

__6.31.__ This exercise chiefly refers to the x>y case in Theorem 20, and it is pretty much a mirror image of the x<=y case already treated.

__6.32.__ There's always ordered'(l) = (tmergesort(l) = l). The proof that ordered'(l) implies ordered(l) is trivial, given Theorem 21. For the converse implication, it would suffice to prove ordered(l) implies tmergesort(l) = l. That can be proved by induction on the length of l, rather in the style of Theorem 24. (Sorry: it is not easy to think of an alternative definition of ordered.)

__6.33.__ It is an easy consequence of the corresponding properties of addition. To show b1 U+ b2 = b2 U+ b1 it suffices by extensionality to show (b1 U+ b2)(x) = (b2 U+ b1)(x), which is equivalent to b1(x)+b2(x) = b2(x)+b1(x). Associativity is similar.

__6.34.__ To prove bag (ins(x,xs)) = {x} U+ bag xs, use structural induction on the list xs. The base case holds because bag (ins(x,[])) = bag [x] = {x} = {x} U+ {} = {x} U+ bag []. To prove the induction step, bag (ins(x,y::xs)) = {x} U+ bag (y::xs), consider separately the cases x<=y and y<x. If x<=y then bag (ins(x,y::xs)) = bag (x::y::xs)) = {x} U+ bag (y::xs) and we are finished without even using the induction hypothesis. If y<x then bag (ins(x,y::xs)) = bag(y::ins(x,xs)) = {y} U+ bag(ins(x,xs)) = {y} U+ {x} U+ bag xs = bag (x::y::xs) by the definition of bag, the induction hypothesis and the commutative property.

To prove bag (insort xs) = bag xs, use structural induction on the list xs. The base case is trivial: because bag (insort []) = bag [] by the definition of insort alone. To prove the induction step, bag (insort (x::xs)) = bag (ins(x, insort xs)) = {x} U+ bag(insort xs) = {x} U+ bag xs = bag (x::xs) by then bag (ins(x,y::xs)) = bag(y::ins(x,xs)) = {y} U+ bag(ins(x,xs)) = {y} U+ {x} U+ bag xs = the definitions of insort and bag, and the induction hypothesis.

__6.35.__ The merge operation can suppress repetitions by testing whether the lists being merged have equal heads.

```
fun merge([],ys) = ys : real list
  | merge(xs,[]) = xs
  | merge(x::xs, y::ys) =
      if x=y then x::merge(xs, ys)  
      else if x<y then x::merge(xs,  y::ys)
                  else y::merge(x::xs,  ys);
```

What about repetitions in the lists xs and ys? By induction on the length of the original list, we can prove that no repetitions can occur, using induction hypotheses that tell us that xs and ys are repetition-free. To state the correctness theorems for sorting, replace multisets by ordinary sets. Replace the function bag by a function set(xs) such that set[] = {} and set(x::xs) = {x} U set(xs).
