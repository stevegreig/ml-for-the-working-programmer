## Chapter 8

__8.1.__ False. Different reference cells can contain the same value. Try evaluating ref(0)=ref(0) at top level.

__8.2.__ It is essential to use a curried function:

```
fun +:= r = let val v0 = ! r in fn v => r:= v0 + v end;
```

__8.3.__ ML complains that :=! and *! are not declared as identifiers. Remember that symbolic identifiers must be separated by white space or other symbols.

Another common error is to omit the parentheses, for example in ~(!p). Then ML regards ! as the function's argument.

__8.4.__ According to the Definition of Standard ML, (E1;E2;...;En) translates to

```
case E1 of _ => case E2 of _ => ... case E(n-1) of _ => En.
```

Also while E1 do E2 goes to

```
    let fun newVar() = if E1 then (E2; newVar()) else ()
    in  newVar()  end;
```

where newVar is a new variable.

__8.5.__ This solution uses a while loop. The condition updates the loop variable, so the loop body is empty.

```
fun sqroot a = 
  let val xp  = ref 1.0
      and acc = 1.0E~10
  in  while let val x = !xp
            in  xp := (a/x + x) / 2.0;  
              		abs (x - !xp) >= acc*x
       	    end
      do  ();
      !xp
  end;
```

__8.6.__ This solution uses a function to swap the contents of two references; a simultaneous assignment operator could be used instead.

```
fun exchange(xp,yp) =
  let val x = !xp and y = !yp 
  in  xp:=y; yp:=x  end;

fun fib 0 = 0
  | fib n =
      let val xp = ref 0
          and yp = ref 1
          and kp = ref 1
      in  while !kp<n  
          do  (xp := !yp + !xp;  exchange(xp,yp);  kp := !kp+1);
          !yp
  end;
```

__8.7.__ The library function ListPair.app applies a function to the element of a list, for the side effects.

```
fun simasgt (ps, xs) = ListPair.app (op:=) (ps,xs);
```

__8.8.__ WI is an identity function and can be used precisely as if it were declared by

```
fun WI x = x;
```

It counts as polymorphic because fun abbreviates a use of val with fn notation, which is a syntactic value.

__8.9.__

* funs is legal, as [hd] is a syntactic value. (List notation counts as a constructor.)
* l is illegal. The right-hand side is polymorphic and not a syntactic value, since rev is not a constructor. But it is safe, since it does not really create references.
* l' is legal because the right-hand side is monomorphic.
* lp is both illegal and unsafe. If it were allowed, lp would be a ref cell of polymorphic type, which could take on one type when receiving assignments and a different type when yielding up its contents. (The right-hand side could be legal in a monomorphic context.)

__8.10.__ Here's one solution. In merge, take case not to call tl outside of a delay.

```
fun merge (xq,yq) : int ImpSeq.t = 
  let val x = ImpSeq.hd xq 
      and y = ImpSeq.hd yq
  in  if x=y then ImpSeq.cons(x, fn()=> merge(ImpSeq.tl xq, ImpSeq.tl yq))
      else if x<y then ImpSeq.cons(x, fn()=> merge(ImpSeq.tl xq, yq))
                  else ImpSeq.cons(y, fn()=> merge(xq, ImpSeq.tl yq))
  end;

fun times x y : int = x*y;
fun timesq (m: int) ns = ImpSeq.map (times m) ns;

val hamming = ImpSeq.cycle(fn hf =>
    ImpSeq.cons(1, fn()=> 
                merge(timesq 2 (hf()),
                      merge(timesq 3 (hf()), 
                            timesq 5 (hf())))));
```

If your solution exploits sharing properly, it should be able to evaluate the following expression instantly:

```
List.drop(ImpSeq.take(hamming,300), 280); 
```

__8.11.__ For more discussion see Bird & Wadler (1988), page 187. Here is a cyclic version:

```
fun cy_iterates f x = 
    ImpSeq.cycle(fn xf => ImpSeq.cons(x, fn()=> ImpSeq.map f (xf())));
```

It is much more efficient than the similar but non-cyclic version:

```
fun map_iterates f x = 
    ImpSeq.cons(x, fn()=> ImpSeq.map f (map_iterates f x));
```

__8.12.__ With ordinary lists, we ask whether a computation terminates. With infinite sequences, the most we can ask for is that the computation makes progress. If it does not, then the attempt to evaluate some element of the sequence may fail to terminate. (And when we have a sequence of sequences, the situation is more complicated still!) The sequence fib2 does not make progress because its second element depends -- via ImpSeq.tl(fibf()) -- upon itself!

There are proof methods, such as computation induction and coinduction, for reasoning about infinite data structures. In the special case of infinite sequences, you can also use ordinary list induction together with the take-lemma; see Bird & Wadler (1988), page 182.

__8.13.__

```
fun toList Nil = []
  | toList (Cons(x,xp)) = x :: toList (force xp);

fun fromList [] = Nil
  | fromList (x::xs) = cons(x, fn()=> fromList xs);

fun interleave (Nil,    yq) = yq
  | interleave (Cons(x,xp), yq) = 
     	Cons(x, delay (fn()=> interleave(yq, force xp)));

 fun concat xqq =
   if null xqq then empty
   else if null(hd xqq) then concat(tl xqq)
  	else cons(hd(hd xqq),  
	         	  fn()=> tl(hd xqq) @ concat(tl xqq));

fun filter pred Nil = Nil
  | filter pred (Cons(x,xp)) =
	    if pred x 
    	then Cons(x, delay(fn()=> filter pred (force xp)))
    	else filter pred (force xp);
```

__8.14.__ It is simplest just to put true or false in the corresponding branches of the conditional:

```
fun delete2 (Ptr p) =
    case !p of
       	Nil => raise Empty
      | Node(lp,x,rp) =>
	         if left(!lp) = lp then (p := Nil;  true)
	          else (right(!lp) := !rp;  left (!rp) := !lp;
		               p := !rp;  false)
```

__8.15.__ The equality !lp=!rp holds just if the left and right links point to equal nodes. It works but needlessly compares the node contents, which therefore would have to have an equality type.

The equality right(!lp)=lp holds if the right link of the node to the left equals the current left link. The equality right(!lp)=rp holds if the right link of the node to the left equals the current right link. These are both correct ways of testing that there is only one node.

In the code for delete, the equality p=lp is always false, as p is created by the function empty and is not equal to any link field.

__8.16.__ This version is wrong because it does not create new references for the new node. The left and right links will always be identical. It cannot make buffers of size greater than one.

__8.17.__ The modifications are straightforward:

```
  fun insert_right (Ptr p, x) =
      case !p of
      	  Nil => 
	            let val lp = ref Nil
		               and rp = ref Nil
	       	        val new = Node(lp,x,rp)
	            in  lp := new;  rp := new;  p := new  end
      	| Node(_,_,rp) =>
	            let val new = Node(ref(!p), x, ref(!rp))
	            in  left(!rp) := new;  rp := new  end;
```

__8.18.__ The following session could then occur, adding 1415 to "They":

```
val buf = Ringbuf.empty();
Ringbuf.insert(buf, "They");
1415 + Ringbuf.delete buf;
```

__8.19.__ Equality of ring buffers means that they denote the same object in the store -- not that they are separate data structures that happen to contain equal values.

__8.20.__ A naive solution would have the exponential behaviour of the Fibonacci function. This solution uses an array to store precomputed values for each possible amount. Given an amount it still depends upon what coins are available; the alternatives are stored in an association list.

This solution could undoubtedly be improved, but it solves the specified problem in 200 msec.

```
fun assoc ([], a) = []
  | assoc ((x,y)::pairs, a) =
      if a=x then  [y]  else  assoc(pairs, a);

fun countChange (coinvals, amount) =
 let val arr = Array.array (amount+1, [])
     fun countc (coinvals, 0)         = 1
       | countc ([],       amount)    = 0
       | countc (c::coinvals, amount) =
      	   if amount<0 then 0
      	   else case assoc (Array.sub(arr, amount), c::coinvals) of
	                 [cc] => cc
             	  | [] => 
                   		let val cc = countc(c::coinvals, amount-c) +
			                               countc(coinvals, amount)
	                   	in  Array.update(arr, amount,
                       				 (c::coinvals, cc)::Array.sub(arr, amount));
                   		    cc
                   		end
 in countc(coinvals, amount) end;
```

__8.21.__ Add the following line to signature VARRAY:

```
val fromList: 'a list -> 'a T
```

Add the following code to the structure. The list must be non-empty, as we need something to put into the dummy node.

```
fun fromList []          = raise Size
  | fromList (l as x::_) =
      Modif{limit=length l, index=ref 0, elem=ref x, 
	           next=ref(Main(Array.fromList l))};
```

__8.22.__ Add the following line to signature VARRAY:

```
val copy: 'a T -> 'a T
```

Add the following code to the structure. Note how arrayCopy copies the underlying array; otherwise they would be shared and the new copy would not be independent of the old. The other code simply copies the list structure and then reroots it. More efficient would be to accumulate a list of changes and apply them directly to the underlying array.

```
fun arrayCopy a = Array.tabulate(Array.length a, fn i => Array.sub(a,i));

fun justCopy (Main ary) = Main (arrayCopy ary)
  | justCopy (Modif{limit,index,elem,next}) = 
      Modif{limit = limit, 
	           index = ref (!index), 
	           elem  = ref (!elem), 
	           next  = ref (justCopy (!next))};

fun copy va = reroot(justCopy va);
```

__8.23.__ Here is a simple solution. Function array ensures that the subarrays are distinct copies. But it does not store the bounds explicitly, or even (for fromList) check that each subarray has the same length. So two versions of length are provided, one for the first dimension and one for the second.

```
signature ARRAY2 =
  sig
  type 'a array
  exception Subscript and Size
  val array: int * int * '_a -> '_a array
  val fromList: '_a list list -> '_a array
  val sub: 'a array * int * int -> 'a
  val update: 'a array * int * int * 'a -> unit
  val length: 'a array -> int
  val length2: 'a array * int -> int
  end;

structure Array2 : ARRAY2 =
  struct
  type 'a array = 'a Array.array Array.array;

  exception Subscript and Size;

  (*create a new m*n array.  Array.array(m, Array.array(n, x)) is wrong!*)
  fun array (m,n,x) = 
    	if m<0 orelse n<0  then  raise Size
    	else  Array.tabulate(m, fn i => Array.array(n,x));

  fun fromList ls = Array.fromList(map Array.fromList ls);

  fun sub(a, i, j) = Array.sub(Array.sub(a, i), j);

  fun update(a,i,j,x) = Array.update(Array.sub(a,i), j, x);

  val length = Array.length;

  fun length2(a,i) = Array.length(Array.sub(a, i));
  end;
```

__8.24.__ The solution is analogous to that of the previous exercise.

__8.25.__ As shown in the two diagrams on re-rooting, the node containing the most recent update becomes the dummy node. Most of the information is redundant and could (in another programming language) be suppressed to save storage. But the node's mutable link is essential.

__8.26.__

```
fun writeCheque w (dols,cents) = 
   String.concat
     ["$",
      StringCvt.padLeft #"*" (w-4) (Int.toString dols),
      ".",
      StringCvt.padLeft #"0" 2 (Int.toString cents)];
```

__8.27.__

```
val toUpper = String.translate (String.str o Char.toUpper);
```

__8.28.__ Function ssShow makes it easy to view the results returned by these expressions.

```
fun ssShow (SOME (x,ss)) = SOME (x, Substring.string ss)
  | ssShow NONE          = NONE;

ssShow (Bool.scan Substring.getc (Substring.full "mendacious"));
ssShow (Bool.scan Substring.getc (Substring.full "falsetto"));
ssShow (Real.scan Substring.getc (Substring.full "6.626x-34"));
ssShow (Int.scan StringCvt.DEC Substring.getc (Substring.full "1o24"));
```

__8.29.__

```
fun dateScan getc inp =
  let val intScan = Integer.scan StringCvt.DEC getc 
      val SOME (day,inp) = intScan inp
      val SOME (#"-",inp) = getc inp
      val (mon,inp) = StringCvt.splitl Char.isUpper getc inp
      val SOME (#"-",inp) = getc inp
      val SOME (year,inp) = intScan inp
  in  if List.exists (fn m => m=mon) months 
      then SOME ((day, mon, year), inp)
      else NONE
  end
  handle Bind => NONE;
```

__8.30.__ The counting function is entirely straightforward. Note the declaration of countWords, which counts the words in a string.

```
fun count_cwl is =
    let val lr = ref 0
       	and wr = ref 0
       	and cr = ref 0
        val countWords = length o String.tokens Char.isSpace
    in
      	while not (TextIO.endOfStream is) do
      	    let val s = TextIO.inputLine is
      	    in  cr := !cr + size s;
             		wr := !wr + countWords s;
               lr := !lr + 1
           end;
           (!lr, !wr, !cr)
    end;
```

__8.31.__

```
fun area r = Math.pi * r * r;

fun promptArea (is, os) =
  while (TextIO.output(os, "Radius? ");  TextIO.flushOut os;
	 not (TextIO.endOfStream is)) do
     TextIO.output(os, case Real.fromString (TextIO.inputLine is) of
		           SOME r => "Area = " ^ Real.toString (area r) ^ "\n"
			 | NONE   => "Invalid input, retry\n");
```

__8.32.__ In htmlCvt, replace TextIO.inputLine by transInputLine, defined below to read a line and translate special characters.

There is an error in this exercise: all the escape sequences require a terminating semicolon. For example &lt; stands for the < character.

```
fun htmlSpecial #"<" = "&lt;"
  | htmlSpecial #">" = "&gt;"
  | htmlSpecial #"&" = "&amp;"
  | htmlSpecial #"\"" = "&quot;"
  | htmlSpecial c    = String.str c;

val transHtmlSpecial = String.translate htmlSpecial;

val transInputLine = transHtmlSpecial o TextIO.inputLine;
```

__8.33.__ An example of the problem is

```
Pretty.pr (TextIO.stdOut, 
           prettyshow (Disj (Conj(Atom"very_rich_indeed", Atom"poor"),
                             Conj(Atom"rich", Atom"fine"))),
    25);
```

which generates the output

```
((very_rich_indeed &
  poor) | (rich & fine))
```

It associates poor with the second conjunction instead of the first. This could be misleading, especially in complicated expressions. It can be corrected by modifying function printing as follows: if a Block is printed over more than one line, force the next Break follow it to make a real line break. This change requires additional book-keeping but is worth doing.

__8.34.__ Here is a sketch of a solution. Declare a new constructor, say

```
BlockCon of T list * int * int
```

Add a boolean argument forcebreaks to printing. When printing a BlockCon, check whether

```
len + breakdist(es,after) <= !space
```

and if false, pass true for forcebreaks in the recursive call (other calls should make this argument false). When printing a Break, make a real line break if forcebreaks is true.

__8.35.__ There are no obvious practical advantages, but it may be useful to have the string as a value. This code is obtained by routine manipulation of the imperative version.

```
  fun toString (e, margin) =
   let fun blanks 0 = ""
         | blanks n = " " ^ blanks(n-1)

       fun prefix a (b,sp) = (a^b, sp)

       fun printing ([], _, _, sp) = ("", sp)
       	 | printing (e::es, blockspace, after, sp) =
	           (case e of
	                Block(bes,indent,len) =>
               		  let val (out, sp') =
	         	          printing(bes, sp-indent, breakdist(es,after), sp)
                   in  prefix out (printing (es, blockspace, after, sp'))
               		  end
         	     | String s => 
              		   prefix s (printing (es, blockspace, after, sp - size s))
	              | Break len => 
                		 if len + breakdist(es,after) <= sp 
                		 then prefix (blanks len)
		                        (printing (es, blockspace, after, sp - len))
                		 else prefix ("\n" ^ blanks(margin-blockspace))
                		      (printing (es, blockspace, after, blockspace)))
   in  #1 (printing([e], margin, 0, margin)) ^ "\n"  end;
```

__8.36.__ You would need a datatype with a constructor for each sort of format specification. For example, there might be a constructor Int_Fmt of int and Real_Fmt of int*int. Also you would need a datatype with a constructor for each type of data to be transmitted, simply to give them all the same type. For input, write an interpreter that takes a string and a list of format specifications, reads the string and returns a list of data items. Output would be done analogously.

This would, as in Fortran, allow formatted I/O for certain types fixed in advance. To allow the collection of types to be extended at any time, you could use type exn in its role as an extensible datatype, declaring new constructors (as exceptions) for new format specifications whenever desired. Some means of extending the system with new read/print routines would have to be worked out also.
