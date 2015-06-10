    Title: Shen Kata #1: Type-safe reference cells
    Date: 2015-06-08T19:38:12
    Tags: shen, currying, reference cells, types, vectors

Unlike many other eager, statically typed functional languages that
emphasize computing with immutable values, Shen lacks native support
for reference cells. Let's add our own.

<!-- more -->

## First-class, locally scoped mutable values

We can think of a reference cell as a box containing a
pointer to a value of any initial type. In ML family languages,
reference cells are associated to interfaces similar to that of the
Standard ML signature

```
signature REF =
sig 
  type 'a ref
  val ref : 'a -> 'a ref
  val writeref : 'a ref -> 'a -> ()
  val readref : 'a ref -> 'a
end
```

`'a ref` is the type of a reference cell, where the ML type `'a` is
the type of its contents. `ref` creates a reference cell containing
its parameter value, `writeref` replaces the contents of a reference
cell with a value of the annotated type of that cell, and `readref`
extracts the contents of a cell.

A write made to a reference cell is propagated to all other data
structures containing that cell, which is itself an immutable value.
In that sense, reference cells are first-class, locally scoped mutable
values of the sort we're accustomed to using in imperative languages.

As in imperative languages, they require a kind of temporal reasoning
that is safely neglected when dealing only with immutable values,
which is one of the stronger selling points of purely functional
languages.

Why bother with reference cells then? At times, the use of mutation
can't be avoided, usually for the sake of efficiency. Some data
structures lack fast, purely functional implementations. Others are
self-referential and can't otherwise be implemented without resorting
to laziness, which comes with its own pitfalls and limitations.

## Shen lacks reference cells

If Shen provided reference cells natively, there would be no reason to
add our own. Any candidate for an ad-hoc reference cell in
Shen would have to support mutation already. Shen provides mutable
values in two principal ways, through vectors and through global
assignments.

Global assignments are not locally scoped, since they're accessible
from anywhere in a Shen program if the name of the assignment is
known.

Shen vectors are first-class, mutable, homogenous containers with a
native type theory in line with what we want for ref types, apeing the
example of ML. Vectors have the additional property that they may be
grown and shrunk an element at a time from the head. In contrast, a
reference cell must refer to a single location in memory that persists
with the cell, which is to say that an unfettered vector
representation allows the programmer to violate core
semantic assumptions behind the creation and use of reference cells.

## A Shen implementation

This suggests we should start with vectors as a data representation,
and constrain them somehow. One approach is to close two functions
over a single cell vector containing an initial value of type
`A`. This prevents the user of the reference cell from accessing the
internal vector representation by any means other than that afforded
by the two functions, which we will implement as a getter/setter
pair. Following the types in the ML signature, we obtain type
signatures for these functions,

the getter, `ref-reader : (one-cell-vector A) --> (lazy A)`

and the setter, `ref-writer : (one-cell-vector A) --> A --> unit`.

`ref-reader`, given a one-cell vector, returns a value of type `(lazy
A)`, whose semantics are identical to a function that takes no
arguments.

`ref-writer` writes a value of type `A` to a one-cell vector.

Natively, Shen has a vector type `(vector A)`, which types a vector
of elements of type `A`. We have to define the `(one-cell-vector A)`
type ourselves, which we do using the sequent rules

```
 (datatype one-cell-vector
   X : A;
   ________________________________
   (@v X <>) : (one-cell-vector A);

   __________________________________________
   V : (one-cell-vector A) >> V : (vector A);)
```
   
Here we give two rules of inference.  The first says that a Shen
expression matching the template `(@v X <>)` can be inferred to be of
type `(one-cell-vector A)` if the subexpression `X` can be inferred to
be of type `A`, where `A` is a type variable and hence may be
substituted for any Shen type (type symbols titled in lower case name
concrete types).

The second rule is subtly different. It says that, if it has been
proven that a Shen expression `V` is of type `(one-cell-vector A)`,
(really, `V` is a template that may be substituted for any Shen
expression), then `V` has the type `(vector A)`.

These rules stringently constrain the number of ways in which we can
generate elements of `(one-cell-vector A)`. Either we've called a
type-checked function that returns a value of that type, or we've
generated one directly using the `(@v X <>)` template, where `X` is an
expression producing a value of type `A`. We could easily enrich
the type theory to allow other semantically valid ways of generating
one cell vectors, but for our purposes these rules suffice.

The unit type is pre-defined in Shen, and is uninhabited
(no values have the type unit by default). We add our own.

```
(datatype unit-type
 __________
 [] : unit;)
```

Equipped with the necessary types, we define the `ref-reader` and
`ref-writer` functions.

```
(define ref-reader
  { (one-cell-vector A) --> (lazy A) } 
  R -> (freeze (<-vector R 1)))

(define ref-writer
  { (one-cell-vector A) --> A --> unit }
  R X -> (do (vector-> R 1 X) []))
```

`ref-reader` suspends ("freezes") a computation on a one cell vector
`R`, which reads the value of that cell whenever the computation is
thawed (Shen vectors are 1-indexed).

`ref-writer` sequences two expressions in a `do` form. The first
writes the value `X` to the cell of `R`, the second evaluates to unit.

We now implement `ref`, again in keeping with the type given in the ML
signature.

```
(define ref
   { A --> (ref A) }
   X -> (let V (@v X <>)
	  (@p (ref-reader V) (ref-writer V))))
```

In Shen, all functions are curried by default, so that the function
`(ref-writer V)` has type `A --> unit`. `(ref A)` is defined in the
datatype

```
(datatype ref-types
   V : (one-cell-vector A);
   _____________________________________________
   (@p (ref-reader V) (ref-writer V)) : (ref A);

   _____________________________________________
   R : (ref A) >> R : ((lazy A) * (A --> unit));)
```

Since in the context of the definition of `ref`, we can prove that the
expression bound to `V` is a one-cell vector, it follows by the first
rule that the ordered pair `(@p (ref-reader V) (ref-writer V))`
inhabits the type `(ref A)`.

The second rule says that a value `R` known to be of type `(ref A)` is
an ordered pair in which the first element has type `(lazy A)` and the
second type `(A --> unit)`.

And that is all. The type rules guarantee that any value proved to be
of type `(ref A)` is an ordered pair of the reader and writer types,
closing over a common one-cell vector, where the reader and writer
functions are generated using the `ref-reader` and `ref-writer`
functions. The absence of rules qualifying values of `(ref A)` in any
other way cause any other attempts to type values as `(ref A)` to fail.

It is now easy to define the Shen versions of the `readref` and
`writeref` functions.

```
(define <-r
   { (ref A) --> A }
   R -> (thaw (fst R)))

(define r->
   { (ref A) --> A --> unit }
   R X -> ((snd R) X))
```
   
The functions `fst` and `snd` project onto the first and second
elements of an ordered pair respectively.

The complete Shen source for the exercise is
[here](https://github.com/mthom/shen-reference-cells/blob/master/ref-cells.shen).

## Example: block-scanner

As an example of reference cells, we adapt the text block scanner
closure from Doug Hoyte's book,
[Let Over Lambda](http://letoverlambda.com/index.cl/guest/chap2.html#sec_6).

```
(define char-scanner
  { string --> (ref string) --> string --> unit }
  Trig Curr (@s C Str) -> (char-scanner Trig Curr Str) where (= (<-r Curr) "")
  Trig Curr (@s C Str) -> (do (r-> Curr (if (= (hdstr (<-r Curr)) C)
					       (tlstr (<-r Curr))
					       Trig))
			      (char-scanner Trig Curr Str))
  Trig Curr "" -> [])

(define block-scanner
  { string --> string --> boolean }
  Trig -> (let Curr (ref Trig)
	    (/. DataString
			(do (char-scanner Trig Curr DataString)
				(= (<-r Curr) "")))))

(set *scanner* (block-scanner "jihad"))

((value *scanner*) "we will start ")
((value *scanner*) "the ji")
((value *scanner*) "had tomorrow.")
```
