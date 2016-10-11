    Title: Poor man's dynamic dispatch with types in Shen
    Date: 2016-10-10T08:27:38
    Tags: shen, types, reflection

*DISCLAIMER: In this post I explore an interesting but ill-advised
use of Shen's type system. Nothing in it should be taken as an
indication of how to write good Shen.*

<!-- more -->

Historically, a lauded feature of Lisp is its extensive support for
runtime introspection. Common Lisp makes it easy to tease out
properties of programs as first class values, which is especially
useful when customizing the behavior of the language to a particular
problem domain. The venerable Common Lisp Object System (CLOS) is
renown in PL circles for its flexibility and dynamism -- its first
implementation was written entirely in the core Common Lisp language.

From the perspective of a language designer, the downside of extensive
introspection support is that makes it much harder to introduce ways
of expressing constraints on code into the language. In this post I
want to show how we can enable a fast, type-driven, mostly reliable
single dispatch mechanism in Shen.

## Property lists and effectful programming in the type checker

One feature Shen exhibits from its Lisp heritage is the property list,
or plist. A plist is a way of annotating data onto a symbol, which can
be associatively read and modified at that symbol, stored as a list of
key/value pairs. In chapter 24 of [Practical Common
Lisp](http://www.gigamonkeys.com/book/), Seibel uses plists to control
the expansion of a family of macros at compile time. Shen's property
lists can be annotated onto any Shen value, and are documented
[here](http://www.shenlanguage.org/learn-shen/property_lists.html).

We'll begin by providing a typed version of Common Lisp's `type-of`
function. To do this we'll exploit the fact that we have at our
disposal most (all?) of the Shen language from within the sequent
rules written in any `datatype` clause.

Since Shen is a Lisp, we also have the home advantage of
homoiconicity. This means we can intercept any datum put out by the
type checker -- itself a Shen value -- and do whatever we like with it
in the course of checking that a value inhabits a type.

So, while verifying that a value `X` inhabits a type `A`, we'll
annotate `X`'s property list with a representation of its type `A` at
the key type-rep. We'll reference the value of type-rep when we add
dynamic dispatch, but first we need to decide on a mode of
representation. For type-reps, we'll use Shen strings.

```
(define string-concat
  []  -> ""
  [S] -> S
  [S | Ss] -> (@s S " " (string-concat Ss)))

(define type->string  
  Xs  -> "()" where (empty? Xs)
  Xs  -> (@s "(" (string-concat (map type->string Xs)) ")") where (cons? Xs)
  Str -> (make-string "~A" Str))
```

A brief overview of the predicates in the `where` clauses: `empty?`
checks for an empty list, `cons?` for a non-empty list. `make-string`
writes a value to a string using the Fortran formatting notation for
strings.

`string-concat` is a simple utility function for concatenating a list
of strings together. Adding types, these functions become

```
(define string-concat
  { (list string) --> string }
  []  -> ""
  [S] -> S
  [S | Ss] -> (@s S " " (string-concat Ss)))

(define type->string
  { A --> string }	
  Xs  -> "()" where (empty? Xs)
  Xs  -> (@s "(" (string-concat (map type->string Xs)) ")") where (cons? Xs)
  Str -> (make-string "~A" Str))
```

To support the polymorphism of `type->string`, we add a verified type
on `cons?`. For any `where Property` clause, Shen automatically
introduces the axiom `Property : verified` into the type theory, which
a Shen programmer can exploit to type values on a case-driven basis.

Having verified that `(cons? Xs)` returns true, we want the type
checker to deduce that `Xs` is a non-empty homogeneous list of values
with type `A`. This is done in the rule

```
(datatype verified-types-for-cons
  _______________________________________
  (cons? Xs) : verified >> Xs : (list A);)
```

The type theory for type-reps is as follows.

```
(datatype type-reps
  ______________________________________________
  X : (type-rep A) >> (get X type-rep) : string;

  let Tag (put (eval X) type-rep (type->string A))
  ________________________________________________
  (tag-value-with-rep X A);

  X : A; (tag-value-with-rep X A);
  ________________________________
  X : (mode (type-rep A) -);)
```

We'll run down the rules from the top. We consider that any value `X` of
type `A` represents the type of `A`; the type `(type-rep A)` is nothing
other than the type `A`.

The first rule says that if the value `X` represents `A`, it is annotated
with the representation of `A` at the key type-rep in its plist, a
string.

The second rule does the work of annotating the plist with the string
representation of `A` at the key type-rep. Shen values get mangled
slightly in the type checker, but the mangling can be overcome using
the `eval` function.

The third and final rule checks that `X` is of type `A` before firing
the clause that annotates the plist of `X` appropriately. The `mode
... -` wrapper is there to prevent the type checker from entering an
infinite loop upon encountering some of the more complicated
(ie. polymorphic) types native to Shen.

We are finally ready to give the definition of `type-of`.

```
(define type-of
  { (type-rep A) --> string }
  X -> (get X type-rep))
```

And that's it. All the heavy lifting is done in the type checker. We
can test the operation of `type-of` on values of various types.

```
(36+) (type-of 3)
"number" : string

(37+) (type-of "a string")
"string" : string

(38+) (type-of false)
"boolean" : string

(39+) (type-of (@p 3 false [1 2 3] (@v (@v symbols are present <>) <>)))
"(number * (boolean * ((list number) * (vector (vector symbol)))))" : string

(40+) (type-of str)
"(Var17 --> string)" : string
```

The function `str` has the polymorphic type `(A --> string)`, but here
a skolemized variable `Var17` is leaked out of the type
checker. Obviously this poses a serious caveat to dynamic dispatch on
polymorphic types. We should be more careful in defining
`type->string` after deciding on a format for polymorphic type
representation. This seems a job for the (Shen and human) reader and
Shen Prolog.

## Generic type verification

What we've developed is a semi-elegant way of implementing generic
verified types. Remember that we had to introduce a special rule for
verifying homogeneous lists in `where` clauses. If we have to do the
same for every type we might want to verify in the future, we will
quickly overburden the type checker with many ad hoc rules.

Fortunately, we can leverage `type-of` to avoid that, at least when
dealing with non-polymorphic types.

```
(define has-type?
  { (type-rep A) --> string --> boolean }
  X Type -> (= (type-of X) Type))

(datatype generic-verification
  if (= (type->string A) Str)
  ______________________________________
  (has-type? X Str) : verified >> X : A;)
```

`has-type?` checks that `X` has the type described in the string, by
extracting its type representation from `type-of`. The rule in
`generic-verification` proves that `X` has type `A` by appealing to
the truth of `has-type?` on `X` and its purported representation
`Str`.

Now we have type verification "for free", at least on arbitrary
concrete types, as demonstrated in the stupid and useless function
`arbitrary-messages`.

```
(define arbitrary-messages
  { (type-rep A) --> string }
  X -> (let Y (+ X X) (str Y)) where (has-type? X "number")
  X -> (let Y (@s X X X) Y) where (has-type? X "string")
  X -> (@s "passed a " (type-of X)))
```

Note that `X` is being typed as a number, as a string, etc. in each of
the adjoining clauses, and is treated accordingly. What we've created
is essentially a limited but type safe version of Common Lisp's
`typecase` macro, without delving into macrology.

# Opportunities and Shortcomings

We've mentioned the difficulty in dealing with polymorphic types, but
another major shortcoming is that Shen's type system is simply too
powerful for this mechanism to work well across all applications. Shen
places no restrictions on the number of types or the relations among
types that any value may belong to.

On the bright side, a technique like this could serve as the basis for
some form of automatic type-driven single dispatch; think Haskell's
typeclasses.

# Source code

... is available
[here](https://gist.github.com/mthom/42878af3bf0d51274a2459faac2edaf2).