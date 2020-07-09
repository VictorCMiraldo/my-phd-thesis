  The syntax of many programming languages is expressed through a mutually
recursive family of datatypes. Before writing a generic differencing
algorithm we need to be able to program generically over mutually
recursive families of datatypes. Consider Haskell itself, a |do| block constructs
an expression, even though the |do| block itself is
composed by a list of statements which may include expressions.

\begin{myhs}
\begin{code}
data Expr  = ... | Do [Stmt] | ...
data Stmt  = Assign Var Expr | Let Var Expr
\end{code}
\end{myhs}

  Another example is found in \texttt{HTML} and \texttt{XML} documents.
These are easily described by a Rose tree, which albeit
being a nested type \cite{Bird1998}, is naturally encoded
in the mutually recursive family of datatypes below.

\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

  The mutual recursion becomes apparent once one instantiates |a| to some
ground type, for instance:

\begin{myhs}
\begin{code}
data RoseI  =  Fork Int ListI
data ListI  =  Nil | RoseI : ListI
\end{code}
\end{myhs}

  Working with generic mutually recursive families in Haskell, however, is a
non-trivial task.  The best solution at the time of writing is the
\texttt{multirec}~\cite{Yakushev2009} library, which is unfortunately
unfit for writing complex programs -- the lack of a combinator-based approach
to generic programming and the pattern functor
(\Cref{sec:background:patternfunctors}) approach makes it hard
to write involved algorithms.

  This meant we had to engineer new generic programming libraries to
tackle the added complexity of mutual recursion. We have devised two
different ways of doing so. First, we wrote the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, which combines a
combinator based (\Cref{sec:background:explicitsop}) approach to
generic programming with mutually recursive types. In fact,
\texttt{generics-mrsop} lies in the intersection of \texttt{multirec}
and the more modern \texttt{generics-sop}~\cite{deVries2014}.  It is
worth noting that neither of the aforementioned libraries
\emph{compete} with our work. We extend both in orthogonal directions,
resulting in a new design altogether, that takes advantage of some
modern Haskell extensions which the authors of the previous work could
not employ.

  The \texttt{generics-mrsop} library, \Cref{sec:gp:mrsop}, was a
conceptual success. It enabled us to prototype and tweak the
algorithms discussed in \Cref{chap:structural-patches} and
\Cref{chap:pattern-expression-patches} with ease. Yet, a memory leak
in the Glasgow Haskell Compiler\footnote{
\url{https://gitlab.haskell.org/ghc/ghc/issues/17223} and
\url{https://gitlab.haskell.org/ghc/ghc/issues/14987}}
made it unusable for encoding real programming languages
such as those in the \texttt{language-python} or \texttt{language-java}
packages. This frustrating outcome meant that a different approach --
which did not rely as heavily on type families -- was necessary
to look at real-world software version control conflict data.

  It turns out that we can sacrifice the sums-of-products
structure of \texttt{generics-mrsop}, significantly decreasing
the reliance of type families, while maintaining a combinator-based
approach. This would still enables us to write the algorithms underlying
the \texttt{hdiff} tool (\Cref{chap:pattern-expression-patches}).
This lead us to develop the \genericssimpl{} library, \Cref{sec:gp:simplistic},
that still maintains a list of the types that belong in the family,
but does not record their internal sum-of-products structure.

  This chapter, then, is concerned with explaining our work
extending the existing generic programming capabilities of Haskell to
support mutually recursive types. We introduce two conceptually different approaches,
but with similar expressivity.
In \Cref{sec:gp:mrsop} we explore the \texttt{generics-mrsop}
library. With its ability of representing explicit sums of products
we are able to illustrate the \texttt{gdiff}~\cite{Lempsink2009} differencing
algorithm, which follows the classical tree-edit distance but in a typed fashion.
Then, in \Cref{sec:gp:simplistic}, we explore the \genericssimpl{} library, which
works on the pattern functor spectrum of generic programming.

\section{The \texttt{generics-mrsop} library}
\label{sec:gp:mrsop}

  The \texttt{generics-mrsop} library is an intersection of the
\texttt{multirec} and \texttt{generics-sop} libraries. It uses
explicit codes in the sums of products style to guide the
representation of datatypes. This enables a simple explicit fixpoint
construction and a variety of recursion schemes, which makes the
development of generic programs fairly straightforward.

\subsection{Explicit Fixpoints with Codes}
\label{sec:gp:explicitfix}

  Introducing information about the recursive positions in a type
requires more expressive codes than in \Cref{sec:background:explicitsop}.
Where our \emph{codes} were a list of lists of types, which could be
anything, we now have a list of lists of |Atom|, which maintains
information about whether a position is recursive or not.

\begin{myhs}
\begin{code}
data Atom = I | KInt | dots

type family    CodeFix (a :: Star)   ::  P [ P [Atom] ]

type instance  CodeFix (Bin Int)  =   P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

  Here, |I| is used to mark the recursive positions and |KInt, dots|
are codes for a predetermined selection of primitive types, which we
refer to as \emph{opaque types}.
Favoring the simplicity of the presentation, we will stick with only
hard coded |Int| as the only opaque type in the universe. Later on,
in \Cref{sec:gp:konparameter}, we parameterize the whole development
by the choice of opaque types.

  We can no longer represent polymorphic types in this universe -- the
\emph{codes} themselves are not polymorphic.  Back in
\Cref{sec:background:explicitsop} we have defined |CodeSOP (Bin a)|,
and this would work for any |a|. The lack of
polymorphism might seem like a disadvantage
at first, but if we are interested in deep generic representations, it
is actually an advantage, as it allows us to have a deep conversion for
free as we do not need to carry |Generic| constraints around. That is,
say we want to deeply convert a value of type |Bin a| to its generic
representation polymorphically on |a|.  We can only do so if we have
access to the |CodeSOP a|, which comes from knowing |Generic a|.  By
specifying the types involved beforehand, we are able to get by
without having to carry all of the constraints we needed in, for
instance, |gsize| at the end of \Cref{sec:background:explicitsop}.
The main benefit is in the simplicity of combinators we will
define in \Cref{sec:gp:combinators}.

  The |RepFix| datatype is similar to the |RepSOP|, but uses an additional
layer that maps an |Atom| into |Star|, denoted |NA|.
Since an atom can be either an opaque type, known statically, or some
type that must be placed in a recursive position later on, we need just
one parameter in |NA|.

\begin{myhs}
\begin{code}
data NA :: Star -> Atom -> Star where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt

newtype  RepFix a x = Rep { unRep :: NS (NP (NA x)) (CodeFix a) }
\end{code}
\end{myhs}

  The |GenericFix| typeclass, below, witnesses the isomorphism between
ordinary types and their deep sums-of-products representation.
Similarly to the other generic typeclasses out there, it contains just
the familiar |toFix| and |fromFix| components. We illustrate part of
the instance that witnesses that |Bin Int| has a generic
representation below.  We omit the |toFix| function as it is the
opposite of |fromFix|.

\begin{myhs}
\begin{code}
class GenericFix a where
  fromFix  :: a -> RepFix a a
  toFix    :: RepFix a a -> a

instance GenericFix (Bin Int) where
  fromFix (Leaf x)   = Rep (         Here  (NA_K x  :* NP0))
  fromFix (Bin l r)  = Rep (There (  Here  (NA_I l  :* NA_I r :* NP0)))
\end{code}
\end{myhs}

  It is an interesting exercise to implement the |Functor| instance
for |(RepFix a)| -- where it can be seen that we were only able to
lift it to a functor by recording the information about the recursive
positions. Otherwise, there would be no easy way of knowing where to apply |f|
when defining |fmap f|.

  Nevertheless, working directly with |RepFix| is hard -- we need to
pattern match on |There| and |Here|, whereas we actually want to have
the notion of \emph{constructor} for the generic setting too!  The
main advantage of the \emph{sum-of-products} structure is to allow a
user to pattern match on generic representations just like they would
on values of the original type, contrasting with
\texttt{GHC.Generics}. One can precisely state that a value of a
representation is composed by a choice of constructor and its
respective product of fields by the |View| type. This \emph{view}
pattern~\cite{Wadler1987,McBride2004} is common in dependently typed programming.

\begin{myhs}
\begin{code}
data Nat = Z | S Nat

data View :: [[ Atom ]] -> Star -> Star where
  Tag  ::  Constr n t -> NP (NA x) (Lkup t n) ->  View t x
\end{code}
\end{myhs}

\noindent A value of |Constr n sum| is a proof that |n| is a
valid constructor for |sum|,
stating that |n < length sum|. |Lkup| performs list lookup at the type-level.
To improve type error messages, we generate a |TypeError| whenever we
reach a given index |n| that is out of bounds. Interestingly, our design
guarantees that this case is never reached by |Constr|.

\begin{myhs}
\begin{code}
data Constr :: Nat -> [k] -> Star where
  CZ  ::                  Constr Z      (x : xs)
  CS  :: Constr n xs  ->  Constr (S n)  (x : xs)

type family Lkup (ls :: [k]) (n :: Nat) :: k where
  Lkup (P [])    _          = TypeError "Index out of bounds"
  Lkup (x : xs)  (P Z)      = x
  Lkup (x : xs)  ((P S) n)  = Lkup xs n
\end{code}
\end{myhs}

  With the help of |sop| and |inj|, declared below, we are
able to pattern match and inject into generic values.
Unfortunately, matching on |Tag| directly can be cumbersome,
but we can always use pattern synonyms~\cite{Pickering2016} to circumvent that.
For example, the synonyms below describe the constructors |Bin| and |Leaf|.

\begin{myhs}
\begin{code}
pattern (Pat Leaf)  x    = Tag CZ       (NA_K x :* NP0)
pattern (Pat Bin)   l r  = Tag (CS CZ)  (NA_I l :* NA_I r :* NP0)

inj  :: View    sop  x  -> RepFix  sop   x
sop  :: RepFix  sop  x  -> View    sop   x
\end{code}
\end{myhs}

  Having the core of the \emph{sums-of-products} universe defined,
we can turn our attention to writing the combinators that the programmer
will use. These will naturally be defined by induction on the |CodeFix| instead of
having to rely on instances, like in \Cref{sec:background:patternfunctors}.
For instance, let us look at |compos|, which applies a function |f| everywhere
on the recursive structure.

\begin{myhs}
\begin{code}
compos :: (GenericFix a) => (a -> a) -> a -> a
compos f = toFix . fmap f . fromFix
\end{code}
\end{myhs}

  Although more interesting in the mutually recursive setting,
\Cref{sec:gp:family}, we can illustrate its use for traversing a
tree and adding one to its leaves. This example is a bit convoluted,
since one could get the same result by simply writing
|fmap (+1) :: Bin Int -> Bin Int|, but shows the intended usage
of the |compos| combinator just defined.

\begin{myhs}
\begin{code}
example :: Bin Int -> Bin Int
example (Leaf n)  = Leaf (n + 1)
example x         = compos example x
\end{code}
\end{myhs}

  It is worth noting the \emph{catch-all} case, allowing one to
focus only on the interesting patterns and using a default implementation
everywhere else, which is convenient when the datatypes in question
are large and might change often.

\paragraph{Converting to a deep representation.}  The |fromFix|
function still returns a shallow representation. But by constructing the
least fixpoint of |RepFix a| we can easily obtain the
deep encoding for free, by
recursively translating each layer of the shallow encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (GenericFix a) => a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . fromFix
\end{code}
\end{myhs}

  So far, we handle the same class of types as the
\texttt{regular}~\cite{Noort2008} library, but we require the
representation to follow a sums of products structure by the
means of |CodeFix|. Those types are guaranteed to have an initial
algebra, and indeed, the generic catamorphism is defined as expected:

\begin{myhs}
\begin{code}
fold :: (RepFix a b -> b) -> Fix (RepFix a) -> b
fold f = f . fmap (fold f) . unFix
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
crush :: (GenericFix a) => (forall x dot Int -> b) -> ([b] -> b) ->  a -> b
crush k cat = crushFix . deepFrom
  where  crushFix :: Fix (RepFix a) -> b
         crushFix = cat . elimNS (elimNP go) . unFix

         go (NA_I x) = crushFix x
         go (NA_K i) = k i
\end{code}
\end{myhs}
\caption{Generic |crush| combinator.}
\label{fig:gp:crush}
\end{figure}

  Some functions may consume a value and produce
a single value, but do not need the full expressivity of |fold|.
Instead, if we know how to consume the opaque types and combine
those results, we can consume any |GenericFix| type using |crush|,
which is defined in \Cref{fig:gp:crush}. The behavior of |crush|
is defined by (1) how to turn atoms into the output
type |b| -- in this case we only have integer atoms, and thus
we require an |Int -> b| function -- and (2) how to combine
the values bubbling up from each member of a product.

  Finally, we come full circle to our running |gsize| example
as it was promised in the introduction. This is noticeably the smallest
implementation so far, and very straight to the point.

\begin{myhs}
\begin{code}
gsize :: (GenericFix a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  At this point we have combined the insight from the \texttt{regular}
library of keeping track of recursive positions with the convenience
of the \texttt{generics-sop} for enforcing a specific \emph{normal
form} on representations. By doing so, we were able to provide a deep
encoding for free. This essentially frees us from the burden of
maintaining constraints. Compare the |gsize| above with its
\texttt{generics-sop} variation, in
\Cref{fig:background:generics-sop:gsize}.  The information about the
recursive position allows us to write neat combinators like |crush|
and |compos| together with a convenient |View| type for easy generic
pattern matching. The only thing keeping us from handling real life
applications is the limited form of recursion.

\subsection{Mutual Recursion}
\label{sec:gp:family}

  Conceptually, going from regular types (\Cref{sec:gp:explicitfix})
to mutually recursive families is simple. We just need to
reference not only one type variable, but one for each element in the
family.  This is usually~\cite{Loh2011,Altenkirch2015} done by adding
an index to the recursive positions to represents each member of
the family.  As a running example, we use the
familiar \emph{rose tree} family.

\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

  The previously introduced |CodeFix|, \Cref{sec:gp:explicitfix}, is
not expressive enough to describe this datatype. In particular, when
we try to write |CodeFix (Rose Int)|, there is no immediately
recursive appearance of |Rose| itself, so we cannot use the atom |I|
in that position. Furthermore |[Rose a]| is not an opaque type either,
so we cannot use any of the other combinators provided by |Atom|. We
would like to record information about |Rose Int| referring to
itself via another datatype.

  Our solution is to move from codes of datatypes to \emph{codes for
families of datatypes}. We no longer talk about |CodeFix (Rose Int)|
or |CodeFix [Rose Int]| in isolation. Codes only make sense within a
family, that is, a list of types. Hence, we talk about the codes of
the two types in the family: |CodeMRec (P [Rose Int, [Rose Int]])|.
Then we extend the language of |Atom|s by appending to |I| a natural
number which specifies the member of the family to recurse into:

\begin{myhs}
\begin{code}
data Atom  = I Nat | KInt | dots
\end{code}
\end{myhs}

The code of this recursive family of datatypes can be described as:

\begin{myhs}
\begin{code}
type FamRose           = P [Rose Int, [Rose Int]]

type CodeMRec FamRose  = (P  [ (P [ (P [ KInt, I (S Z)])])
                             , (P [ (P []), P [ I Z, I (S Z)]])
                             ])
\end{code}
\end{myhs}

  Let us have a closer look at the code for |Rose Int|, which appears in
the first place in the list. There is only one constructor which has
an |Int| field, represented by |KInt|, and another in which we recurse
via the second member of our family (since lists are 0-indexed, we
represent this by |S Z|). Similarly, the second constructor of |[Rose
Int]| points back to both |Rose Int| using |I Z| and to |[Rose Int]|
itself via |I (S Z)|.

  Having settled on the definition of |Atom|, we now need to adapt
|NA| to the new |Atom|s. To interpret any |Atom| into |Star|,
we need a way assign values to the different recursive positions. This
information is given by an additional type parameter |phi| that maps
natural numbers into types.

\begin{myhs}
\begin{code}
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I  :: phi n  -> NA phi (I n)
  NA_K  :: Int    -> NA phi KInt
\end{code}
\end{myhs}

This additional |phi| naturally bubbles up to |RepMRec|.

\begin{myhs}
\begin{code}
type RepMRec (phi :: Nat -> Star) (c :: [[Atom]]) = NS (NP (NA phi)) c
\end{code}
\end{myhs}

The only piece missing here is tying the recursive knot. If we want
our representation to describe a family of datatypes, the obvious
choice for |phi n| is to look up the type at index |n| in
|FamRose|. In fact, we are simply performing a type-level lookup in
the family, so we can reuse the |Lkup| from \Cref{sec:gp:explicitfix}.

In principle, this is enough to provide a ground representation for
the family of types. Let |fam| be a family of types, like |(P [Rose
Int, [Rose Int]])|, and |codes| the corresponding list of codes. Then
the representation of the type at index |ix| in the list |fam| is
given by:

\begin{myhs}
\begin{code}
RepMRec (Lkup fam) (Lkup codes ix)
\end{code}
\end{myhs}

This definition states that to obtain the representation of the type
at index |ix|, we first lookup its code. Then, in the recursive
positions we interpret each |I n| by looking up the type at that index
in the original family. This gives us a \emph{shallow}
representation.

Unfortunately, Haskell only allows saturated, that is, fully-applied
type families. Hence, we cannot partially apply |Lkup| like we did it
in the example above.  As a result, we need to introduce an
intermediate datatype |El|,

\begin{myhs}
\begin{code}
data El :: [Star] -> Nat -> Star where
  El :: Lkup fam ix -> El fam ix
\end{code}
\end{myhs}

The representation of the family |fam| at index |ix| is thus given in
terms of |El|, which can be partially applied, |RepMRec (El fam) (Lkup
codes ix)|. We only need to use |El| in the first argument, because
that is the position in which we require partial application.  The
second position has |Lkup| already fully-applied, and can stay as is.

  We still have to relate a family of types to their respective codes.
As in other generic programming approaches, we want to make their
relation explicit. The |Family| typeclass below realizes this
relation, and introduces functions to perform the conversion between
our representation and the actual types. Using |El| here spares us
from using a proxy for |fam| in |fromMRec| and |toMRec|:

\begin{myhs}
\begin{code}
class Family (fam :: [Star]) (codes :: [[[Atom]]]) where
  fromMRec  ::  SNat ix -> El fam ix -> RepMRec (El fam) (Lkup codes ix)
  toMRec    ::  SNat ix -> RepMRec (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}

  One of the differences between other approaches and ours is that we do
not use an associated type to define the |codes| for the family
|fam|. One of the reasons to choose this path is that it alleviates
the burden of writing the longer |CodeMRec fam| every time we want to
refer to |codes|. Furthermore, there are types like lists which appear
in many different families, and in that case it makes sense to speak
about a relation instead of a function.

Since now |fromMRec| and |toMRec| operate on families, we have to
specify how to translate \emph{each} of the members of the family
\emph{to} and \emph{from} their generic representation.
This translation needs to know
the index of the datatype we are converting between in each
case, hence the additional singleton |SNat ix| parameter. Pattern matching on
this singleton~\cite{Eisenberg2012} type informs the compiler about
the shape of the |Nat| index. Its definition is:

\begin{myhs}
\begin{code}
data SNat (n :: Nat) where
  SZ  ::              SNat (P Z)
  SS  ::  SNat n  ->  SNat ((P S) n)
\end{code}
\end{myhs}

  This, in turn, enables us to write the definition of |fromMRec| for
the family of rose trees.

\begin{myhs}
\begin{code}
-- First type in the family
fromMRec SZ       (El (Fork x ch))  = Rep (Here (NA_K x :* NA_I ch :* NP0))
-- Second type in the family
fromMRec (SS SZ)  (El [])           = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))     = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
\end{code}
\end{myhs}

  By pattern matching on the index, the compiler knows which family
member to expect as a second argument. This then allows the pattern
matching on the |El| to typecheck.

The limitations of the Haskell type system lead us to introduce |El|
as an intermediate datatype. Our |fromMRec| function does not take a
member of the family directly, but an |El|-wrapped one. However, to
construct that value, |El| needs to know its parameters, which amounts
to knowing the family we are embedding our type into and the index in that
family. Those values are not immediately obvious, but we can use
Haskell's visible type application~\cite{EisenbergWA16} to work around
it. The |into| function injects a value into the corresponding |El|:

\begin{myhs}
\begin{code}
into  :: forall fam ty ix dot (ix ~ Idx ty fam , Lkup fam ix ~ ty) => ty -> El fam ix
into  = El

intoRose :: Rose Int -> El FamRose (P Z)
intoRose = into (TApp FamRose)
\end{code}
\end{myhs}


  |Idx|, here, is a closed type family implementing the inverse of
|Lkup|, that is, obtaining the index of the type |ty| in the list
|fam|. Using this function we can turn a |[Rose Int]| into its generic
representation by writing |fromMRec . into (TApp FamRose)|. The type
application |(TApp FamRose)| is responsible for fixing the mutually
recursive family we are working with, which allows the type checker to
reduce all the constraints and happily inject the element into |El|.

\paragraph{Deep representation.} In \Cref{sec:gp:explicitfix} we have
described a technique to derive deep representations from shallow
representations. We can play a very similar trick here. The main
difference is the definition of the least fixpoint combinator, which
receives an extra parameter of kind |Nat| indicating which |code| to
use first:

\begin{myhs}
\begin{code}
newtype Fix (codes :: [[[Atom]]]) (ix :: Nat)
  = Fix { unFix :: RepMRec (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

Intuitively, since now we can recurse on different positions, we need
to keep track of the representations for all those positions in the
type. This is the job of the |codes| argument. Furthermore, our |Fix|
does not represent a single datatype, but rather the \emph{whole}
family. Thus, we need each value to have an additional index to
declare on which element of the family it operates.

As in the previous section, we can obtain the deep representation by
iteratively applying the shallow representation. Earlier we used
|fmap| since the |RepFix| type was a functor. |RepMRec| on the other
hand cannot be given a |Functor| instance, but we can still define a
similar function |mapRec|,

\begin{myhs}
\begin{code}
mapRep  ::  (forall ix dot phi1 ix -> phi2 ix) ->  RepMRec phi1 c -> RepMRec phi2 c
\end{code}
\end{myhs}

This signature tells us that if we want to change the |phi1| argument in
the representation, we need to provide a natural transformation from
|phi1| to |phi2|, that is, a function which works over each
possible index this |phi1| can take and does not change this index.
This follows from |phi1| having kind |Nat -> Star|.

\begin{myhs}
\begin{code}
deepFrom  ::  Family fam codes =>  El fam ix -> Fix (RepMRec codes ix)
deepFrom = Fix . mapRec deepFrom . fromMRec
\end{code}
\end{myhs}

\paragraph{Only well-formed representations are accepted.}  At first
glance, it may seem like the |Atom| datatype gives too much freedom:
its |I| constructor receives a natural number, but there is no
apparent static check that this number refers to an actual member of
the recursive family we are describing. For example, the list of codes
given by |(P [ (P [ (P [ KInt, I (S (S Z))])])])| is accepted by the
compiler although it does not represent any family of datatypes.

A direct solution to this problem is to introduce yet another index,
this time in the |Atom| datatype, which specifies which indices are
allowed.  The |I| constructor is then refined to take not any natural
number, but only those which lie in the range -- this is usually known
as |Fin n|.

\begin{myhs}
\begin{code}
data Atom (n :: Nat) = I (Fin n) | KInt | dots
\end{code}
\end{myhs}

The lack of dependent types makes this approach very hard, in Haskell.
We would need to carry around the inhabitants |Fin n| and define functionality
to manipulate them, which would greatly hinder the usability of the library.

By looking a bit more closely, we find that we are not losing any type-safety
by allowing codes which reference an arbitrary number of recursive positions.
Users of our library are allowed to write the previous ill-defined code, but
when trying to write \emph{values} of the representation of that code, the
|Lkup| function detects the out-of-bounds index, raising a type error and
preventing the program from compiling in the first place, instead of
crashing at run-time.

\subsubsection{Parameterized Opaque Types}
\label{sec:gp:konparameter}

Up to this point we have considered |Atom| to include a predetermined
selection of \emph{opaque types}, such as |Int|, each of them
represented by one of the constructors other than |I|. This is far
from ideal, for two conflicting reasons:

\begin{enumerate}
\item The choice of opaque types might be too narrow. For example, the
user of our library may decide to use |ByteString| in their
datatypes. Since that type is not covered by |Atom|, nor by our
generic approach, this implies that \texttt{generics-mrsop} becomes
useless to them.
\item The choice of opaque types might be too wide. If we try to
encompass any possible situation, we end up with a huge |Atom|
type. But for a specific use case, we might be interested only in
|Int|s and |Float|s. This means we have to worry about possibly ill-formed
representations and pattern matches which should never be reached.
\end{enumerate}

Our solution is to \emph{parameterize} |Atom|,
giving users the choice of opaque types:

\begin{myhs}
\begin{code}
data Atom kon = I Nat | K kon
\end{code}
\end{myhs}

For example, if we only want to deal with numeric opaque types, we can write:

\begin{myhs}
\begin{code}
data NumericK = KInt | KInteger | KFloat
type NumericAtom = Atom NumericK
\end{code}
\end{myhs}

The representation of codes must be updated to reflect the possibility of
choosing different sets of opaque types. The |NA| datatype in this
final implementation provides two constructors, one per constructor in |Atom|.
The |NS| and |NP| datatypes do not require any change.

\begin{myhs}
\begin{code}
data NA :: (kon -> Star) -> (Nat -> Star) -> Atom kon -> Star where
  NA_I  :: phi    n  -> NA kappa phi (I  n)
  NA_K  :: kappa  k  -> NA kappa phi (K  k)

type  RepMRec (kappa :: kon -> Star) (phi :: Nat -> Star) (c :: [[Atom kon]]) = NS (NP (NA kappa phi)) c
\end{code}
\end{myhs}

The |NA_K| constructor in |NA| makes use of an additional argument |kappa|.
The problem is that we are defining the code for the set of opaque types by
a specific kind, such as |Numeric| above. On the other hand, values which
appear in a field must have a type whose kind is |Star|. Thus, we require a mapping
from each of the codes to the actual opaque type they represent. This
is exactly the \emph{opaque type interpretation} |kappa|. Here is the
datatype interpreting |NumericK| into ground types:

\begin{myhs}
\begin{code}
data NumericI :: NumericK -> Star where
  IInt      :: Int      -> NumericI KInt
  IFloat    :: Float    -> NumericI KFloat
\end{code}
\end{myhs}

The last piece of our framework which has to be updated to support
different sets of opaque types is the |Family| typeclass, as given in
\Cref{fig:gp:int}. This typeclass provides an interesting use case for
the new dependent features in Haskell; both |kappa| and |codes| are
parameterized by an implicit argument |kon| which represents the set of
opaque types.

\begin{figure}
\begin{myhs}
\begin{code}
class Family (kappa :: kon -> Star) (fam :: [Star]) (codes :: [[[Atom kon]]]) where

  fromMRec  :: SNat ix  -> El fam ix -> RepMRec kappa (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec kappa (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}
\caption{|Family| typeclass with support for different opaque types.}
\label{fig:gp:int}
\end{figure}

We stress that the parametrization over opaque types does \emph{not}
mean that we can use only closed universes of opaque types. It is
possible to provide an \emph{open} representation by choosing |(Star)|
-- the whole kind of Haskell's ground types -- as argument to
|Atom|. As a consequence, the interpretation ought to be of kind |Star
-> Star|, as given by |Value|, below. To use |(Star)| as an argument to a type, we must enable
the \texttt{TypeInType} language extension~\cite{Weirich2013,Weirich2017}.



\begin{myhs}
\begin{code}
data Value :: Star -> Star where
  Value :: t -> Value t
\end{code}
\end{myhs}

%  All the generic operations implemented use
%parametrized version of |Atom|s and representations described in this section.
%For convenience we also provide a basic set of opaque types which includes the
%most common primitive datatypes.

\subsubsection{Selection of Useful Combinators}
\label{sec:gp:combinators}

%{
%format f_K  = "\HV{f_k}"
%format f_I  = "\HV{f_I}"
%format eq_K = "\HV{eq_k}"

  The advantages or a \emph{code based} approach to generic programming
becomes evident when we look at the generic combinators that
\texttt{generics-mrsop} provides.  We refer the reader to the
actual documentation for a comprehensive list. Here we look at
a selection of useful functions in their full form. Let us start
with the bifunctoriality of |RepMRec|:

\begin{myhs}
\begin{code}
bimapRep  ::  (forall k   dot kappa1  k   -> kappa2  k)  ->  (forall ix  dot phi1    ix  -> phi2    ix)
          ->  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c
bimapRep f_K f_I = mapNS (mapNP (mapNA f_I f_I))
\end{code}
\end{myhs}

To destruct a |RepMRec kappa phi c| we need a way for
eliminating every recursive position or opaque type inside the
representation and a way of combining these results.

\begin{myhs}
\begin{code}
elimRep  ::  (forall k   dot kappa  k   -> a)  ->  (forall ix  dot phi    ix  -> a)  ->  ([a] -> b) ->  RepMRec kappa phi c -> b
elimRep f_K f_I cat = elimNS cat (elimNP (elimNA f_K f_I))
\end{code}
\end{myhs}

  Another useful operator, particularly when combined with |bimapRep| is
the |zipRep|, that works just like a regular |zip|. Our |zipRep|
attempts to put two values of a representation ``side-by-side'', as long
as they are constructed with the same injection into the $n$-ary sum, |NS|.

\begin{myhs}
\begin{code}
zipRep  ::  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c ->  Maybe (RepMRec (kappa1 :*: kappa2) (phi1 :*: phi2) c)
zipRep r s = case (sop r , sop s) of
   (Tag cr pr , Tag cs ps) -> case testEquality cr pr of
      Just Refl -> inj cr <$$> zipWithNP zipAtom pr ps
\end{code}
\end{myhs}

 We use |testEquality| from |Data.Type.Equality| to check for type index equality
and inform the compiler of that fact by matching on |Refl|.
%%
%%   The |testEquality| function, from |Data.Type.Equality|, tests type indices
%% for propositional equality. It has type |f x -> f y -> Maybe (x :~: y)|,
%% where |(:~:)| is a datatype with a single constructor, |Refl :: x :~: x|.
%% This is analogous to how the majority of dependently typed languages
%% handle propositional equality. In Haskell, we declare the functors that
%% support decidable equality on their indexes through the |TestEquality| typeclass.

  Finally, we can start assembling these building blocks into
more practical functionality. \Cref{fig:gp:genericeq} shows
the definition of generic equality using \texttt{generics-mrsop},
where the |EqHO| typeclass is a lifted version of |Eq|, for types
of kind |k -> Star|, defined below. The library also provide
|ShowHO|, the |Show| counterpart.

\begin{figure}
\begin{myhs}
\begin{code}
geq  ::  (EqHO kappa , Family kappa fam codes) => (forall k dot kappa k -> kappa k -> Bool)
     ->  El fam ix -> El fam ix -> Bool
geq eqK x y = go (deepFrom x) (deepFrom y)
  where go (Fix x) (Fix y)
      =  maybe False (elimRep (uncurry eqK) (uncurry go) and) $  zipRep x y
\end{code} %$
\end{myhs}
\caption{Generic equality.}
\label{fig:gp:genericeq}
\end{figure}

\begin{myhs}
\begin{code}
class EqHO (f :: a -> Star) where
  eqHO :: forall x dot f x -> f x -> Bool
\end{code}
\end{myhs}

  We decided to provide a custom equality in
\texttt{generics-mrsop} for two main reasons. Firstly, when we started
developing the library the
\texttt{-XQuantifiedConstraints}~\cite{Bottu2017} extension was not
completed.  Yet, once quantified constraints were available in Haskell
we wrote \texttt{generics-mrsop-2.2.0} using the extension and
defining |EqHO f| as a synonym to |forall x . Eq (f x)|.  Developing
applications on top of \texttt{generics-mrsop} became more difficult.
The user now would have to reason about and pass around complicated
constraints down to datatypes and auxiliary functions. Moreover, our use
case was very simple, not extracting any of the advantages of
quantified constraints. Eventually we decided to rollback to the lifted
|EqHO| presented above in \texttt{generics-mrsop-2.3.0}.

  As presented so far, we have all the necessary tools to encode our
first differencing attempt, shown in \Cref{chap:structural-patches} of
this thesis. The next sections discusses some aspects that, albeit not
directly required for understanding the remainder of this thesis, are
interesting in their own right and round off the presentation of
\texttt{generics-mrsop} as a library.

%% \subsection{The (Co)Free (Co)Monad}
%% \label{sec:gp:mrsop:holes}
%%
%%   The |SFix| datatype provides a deep representation of an element of
%% a mutually recursive family, which is useful in its own right, but
%% fairly inflexible. Imagine we want to perform some sort of generic unification
%% over terms of a given language -- this will require us to augment our
%% generic representation with unification variables. Another example is the
%% caching of the value of some catamorphism to avoid recomputation -- here
%% we would need to annotate ever layer of the |SFix| with some additional data.
%% Both scenarios can easily be solved with the help of the \emph{free monad}
%% and \emph{cofree comonad}~\cite{Ghani2001}, respectively. \victor{what to cite
%% for free monad?}
%%
%%   In fact, we can combine both the \emph{free monad} and the
%% \emph{cofree comonad} in the same datatype, with different parameters.
%% We can write a fixpoint combinator that receives two additional
%% functors, |phi| and |h| -- one for the comonadic structure and
%% another for the monadic structure.
%%
%% \begin{myhs}
%% \begin{code}
%% data HolesAnn kappa codes phi h at where
%%   Hole'  :: phi at
%%          -> h at
%%          -> HolesAnn kappa codes phi h at
%%   Prim'  :: phi ((P K) k)
%%          -> kappa k
%%          -> HolesAnn kappa codes phi h a
%%   Roll'  :: (IsNat n , IsNat i)
%%          => phi ((P I) i)
%%          -> Constr (Lkup i codes) n
%%          -> NP (HolesAnn kappa codes phi h) (Lkup n (Lkup i codes))
%%          -> HolesAnn kappa codes phi h ((P I) i)
%% \end{code}
%% \end{myhs}
%%
%%   Note how the |SFix kappa fam x| combinator from before can be easily
%% represented through |HolesAnn kappa fam U1 V1 x|, that is, it carries
%% the superfluous (unit type) annotations and has no holes, as expressed
%% by the empty functor |V1|. Moreover, we already expose the sums of products
%% view over the |Roll'| constructor, bypassing the need to translate a |RepMRec|
%% into a |View| every time.
%%
%%   The design advantage of having the free monad and cofree comonad
%% on the same datatype is that we can represent all four variations
%% with the same datatype, writing manipulation functions only once.
%% We now have plain fixpoints, annotated fixpoints (cofree comonad),
%% fixpoints augmented with holes (free monad) and annotated fixpoints
%% augmented with holes:
%%
%% \begin{myhs}
%% \begin{code}
%% type Fix     kappa codes      = HolesAnn kappa codes U1 V1
%% type FixAnn  kappa codes phi  = HolesAnn kappa codes phi V1
%% type Holes   kappa codes      = HolesAnn kappa codes U1
%% \end{code}
%% \end{myhs}
%%
%%   Note that the |Hole| constructor allows for a hole to be placed on a recursive position
%% or on an opaque type, by not restricting its type index. We can disallow holes on opaque
%% values, for example, by passing a custom datatype to |phi| that does so.
%%
%%   Finally, to make these type synonyms useful to a user of the library, we provide sets of
%% pattern synonyms~\cite{Pickering2016} and declare tham as
%% {\small \verb!{-# COMPLETE ... #-}!} -- which
%% stops \texttt{GHC} from issuing \texttt{-Wincomplete-patterns} warnings.
%% This effectively hides this overloading from the user while providing
%% maximum flexibility.
%%
%% \begin{myhs}
%% \begin{code}
%% pattern Fix  :: () => (IsNat i , IsNat n)
%%              => Constr ((P I) i)
%%              -> NP (SFix kappa codes) (Lkup n (Lkup i codes))
%%              -> Fix kappa codes ((P I) i)
%% pattern Fix c xs = Roll' U1 c xs
%%
%% pattern Prim  :: prim k -> Fix kappa codes ((P k) k)
%% pattern Prim x = Prim' U1 x
%% {-# COMPLETE SFix , Prim #-}
%% \end{code}
%% \end{myhs}
%%
%%   In \Cref{sec:gp:simplistic:holes} we will come back to the |HolesAnn|
%% datatype in a slightly different flavour. Since we actually only
%% require this new flavour -- in the majority of \Cref{chap:pattern-expression-patches} --
%% we defer further exploration of |HolesAnn| until then.
%%
%% \victor{I have not yet implemented this |HolesAnn| in this very form in the actual library;
%% it is similar. How important is it that its exactly the same? I think its pretty important, no?}

\subsection{Practical Features}
\label{sec:gp:advancedfeatures}

  The development of the \texttt{generics-mrsop} library started
primarily to enable us to write
\texttt{hdiff} (\Cref{chap:pattern-expression-patches}) possible.  This
was a great expressivity test for our generic programming library and
led us to develop overall useful features that, although not novel,
make the adoption of a generic programming library much more likely.
This section is a small tutorial into two important practical
features of \texttt{generics-mrsop} and documents
the engineering effort that was put in the library.

\subsubsection{Template Haskell}
\label{sec:gp:templatehaskell}

  Having a convenient and robust way to get the |Family| instance for
a given selection of datatypes is of paramount importance for the
usability of our library. In a real scenario, a mutually recursive
family may consist of many datatypes with dozens of
constructors. Sometimes these datatypes are written with parameters,
or come from external libraries.

  Our goal here is to automate the generation of |Family| instances under all
those circumstances using \emph{Template Haskell}~\cite{Sheard2002}.
From the programmers' point of view, they only need to call |deriveFamily|
with the topmost (that is, the first) type of the family. For example:

\newcommand{\shspc}{\hspace{-0.05em}}
%format (tht (a)) = "\HSSym{[\shspc t\shspc|}" a "\HSSym{|\shspc]}"
\begin{myhs}
\begin{code}
data Exp   var = dots
data Stmt  var = dots
data Prog  var = dots
deriveFamily (tht (Prog String))
\end{code}
\end{myhs}

  The |deriveFamily| takes care of unfolding the (type-level) recursion until it
reaches a fixpoint.  In this case, the type synonym |FamProgString = P [Prog
String , dots]| will be generated, together with its |Family|
instance. Optionally, one can also pass along a custom function to decide
whether a type should be considered opaque. By default, it uses a
selection of Haskell built-in types as opaque types.

\paragraph{Unfolding the Family}

  The process of deriving a whole mutually recursive family from a
single member is conceptually divided into two disjoint
processes. First we repeatedly unfold all definitions and follow all the
recursive paths until we reach a fixpoint. At that moment we know that
we have discovered all the types in the family. Second, we translate
the definition of those types to the format our library expects.
During the unfolding process we keep a key-value map in a |State|
monad, keeping track of three things: the types we have seen;
the types we have seen \emph{and} processed; and the indices of
those within the family.

  Let us illustrate this process in a bit more detail using our
running example of a mutually recursive family and consider what
happens within \emph{Template Haskell} when it starts unfolding the
|deriveFamily| clause.

\begin{myhs}
\begin{code}
data Rose a  = Fork a [Rose a]
data [a]     = nil | a : [a]
deriveFamily (tht (Rose Int))
\end{code}
\end{myhs}

  The first thing that happens is registering that we have seen the type
|Rose Int|.  Since it is the first type to be discovered, it is
assigned index zero within the family.  Next we need to reify the
definition of |Rose|. At this point, we query \emph{Template Haskell}
for the definition, and we obtain |data Rose x = Fork x [Rose
x]|. Since |Rose| has kind |Star -> Star|, it cannot be directly
translated -- our library only supports ground types, which are those
with kind |Star|.  But we do not need a generic definition for |Rose|,
we just need the specific case where |x = Int|.  Essentially, we just
apply the reified definition of |Rose| to |Int| and $\beta$-reduce it,
giving us |Fork Int [Rose Int]|.

  The next processing step is looking into the types of the fields of
the (single) constructor |Fork|. First we see |Int| and decide it is
an opaque type, say |KInt|. Second, we see |[Rose Int]| and notice it
is the first time we see this type. Hence, we register it with a fresh
index, |S Z| in this case. The final result for |Rose Int| is |P [P [K
KInt, I (S Z)]]|.

  We now go into |[Rose Int]| for processing.  Once again we need to
perform some amount of $\beta$-reduction at the type-level before
inspecting its fields.  The rest of the process is the same as that for
|Rose Int|.  However, when we encounter the field of type |Rose Int|
this is already registered, so we just need to use the index |Z| in
that position.

  The final step is generating the actual Haskell code from the data
obtained in the previous process. This is a very verbose and
mechanical process, whose details we omit. In short, we generate the
necessary type synonyms, pattern synonyms, the |Family| instance, and
metadata information.  The generated type synonyms are named after the
topmost type of the family, passed to |deriveFamily|:

\begin{myhs}
\begin{code}
type  FamRoseInt    = P [ Rose Int                    , [Rose Int] ]
type  CodesRoseInt  = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
\end{code}
\end{myhs}

%   Pattern synonyms are useful for convenient pattern matching and injecting into
% the |View| datatype. We produce two different kinds of pattern synonyms.
% First, synonyms for generic representations, one per constructor. Second,
% synonyms which associate each type in the recursive family with their
% position in the list of codes.
%
% \vspace{.1cm}
% \begin{myhs}
% %format forkP = "\HT{\overline{Fork}}"
% %format nilP  = "\HT{\overbar{[]}}"
% %format consP = "\HT{\overline{:}}"
% \begin{code}
% pattern forkP x xs  = Tag SZ       (NA_K x :* NA_I xs :* NP0)
% pattern nilP        = Tag SZ       NP0
% pattern x consP xs  = Tag (SS SZ)  (NA_I x :* NA_I xs :* NP0)
% pattern (Pat RoseInt)      = SZ
% pattern (Pat ListRoseInt)  = SS SZ
% \end{code}
% \end{myhs}

  The actual |Family| instance is exactly as the one shown in
\Cref{sec:gp:family}

\begin{myhs}
\begin{code}
instance Family Singl FamRoseInt CodesRoseInt where dots
\end{code}
\end{myhs}


\subsubsection{Metadata}
\label{sec:gp:metadata}

  There is one final ingredient missing to make
\texttt{generics-mrsop} fully usable in practice. We must maintain
the \emph{metadata} information of our datatypes.  This metadata
includes the datatype name, the module where it was defined, and the
name of the constructors. Without this information we would never be
able to pretty print the generic code in a satisfactory way. This
includes conversion to semi-structured formats, such as JSON, or
actual pretty printing.

  Like in \texttt{generics-sop}~\cite{deVries2014}, having the code
for a family of datatypes available allows for a completely separate
treatment of metadata. This is yet another advantage of the
sum-of-products approach compared to the more traditional pattern
functors. In fact, our handling of metadata is heavily inspired from
\texttt{generics-sop}, so much so that we will start by explaining a
simplified version of their handling of metadata, and then outline the
differences to our approach.

  The general idea is to store the meta information following the
sum-of-products structure of the datatype itself. Instead of data, 
we keep track of the names of the different parts and other meta information 
that can be useful. It is advantageous to keep metadata separate from the
generic representation as it would only clutter the definition of
generic functionality.  This information is tied to a datatype by
means of an additional typeclass |HasDatatypeInfo|.  Generic
functions may now query the metadata by means of functions like
|datatypeName|, which reflect the type information into the term
level.  The definitions are given in \Cref{fig:gp:sopmeta} and follow
closely how \texttt{generics-sop} handles metadata.

\begin{figure}
\begin{myhs}
\begin{code}
data DatatypeInfo :: [[Star]] -> Star where
  ADT  :: ModuleName -> DatatypeName -> NP  ConstrInfo cs       -> DatatypeInfo cs
  New  :: ModuleName -> DatatypeName ->     ConstrInfo (P [c])  -> DatatypeInfo (P [ P [ c ]])

data ConstrInfo :: [Star] -> Star where
  Constructor  :: ConstrName                             -> ConstrInfo xs
  Infix        :: ConstrName -> Associativity -> Fixity  -> ConstrInfo (P [ x, y ])
  Record       :: ConstrName -> NP FieldInfo xs          -> ConstrInfo xs

data FieldInfo :: Star -> Star where
  FieldInfo :: FieldName -> FieldInfo a

class HasDatatypeInfo a where
  datatypeInfo :: proxy a -> DatatypeInfo (Code a)
\end{code}
\end{myhs}
\caption{Definitions related to metadata from \texttt{generics-sop}.}
\label{fig:gp:sopmeta}
\end{figure}

  Our library uses the same approach to handle metadata. In fact, the
code remains almost unchanged, except for adapting it to the larger
universe of datatypes we can now handle. Unlike \texttt{generic-sop},
our list of lists representing the sum-of-products structure does not
contain types of kind |Star|, but |Atom|s. All the types representing
metadata at the type-level must be updated to reflect this new
scenario:

\begin{myhs}
\begin{code}
data DatatypeInfo  :: [  [  Atom kon ]]  -> Star where dots
data ConstrInfo    ::    [  Atom kon ]   -> Star where dots
data FieldInfo     ::       Atom kon     -> Star where dots
\end{code}
\end{myhs}

  As we have discussed above, our library is able to generate codes not
only for single types of kind |Star|, like |Int| or |Bool|, but also
for types which are the result of type-level applications, such as
|Rose Int| and |[Rose Int]|.  The shape of the metadata information in
|DatatypeInfo|, a module name plus a datatype name, is not enough to
handle these cases.  We replace the uses of |ModuleName| and
|DatatypeName| in |DatatypeInfo| by a richer promoted type |TypeName|,
which can describe applications, as required.

\begin{myhs}
\begin{code}
data TypeName = ConT ModuleName DatatypeName | TypeName :@: TypeName

data DatatypeInfo :: [[Atom kon]] -> Star where
  ADT  ::  TypeName  -> NP  ConstrInfo cs       ->  DatatypeInfo cs
  New  ::  TypeName  ->     ConstrInfo (P [c])  ->  DatatypeInfo (P [ P [ c ]])
\end{code}
\end{myhs}

  An important difference to \texttt{generics-sop}
is that the metadata is not defined for a single type, but
for a type \emph{within} a family. This can be seen in the signature of
|datatypeInfo|, which receives proxies for both the family and the type.
The type equalities in that signature reflect the fact that the given type
|ty| is included with index |ix| within the family |fam|. This step is needed
to look up the code for the type in the right position of |codes|.

\begin{myhs}
\begin{code}
class (Family kappa fam codes) => HasDatatypeInfo kappa fam codes ix | fam -> kappa codes where
  datatypeInfo  ::  (ix ~ Idx ty fam , Lkup ix fam ~ ty) =>  Proxy fam -> Proxy ty
                ->  DatatypeInfo (Lkup ix codes)
\end{code}
\end{myhs}

  Template Haskell would generate the instance below for |Rose Int|:

\begin{myhs}
\begin{code}
instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _  = ADT (ConT "E" "Rose" :@: ConT "Prelude" "Int")
                    $ (Constructor "Fork") :* NP0
\end{code} %$
\end{myhs}

\subsection{Example: Well-Typed Classical Tree Differencing}
\label{sec:gp:well-typed-tree-diff}

  This section, based on the work of Lempsink~\cite{Lempsink2009} which
originally implemented in the \texttt{gdiff} library, is the
related work that is closest to ours in the sense that it is the only
\emph{typed} approach to differencing. The presentation provided here
is adapted from Van Putten's~\cite{Putten2019} master thesis and is
available as the \texttt{generics-mrsop-gdiff} library.

  Next, we discuss how to make tree edit-scripts (\Cref{sec:background:tree-edit-distance})
type-safe following the work of Lempsink~\cite{Lempsink2009}.
We start by lifting edit-scripts to kind |[Star] -> [Star] -> Star|, which enables
the indexing of the types for the source and destination forests of
particular edit-scripts.  Consequently, instead of differencing a list
of trees, we will difference an $n$-ary product, |NP|, indexed by the
type of each tree.

\begin{myhs}
\begin{code}
type PatchGDiff kappa codes xs ys = ES kappa codes xs ys

diff  :: (TestEquality kappa, EqHO kappa)
      => NP (NA kappa (Fix kappa codes)) xs -> NP (NA kappa (Fix kappa codes)) ys
      -> PatchGDiff kappa codes xs ys
\end{code}
\end{myhs}

  One confusing complication is that our edit operations operate over
both constructors of the family and opaque values, unlike the untyped
version of tree differencing
(\Cref{sec:background:tree-edit-distance}), where everything is a
label. Consequently, writing the edit operations requires a uniform
treatment of recursive constructors and opaque values, which is done
by the |Cof| type, read as \emph{constructor-of}. This represents the
\emph{unit of modification} of each edit operation.  A value of type
|Cof kappa codes at tys| represents a constructor of atom |at|, which
expects arguments whose type is |NP I tys|, for the family |codes|
with opaque types interpreted by |kappa|.  Its definition is given
below.

\begin{myhs}
\begin{code}
data Cof kappa codes :: Atom kon -> [Atom kon] -> Star where
  ConstrI  :: (IsNat c, IsNat n)
           => Constr (Lkup n codes) c -> ListPrf (Lkup c (Lkup n codes))
           -> Cof kappa codes ((P I) n) (Lkup c (Lkup n codes))
  ConstrK  :: kappa k -> Cof kappa codes ((P K) k) Pnil
\end{code}
\end{myhs}

  We need the |ListPrf| argument to |ConstrI| to be able to manipulate
the type-level lists when defining the application function,
|applyES|.  But first, we have to define our edit-scripts. A value
of type |ES kappa codes xs ys| represents a transformation of a value of
|NP (NA kappa (Fix kappa codes)) xs| into a value of |NP (NA kappa (Fix ki
codes)) ys|.  The |NP| serves as a list of trees, as is usual for the
tree differencing algorithms, but it enables us to keep track of the
type of each individual tree through the index to |NP|.

\begin{myhs}
\begin{code}
data ES kappa codes :: [Atom kon] -> [Atom kon] -> Star where
  ES0  :: ES kappa codes (P []) (P [])
  Ins  :: Cof kappa codes a t  -> ES kappa codes          i   (t :++:  j)  -> ES kappa codes           i   (a Pcons  j)
  Del  :: Cof kappa codes a t  -> ES kappa codes (t :++:  i)           j   -> ES kappa codes (a Pcons  i)            j
  Cpy  :: Cof kappa codes a t  -> ES kappa codes (t :++: i)   (t :++:  j)  -> ES kappa codes (a Pcons i)   (a Pcons  j)
\end{code}
\end{myhs}

%format tn = "\HV{t_n}"
  Let us take |Ins|, for example. Inserting a constructor |c :: t1 ->
dots -> tn -> (P I ix)| in a forest |x1 :* x2 :* dots :* Nil| will
take the first |n| elements of that forest and use them as arguments to
|c|. This is realized by the |insCof| function, shown below.

\begin{myhs}
\begin{code}
insCof  :: Cof kappa codes a t
        -> NP (NA kappa (Fix kappa codes)) (t :++: xs) -> NP (NA kappa (Fix kappa codes)) (a Pcons xs)
insCof (ConstrK k)        xs =  NA_K k :* xs
insCof (ConstrI c ispoa)  xs =  let (poa, xs') = split ispoa xs in NA_I (Fix $$ inj c poa) :* xs'
\end{code}
\end{myhs}

  The example also showcases the use of the |ListPrf| present in |ConstrI|, which is
necessary to enable us to split the list |t :++: xs| into |t| and |xs|. The
typechecker needs some more information about |t|, since type families are
not injective. The |split| function has type:

\begin{myhs}
\begin{code}
split :: ListPrf xs -> NP p (xs :++: ys) -> (NP p xs, NP p ys)
\end{code} %
\end{myhs}

  The |delCof| function is dual to |insCof|, but since we construct
a |NP| indexes over |t :++: xs|, we need not use the |ListPrf| argument.
Finally, we can assemble the application function that witnesses
the semantics of |ES|:

\begin{myhs}
\begin{code}
applyES  :: (forall k dot Eq (kappa k)) => ES kappa codes xs ys -> PoA kappa (Fix kappa codes) xs
         -> Maybe (PoA kappa (Fix kappa codes) ys)
applyES ES0           _   = Just Nil
applyES (Ins _ c es)  xs  = insCof c <$$> applyES es xs
applyES (Del _ c es)  xs  = delCof c xs >>= applyES es
applyES (Cpy _ c es)  xs  = insCof c <$$> (delCof c xs >>= applyES es)
\end{code}
\end{myhs}

\subsubsection{Discussion}

  The approach of providing typed edit operations has many nice
aspects. It immediately borrows the existing algorithms and
metatheory and can improve the size of edit-scripts significantly
by being able to provide |CpyTree|, |InsTree| and |DelTree| which
copy, insert and delete entire trees instead of operating
on individual constructors. This is possible because we can look at
the type of the edit-script in question -- substitute the insertion
of a constructor by |InsTree| whenever all of its fields are also
comprised solely of insertions.

  Although type-safe by construction, which is undoubtedly a plus point,
computing edit-scripts, with memoization, still takes $\mathcal{O}(n
\times m)$ time, where $n$ and $m$ are the number of constructors in
the source and destination trees. This means this is at least
quadratic in the size of the smaller input, which is not practical for
a tool that is supposed to be run multiple times per commit on large
inputs (hundreds to thousands of lines). This downside is not specific 
to this approach, but rather quite common for tree differencing 
algorithms. They often belong to complexity classes that make them impractical.

  Another downside comes to the surface when we want to look into merging
these edit-scripts. Vassena~\cite{Vassena2016} developed a merging
algorithm but notes some difficult setbacks, mainly due to
the heterogeneity of |ES|. Suppose, for example, we want to merge |p : ES xs ys|
and |q : ES xs zs|. This means producing an edit-script |r| that
transforms the forest |xs| into some other forest |ks|.
But how can we determine |ks| here? It is not always the case that
there is a solution. In fact, the merge algorithm~\cite{Vassena2016}
for |ES| might fail due to conflicting changes \emph{or} the
inability to find a suitable |ks|.
Regardless, the work of Vassena~\cite{Vassena2016}
was of great inspiration for this thesis in
showing that there definitely is a place for type-safe approaches
to differencing.

\section{The \genericssimpl{} Library}
\label{sec:gp:simplistic}

  Unfortunately, the \texttt{generics-mrsop} uncovered a memory
leak in the Haskell compiler itself when used for large
mutually recursive families. The bugs have been reported
in the GHC bug tracker\footnote{
\url{https://gitlab.haskell.org/ghc/ghc/issues/17223} and
\url{https://gitlab.haskell.org/ghc/ghc/issues/14987}}
but have not been resolved at the time of writing.
This means that if we wish to collect large scale real data
for our experiments, we must develop an alternative approach.

  \digress{After realizing that the differencing algorithms presented in
\Cref{chap:pattern-expression-patches} did not explicitly require
sums of products to work, I was able to implement a workaround
using \texttt{GHC.Generics} to encode mutually recursive families. The
main idea is to take the dual approach from
\texttt{generics-mrsop}: instead of defining which types belong in the
family, we define which types \emph{do not} belong to the family.
Corresponding with A. Serrano we discussed how this approach could
be seen as an extension of his \genericssimpl{}
library, which lead me to write the layer that handles deep representations with
support for mutual recursion on top a the preliminary version of this library,
giving rise to the \genericssimpl{} library in its current form.}

\subsection{The Simplistic View}

  The \genericssimpl{} library
can be seen as a layer on top of \texttt{GHC.Generics} to ease out the
definition of new generic functionality. The pattern functor approach
used by \texttt{GHC.Generics}, shown in \Cref{sec:background:patternfunctors},
requires the user to write a large number of typeclass instances to define
even basic generic functions. Yet, the pattern functors generated by GHC
are restricted to sums, products, unit, constants and metadata information.
This means we can model representations as a single GADT, |SRep|
defined below, indexed by the pattern functor it inhabits.

\begin{myhs}
\begin{code}
data SRep (phi :: Star -> Star) :: (Star -> Star) -> Star where
  S_U1    ::                                 SRep phi U1
  S_K1    ::                 phi a       ->  SRep phi (K1 i a)
  S_L1    ::                 SRep phi f  ->  SRep phi (f :+: g)
  S_R1    ::                 SRep phi g  ->  SRep phi (f :+: g)
  (:**:)  :: SRep phi f  ->  SRep phi g  ->  SRep phi (f :*: g)
  S_M1    :: SMeta i t   ->  SRep phi f  ->  SRep phi (M1 i t f)
\end{code}
\end{myhs}

  The handling of metadata is borrowed entirely from \texttt{GHC.Generics}
and captured by the |SMeta| datatype, which records the kind of
meta-information stored at the type-level.

\begin{myhs}
\begin{code}
data SMeta i t where
  SM_D  :: Datatype    d  => SMeta D d
  SM_C  :: Constructor c  => SMeta C c
  SM_S  :: Selector    s  => SMeta S s
\end{code}
\end{myhs}

  The |SRep| datatype enables us to write generic functionality
more concisely than \texttt{GHC.Generics}. Take the |gsize| function from
\Cref{sec:background:patternfunctors} as an example.
With pure \texttt{GHC.Generics}, we must use |Size| and |GSize|
typeclasses. With |SRep| we can write it directly, provided
we have a way to count the size of the leaves of type |phi|.

\begin{myhs}
\begin{code}
gsize  :: (forall x dot phi x -> Int) -> SRep phi f -> Int
gsize r S_U1         = 0
gsize r (S_K1    x)  = r x
gsize r (S_M1 _  x)  = gsize r x
gsize r (S_L1    x)  = gsize r x
gsize r (S_R1    x)  = gsize r x
gsize r (x :**: y)   = gsize r x + gsize r y
\end{code}
\end{myhs}

  Naturally, we still need to convert values of |GHC.Generics.Rep f x|
into their closed representation, |SRep phi (GHC.Generics.Rep f)| and
make some choice for |phi|. We could use |K1 R| as |phi|, essentially
translating only the first layer into a generic representation,
but as we shall see in \Cref{sec:gp:simplistic-deep}, we can also
translate the entire value and use a fixpoint combinator in |phi|.

  Even though |SRep| lacks a \emph{codes-based} approach, that is,
it can be defined for arbitrary types like \texttt{GHC.Generics},
it still admits some combinators that greatly assist a
programmer when writing their generic code, unlike \texttt{GHC.Generics}.
The most useful are |repMap|, |repZip| and |repLeaves|, that map, zip
and collect the leaves of a |SRep| respectively. These can easily
be generalized to a monadic version.

\begin{myhs}
\begin{code}
repMap     :: (forall x dot phi x -> psi x) -> SRep phi f -> SRep psi f

repZip     :: SRep phi f -> SRep psi f -> Maybe (SRep (phi :*: psi) f)

repLeaves  :: SRep phi f -> [Exists phi]
\end{code}
\end{myhs}


\subsection{Mutual Recursion}
\label{sec:gp:simplistic-deep}

  The |SRep phi f| datatype enables us to write generic functions
without resorting to typeclasses and also provides a simple
way to interact with potentially recursive subtrees through the
|phi| functor. To write a deep representation,
all we have to do is define a mutually recursive family to be
any type that is \emph{not} a primitive type, where
the choice of primitive type shall be parameterized through
the usual |kappa| parameter. The pseudo-code below illustrates
this idea.

\begin{myhs}
\begin{code}
data SFix kappa :: Star -> Star where
  Prim  :: (x `elem` kappa)                  => x -> SFix kappa fam x
  SFix  :: (not (x`elem` kappa), Generic x)  => SRep (SFix prim) (Rep x)  -> SFix kappa fam x
\end{code}
\end{myhs}

  This approach works well for simpler applications, but by defining a
mutually recursive family in an \emph{open} fashion, \ie{}, |t| is an
element iff |not (t `elem` kappa)|, for some list |kappa| of types
regarded as primitive, we would only be able to check for index equality
through the |Typeable| machinery~\cite{PeytonJones2016}.
This would have to spread across the library, inherently breaking
parametricity of maps and catamorphisms besides polluting the interface.
Checking for index equality is crucial for the definition of many
generic concepts -- zippers being a prominent example, \Cref{sec:gp:simplistic-zipper} --
and was trivial to define  in \texttt{generics-mrsop}, thanks
to its \emph{closed} approach: should two types be identified by the same index
into a list containing all members of the family, then they are the same type.

  To avoid having to spread |Typeable|s around but still maintaining decidable
type index equality we will apply the same trick here and define a family as two
disjoint lists: a type-level list |fam| for the elements that belong
in the family and one for the primitive types, usually denoted |kappa|.
Note that unlike \texttt{generics-mrsop}, |kappa| here has kind |P [ Star ]|.

  Recursion is easily achieved through a |SFix kappa fam| combinator,
where |fam :: P [ Star ]| is the list of types that belong
in the family and |kappa :: P [ Star ]| is the list of types to be considered primitive,
that is, is is not unfolded into a generic representation. The |SFix|
combinator has two constructors, one for carrying values
of primitive types and one for unfolding a next layer of the generic
representation, as defined below.

\begin{myhs}
\begin{code}
data SFix kappa fam :: Star -> Star where
  Prim  :: (PrimCnstr kappa fam x) => x -> SFix kappa fam x

  SFix  :: (CompoundCnstr kappa fam x) => SRep (SFix prim) (Rep x) -> SFix kappa fam x
\end{code}
\end{myhs}

  Here, |PrimCnstr| and |CompoundCnstr| are constraint synonyms, defined below,
to encapsulate what it means for a type |x| to be primitive (resp. compound)
with respect to the |fam| and |prim| list of types.

\begin{myhs}
\begin{code}
type PrimCnstr      kappa fam x = (Elem x kappa , NotElem x fam)
type CompoundCnstr  kappa fam x = (Elem x fam   , NotElem x kappa , Generic x)
\end{code}
\end{myhs}

  |Elem| and |NotElem| are custom constraints that state whether
or not a type is an element of a list of types. They are defined with
the help of the boolean type family and, in the |Elem| case,
we also carry a typeclass that enables us to construct
a membership proof.

\begin{myhs}
\begin{code}
type Elem     a as  = (IsElem a as ~ P True , HasElem a as)
type NotElem  a as  = IsElem a as ~ P False

type family IsElem (a :: Star) (as :: [ Star ]) :: Bool where
  IsElem a           (P [])  = P False
  IsElem a (a Pcons  as)     = P True
  IsElem a (b Pcons  as)     = IsElem a as
\end{code}
\end{myhs}

  |HasElem a as|, here, is a typeclass that produces an actual proof
that the list |as| contains |a| -- encoded in a datatype |ElemPrf a as|.
Pattern matching on a value of type |ElemPrf a as| will unfold the structure of |as|.
This is crucial in, for example, accessing typeclass instances for
types in |SFix kappa fam|. The |HasElem| typeclass and |ElemPrf| datatype
are defined below.

\begin{myhs}
\begin{code}
data ElemPrf a as where
  Here   :: ElemPrf a (a Pcons as)
  There  :: ElemPrf a as -> ElemPrf a (b Pcons as)

class HasElem a as where
  hasElem :: ElemPrf a as
\end{code}
\end{myhs}

  To define generic functions, we often need operation over the primitive types.
We can encode this via constraints, requiring that \emph{all} elements
of |kappa| have instances of some typeclass. Suppose we would like to write a
term-level equality operator for values of type |SFix kappa fam x|, as
in the |Eq| typeclass. This would require to ultimately compare
values of type |y|, for some |y| such that |Elem y kappa|.  Naturally,
this can only be done if all elements of |kappa| are members of the
|Eq| typeclass. We specify that all elements of |kappa| satisfy
a constraint with the |All|~\cite{deVries2014} type family:

\begin{myhs}
\begin{code}
type family All c xs :: Constraint where
  All c  (P [])        = ()
  All c  (x (P :) xs)  = (c x , All c xs)
\end{code}
\end{myhs}

  Now, given a function with type |(All Eq prim) => SFix prim x -> dots|,
we must extract the |Eq y| instance from |All Eq prim|, for some |y|
such that |IsElem y prim ~ P True|. This is where |ElemPrf|  becomes
essential. By pattern matching on |ElemPrf|  we are able to extract the
necessary instance, as shown by the |witness| function below. Naturally,
once we find the instance we are looking for, we record it in a datatype
for easier access.

\begin{myhs}
\begin{code}
data Witness c x where
  Witness :: (c x) => Witness c x

witness  :: forall x xs c dot (HasElem x xs , All c xs) => Proxy xs -> Witness c x
witness _ = witnessPrf (hasElem :: ElemPrf x xs)
  where  witnessPrf :: (All c xs) => ElemPrf x xs -> Witness c x
         witnessPrf Here       = Witness
         witnessPrf (There p)  = witnessPrf p
\end{code}
\end{myhs}

  The |witness| function above enables us to cast the
usual |(==)| function, from |Eq|, as operating over any
element of a list of types. Pattern matching on the result
of |witness| enables the compiler to access the necessary |Eq|
instance. With the help of |weq| below,
we define the |Eq| instance for |SFix| in \Cref{fig:gp:sfix-eq}.
Note that calling |witness| will require an explicit type
annotation informing the compiler about which typeclass
we wish to extract from the top-level |All| constraint.

\begin{myhs}
\begin{code}
weq :: forall x xs dot (All Eq xs , Elem x xs) => Proxy xs -> x -> x -> Bool
weq p = case witness p :: Witness Eq x of Witness -> (==)
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
instance (All Eq kappa) => Eq (SFix kappa fam f) where
  (Prim x) == (Prim y)  = weq x y
  (SFix x) == (SFix y)  = maybe False (all (==) . repLeaves) (repZip x y)
\end{code}
\end{myhs}
\caption{Equality instance for |SFix|.}
\label{fig:gp:sfix-eq}
\end{figure}

  With the |Elem| functionality in place, we can define type-level
equality for elements of a given list -- given |SFix kappa fam x| and
|SFix kappa fam y|, to be able to know whether |x :~: y|.  This functionality is
important when defining the zipper~\cite{Huet1997} or generic unification,
and it comes for free in code-based approaches, such as \texttt{generics-mrsop}. In our
current setting, we need to use the |fam| type-level list and
the |HasElem| typeclass.  Note that the proxies are present solely to
aid the reduction of the |IsElem| type family, needed for |Elem|.

\begin{myhs}
\begin{code}
sameType  :: (Elem x fam , Elem y fam)
          => Proxy fam -> Proxy x -> Proxy y -> Maybe (x :~: y)
sameType _ _ _ = sameIdx (hasElem :: ElemPrf x fam) (hasElem :: ElemPrf y fam)
  where  sameIdx :: ElemPrf x xs -> ElemPrf x' xs -> Maybe (x :~: x')
         sameIdx Here        Here       = Just Refl
         sameIdx (There rr)  (There y)  = go rr y
         sameIdx _           _          = Nothing
\end{code}
\end{myhs}


\paragraph{Converting to a deep representation.}
  With representational issues out of the way, we shall need to
translate between a value and its deep \texttt{GHC.Generics}-based
representation. This can be done with the generic functions |dfrom| and |dto|,
which follow the textbook recipe of defining generic functionality
with \texttt{GHC.Generics}: use a typeclass and its generic
variant and use \emph{default signatures}
to bridge the gap between them. In our case, this is done with
the |Deep| and |GDeep| typeclasses, declared in \Cref{fig:gp:gdeep}.

\begin{figure}
\begin{myhs}
\begin{code}
class (CompoundCnstr kappa fam a) => Deep kappa fam a where
  dfrom :: a -> SFix kappa fam a
  default dfrom  :: (GDeep kappa fam (Rep a)) => a -> SFix kappa fam a
  dfrom = SFix . gdfrom . from

  dto :: SFix kappa fam a -> a
  default dto  :: (GDeep kappa fam (Rep a)) => SFix kappa fam a -> a
  dto (SFix x) = to (gdto x)

class GDeep kappa fam f where
  gdfrom  :: f x -> SRep (SFix kappa fam) f
  gdto    :: SRep (SFix kappa fam) f -> f x
\end{code}
\end{myhs}
\caption{Declaration of |Deep| and |GDeep| typeclasses.}
\label{fig:gp:gdeep}
\end{figure}

  Defining the |GDeep| instances is straightforward with the exception
of the |(K1 R a)| case, where we must decide whether or not |a|
is a primitive type. Ideally we would like to write something
in the lines of:

\begin{myhs}
\begin{code}
instance (IsElem a kappa ~ P True)   => GDeep kappa fam (K1 R a) dots
instance (IsElem a kappa ~ P False)  => GDeep kappa fam (K1 R a) dots
\end{code}
\end{myhs}

  But \texttt{GHC} cannot distinguish between these two instances
when resolving them. Not even \texttt{-XOverlappingInstances}
can help us here. The only way out is to abstract the call to |IsElem|
to an auxiliary typeclass, which ``pattern matches'' on the
result of this type-level computation.

\begin{myhs}
\begin{code}
class GDeepAtom kappa fam (isPrim :: Bool) a where
  gdfromAtom  :: Proxy isPrim -> a -> SFix kappa fam a
  gdtoAtom    :: Proxy isPrim -> SFix kappa fam a -> a
\end{code}
\end{myhs}

  The |GDeepAtom| class possesses only two instances, one for primitive types
and one for types we wish to consider as members of our mutually
recursive family, which are indicated by the |isPrim| parameter.
We recall the definitions for |CompoundCnstr| and |PrimCnstr| below.

\begin{myhs}[.93\textwidth]
\begin{code}
instance (CompoundCnstr  kappa fam a , Deep kappa fam a)  => GDeepAtom kappa fam (P False)  a dots
instance (PrimCnstr      kappa fam a)                     => GDeepAtom kappa fam (P True)   a dots

type PrimCnstr      kappa fam x = (Elem x kappa , NotElem x fam)
type CompoundCnstr  kappa fam x = (Elem x fam   , NotElem x kappa , Generic x)
\end{code}
\end{myhs}

  Finally, the actual instance for |GDeep prim (K1 R a)| triggers the evaluation
of |IsElem|, which in turn brings into scope the correct
variation of the |GDeepAtom|:

\begin{myhs}
\begin{code}
instance (GDeepAtom kappa fam (IsElem a prim) a) => GDeep kappa fam (K1 R a) dots
\end{code}
\end{myhs}

  With the |Deep| typeclass setup, all we have to do is declare an empty instance
for every element of the family. \Cref{fig:gp:simplistic:example}
illustrates the usage for the |Rose| datatype.
The monomorphic versions of |dfrom| and |dto| simply aid the compiler
by providing all necessary type parameters.

\begin{figure}
\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
  deriving (Eq , Show , Generic)

type PrimsRose  = P [ Int ]
type FamRose    = P [ Rose Int , [Rose Int] ]

instance Deep PrimsRose FamRose (Rose Int)
instance Deep PrimsRose FamRose [ Rose Int ]

dfromRose :: Rose Int -> SFix PrimsRose FamRose (Rose Int)
dfromRose = dfrom

dtoRose :: SFix PrimsRose FamRose (Rose Int) -> Rose Int
dtoRose = dto
\end{code}
\end{myhs}
\caption{Usage example for \genericssimpl{}.}
\label{fig:gp:simplistic:example}
\end{figure}

\subsection{The (Co)Free (Co)Monad}
\label{sec:gp:simplistic:holes}

  Although the |SFix| type makes for a very intuitive recursion combinator,
it does not give us much flexibility: it does not support
annotations nor holes. For example, suppose we want to define
a generic unification algorithm: how would we represent
unification variables within |SFix|? We would need an augmented
|SFix| which would carry one extra constructor for unification variables.
Another example would be annotating an |SFix| with some auxiliary
values to make certain computations more efficient.
These variations over fixpoints can be achieved by
combining the free monad and the cofree comonad in the same type,
which we name |HolesAnn kappa fam phi h a|. A value of type |HolesAnn kappa fam phi h a|
is isomorphic to a value of type |a|, where each constructor is annotated
with |phi| and we might have holes of type |h|.

\begin{myhs}
\begin{code}
data HolesAnn kappa fam phi h a where
  Hole'  :: phi a -> h a -> HolesAnn kappa fam phi h a
  Prim'  :: (PrimCnstr kappa fam a)      => phi a -> a -> HolesAnn kappa fam phi h a
  Roll'  :: (CompoundCnstr kappa fam a)  => phi a -> SRep (HolesAnn kappa fam phi h) (Rep a)
         -> HolesAnn kappa fam phi h a
\end{code}
\end{myhs}

  The |SFix| combinator presented earlier can be easily seen as the
special case where annotations are the unit type, |U1|, and holes do
not exist (which is captured by the empty type |V1|). We can represent
all the variations over fixpoints through type synonyms:

\begin{myhs}
\begin{code}
type SFix     kappa fam      = HolesAnn kappa fam U1 V1
type SFixAnn  kappa fam phi  = HolesAnn kappa fam phi V1
type Holes    kappa fam      = HolesAnn kappa fam U1
\end{code}
\end{myhs}

  Again, with the help of pattern synonyms and \texttt{COMPLETE} pragmas -- which
stops \texttt{GHC} from issuing \texttt{-Wincomplete-patterns} warnings -- we
can simulate the |SFixAnn| datatype, for example.

\begin{myhs}
\begin{code}
pattern SFixAnn  :: () => (CompoundCnstr kappa fam a)
                 => phi a -> SRep (SFixAnn kappa fam phi) (Rep a) -> SFixAnn kappa fam phi a
pattern SFixAnn ann x = Roll' ann x

pattern PrimAnn  :: () => (PrimCnstr kappa fam a) => phi a -> a -> SFixAnn kappa fam ann a
pattern PrimAnn ann x = Prim' ann x
{-# COMPLETE SFixAnn , PrimAnn #-}
\end{code}
\end{myhs}

  Annotated fixpoints, in fact, are very important for us.
Many of the algorithms in \Cref{chap:pattern-expression-patches}
proceed by first annotating a tree with some auxiliary information and then
computing a result over said tree. This ensures we never recompute
auxiliary information and keeps our algorithms linear.

\subsubsection{Annotated Fixpoints}
\label{sec:gp:annfix}

  Catamorphisms are used in a large number of computations over recursive
structures. They receive an algebra that is used to consume one layer of
a datatype at a time and consumes the whole value of the datatype using this
\emph{recipe}. The definition of the catamorphism is trivial in a setting
where we have explicit recursion:

\begin{myhs}
\begin{code}
cata  :: (forall b dot (CompoundCnstr kappa fam b)  => SRep phi (Rep b) -> phi b)
      -> (forall b dot (PrimCnstr kappa fam b) => b -> phi b) -> SFix kappa fam h a -> phi a
cata f  g  (SFix x)  = f (repMap (cata f g) x)
cata _  g  (Prim x)  = g x
\end{code}
\end{myhs}

  One example of catamorphisms is computing the \emph{height} of
a recursive structure. It can be defined with |cata|
in a simple manner with the help of the |Const| functor.

\begin{myhs}[.93\textwidth]
\begin{code}
newtype Const t x = Const { getConst :: t }

heightAlgebra :: SRep (Const Int) xs -> Const Int iy
heightAlgebra = Const . (1+) . maximum . (0:) . map (exElim getConst) . repLeaves

height :: SFix kappa fam a -> Int
height = getConst . cata heightAlgebra
\end{code}
\end{myhs}

  Now imagine our particular application makes a number of decisions
based on the height of the (generic) trees it handles. Calling
|height| at each of those decision points is time consuming.
It is much better to compute the height of a tree only once and keep
the intermediary results annotated in their respective subtrees.
We can easily do so with our |SFixAnn| \emph{cofree comonad}~\cite{Ghani2001}.
In fact, we would say that the height is a synthesized attribute in
\emph{attribute grammar}~\cite{Knuth1990} lingo.

\begin{myhs}
\begin{code}
synthesize  :: (forall b dot (CompoundCnstr kappa fam a) => SRep phi (Rep b) -> phi b)
            -> (forall b dot (PrimCnstr kappa fam a) => b -> phi b)
            -> SFix kappa fam a -> SFixAnn  kappa fam phi  a
synthesize  f g  = cata (\r -> SFixAnn (f (repMap getAnn r)) r) (\a -> PrimAnn (g b) b)
\end{code}
\end{myhs}

  Finally, an algorithm that constantly queries the height of the subtrees
can be computed in two passes: in the first pass we compute the heights and
leave them annotated in the tree, in the second we run the algorithm.
Moreover, we can compute all the necessary synthesized attributes an algorithm
needs in a single preprocessing phase. This is a crucial maneuver to
make sure our generic programs can scale to real-world inputs.
Naturally, |cata| and |synthesize| are actually implemented in their monadic
form and over |HolesAnn| for maximal generality.

\subsection{Practical Features}

  Whilst developing \texttt{hdiff} (\Cref{chap:pattern-expression-patches}), we
ran into a number of practicalities regarding the underlying generic programming
library. Of particular importance are zippers and unification, which play
a big role in the algorithms underlying the \texttt{hdiff} approach. This section
gives an overview of those features.

\subsubsection{Zippers}
\label{sec:gp:simplistic-zipper}

  Zippers~\cite{Huet1997} are a well established technique for traversing a recursive
data structure keeping track of a focus point. Defining
generic zippers is not new, this has been done by many authors
\cite{Adams2010,Hinze2004,Yakushev2009} for many different classes of datatypes
in the past. In our particular case, we are not interested in traversing a generic
representation by means of the usual zipper traversals -- up, down, left and
right -- which move the focus point. Instead, we just want a datatype that
encodes a context with one focus, encoded by |SZip| below.
A value of type |SZip ty w f| represents a value of type |SRep w f|
with one \emph{hole}, or \emph{focus}, in a position with type |ty|.

\begin{myhs}
\begin{code}
data SZip ty w f where
  Z_L1     ::                 SZip ty  w f  -> SZip ty w (f :+: g)
  Z_R1     ::                 SZip ty  w g  -> SZip ty w (f :+: g)

  Z_PairL  :: SZip ty w f  -> SRep     w g  -> SZip ty w (f :*: g)
  Z_PairR  :: SRep w f     -> SZip ty  w g  -> SZip ty w (f :*: g)

  Z_M1     :: SMeta i t    -> SZip ty  w f  -> SZip ty w (M1 i t f)
  Z_KH     ::                               -> SZip ty w (K1 i a)
\end{code}
\end{myhs}

The |Zipper| datatype will ensure that the focus lies in a recursive position.
Its definition is given below. It encapsulates the |ty| above as an existential
type and keeps the focus point accessible. We also pass around a
constraint-kinded variable to enable one to specify custom constraints
about the types in question.

\begin{myhs}
\begin{code}
data Zipper c f g t where
  Zipper :: c => SZip t f (Rep t) -> g t -> Zipper c f g t
\end{code}
\end{myhs}

  Given a value of type |SZip ty phi t| and a value of type |phi ty|,
it is straightforward to plug the hole and produce a |SRep phi t|.
The other way around, however, is more complicated. Given a |SRep phi t|,
we might have many possible zippers -- binary trees, for example, can have
a hole on the left or on the right branch. Consequently, we must return a list
of zippers. The |zippers| function below does exactly that. Its type is convoluted
because it works over |HolesAnn| (and therefore also for |SFix|, |SFixAnn| and |Holes|),
but it is conceptually simple: given a test for whether a hole of type |phi a|
is actually a hole in a recursive position, we return the list of possible
zippers for a value with holes. The definition is standard and we encourage the
interested reader to check the source code for more details (\Cref{chap:where-is-the-code}).

\begin{myhs}
\begin{code}
type Zipper' kappa fam phi h t
  = Zipper (CompoundCnstr kappa fam t) (HolesPhi kappa fam phi h) (HolesPhi kappa fam phi h) t

zippers  :: (forall a dot (Elem t fam) => h a -> Maybe (a :~: t))
         -> HolesPhi kappa fam phi h t -> [Zipper' kappa fam phi h t]
\end{code}
\end{myhs}

\subsubsection{Unification and Anti-Unification}
\label{sec:gp:simplistic-unif}

  Both unification and anti-unification algorithms make up an
important part of the vernacular of term-manipulation.
Unsurprisingly, we will also need to implement these features
into \genericssimpl{}. We use them extensively
in \Cref{chap:pattern-expression-patches}. This section provides an
overview of the (anti-)unification provided by \genericssimpl{}.

  Syntactic unification algorithms \cite{Robinson1965} receive as input
two terms |t| and |u| with variables and outputs substitutions
|sigma| such that |sigma t == sigma u|, when such |sigma| exists.
Anti-unification\cite{Plotkin1971}, on the other hand,
receives two terms |t| and |u| and outputs one term |r| and two substitutions
|sigma| and |phi| such that |t == sigma r| and |u = phi r|.

  With our current setup, we want to unify two terms of type |Holes kappa fam phi at|,
that is, two elements of the mutually recursive family |fam| with unification
variables of type |phi|. A substitution is given by:

\begin{myhs}
\begin{code}
type Subst kappa fam phi = Map (Exists phi) (Exists (Holes kappa fam phi))
\end{code}
\end{myhs}

  We need the existentials here in order to use the builtin, homogeneous, |Data.Map|.
\digress{we could write a custom heterogeneous key-value store, but I'm doubtful this
would be worth the trouble. |Data.Map| has excellent performance and has been
thoroughly tested.} Naturally,
when looking for the value associated with a key within the substitution
we will run into a type error as soon as we unwrap the |Exists|. There are
a number of solutions to this. For one, we could use the |sameTy| function
and ensure they are of the same type. Pragmatically though, as long as
we ensure we only insert keys |phi at| associated with values |Holes kappa fam phi at|,
the type indexes will never differ and we can safely call |unsafeCoerce| to
mitigate any performance overhead. We chose to use |unsafeCoerce| but stress
that it can be easily avoided with a call to |sameTy|.

\begin{myhs}
\begin{code}
substInsert  :: (Ord (Exists phi)) => Subst kappa fam phi -> phi at -> Holes kappa fam phi at
             -> Subst kappa fam phi

substLkup    :: (Ord (Exists phi)) => Subst kappa fam phi -> phi at -> Maybe (Holes kappa fam phi at)
\end{code}
\end{myhs}

  When attempting to solve a unification problem, there are two types
of failures that can occur: symbol clashes happen when we try to
unify different symbols, for example, |c x| is not unifiable with |c'
x| because |c /= c'|; and occurs-check errors are raised when there is
a loop in the substitution, For example, if we try to unify |c (c' x)|
with |c x|, we would have to substitute |x| for |c' x|, but this would
never terminate.  We encode these errors in the |UnifyErr| datatype,
making it easy for users of the library to catch these errors and
extract information from them.

\begin{myhs}
\begin{code}
data UnifyErr kappa fam phi where
  OccursCheck  :: [Exists phi] -> UnifyErr kappa fam phi
  SymbolClash  :: Holes kappa fam phi at -> Holes kappa fam phi at -> UnifyErr kappa fam phi
\end{code}
\end{myhs}

  The |unify| function has the type one would expect: given two terms
with unification variables of type |phi|, either they are not unifiable
or there exists a substitution that makes them equal.

\begin{myhs}
\begin{code}
unify  :: ( Ord (Exists phi) , EqHO phi) => Holes kappa fam phi at -> Holes kappa fam phi at
       -> Except (UnifyErr kappa fam phi) (Subst kappa fam phi)
\end{code}
\end{myhs}

  Our |unify| function is a constraint-based unifier which computes the most general
unifier in two phases: first it collects all the necessary equivalences, then it tries to
produce an idempotent substitution from the gathered equivalences.
We omit technical details regarding the implementation of the
unification algorithm and refer the reader to the existing literature~\cite{Robinson1965}.

% A substitution |[(x , Bin w z) , (w , Bin y y)]|
% can be minimized to |[(x , Bin (Bin y y) z) , (w , Bin y y)]|, where
% no metavariable in the image could be futher refined under the current
% substitution. Whenever a cycle is found, we simply break it in an arbitrary
% point, for example, |[(x , y) , (y , z) , (z , x)]| could be minimized to
% |[(x,z) , (y,z)]|.

  Anti-unification~\cite{Plotkin1971} is dual to unification. It is
the process of identifying the longest common prefix of two terms
For example, take |x = Bin (Bin 1 2) Leaf| and |y = Bin (Bin 1 3) (Bin 4
5)|, the term |Bin (Bin 1 a) b| is the least general generalization of
|x| and |y|. That is, there exist two instantiations of |a| and |b|
yielding |x| or |y|. The term |Bin c b| is also a generalization of
|x| and |y|, but it is not the \emph{least} general because to obtain
|x| or |y| we would have instantiate |c| as |Bin 1 2| or |Bin 1 3|,
and these terms can be further anti-unified. \Cref{fig:gp:antiunif}
illustrates the implementation of the syntactical anti-unification
algorithm.

\begin{figure}
\begin{myhs}
\begin{code}
lgg  :: (All Eq kappa) => Holes kappa fam phi at -> Holes kappa fam psi at
     -> Holes kappa fam (Holes kappa fam phi :*: Holes kappa fam psi) at
lgg (Prim x) (Prim y) =
  | weq (Proxy :: Proxy kappa) x y  = Prim x
  | otherwise                       = (Prim x :*: Prim y)
lgg x@(Roll rx) y@(Roll ry) = case zipSRep rx ry of
    Nothing  -> Hole (x :*: y)
    Just r   -> Roll (repMap (uncurry' lgg) r)
lgg x y = Hole (x :*: y)
\end{code}
\end{myhs}
\caption{Classic anti-unification algorithm~\cite{Plotkin1971},
producing the least general generalization of two trees.}
\label{fig:gp:antiunif}
\end{figure}

\section{Discussion}
\label{sec:gp:discussion}

  In this chapter we explored two different ways of writing generic
programs that must work over mutually recursive families. Looking back
at the spectrum of generic programming libraries, in
\Cref{fig:background:gplibraries}, we had a open hole for
\emph{code-based} approach with explicit recursion of any type, which
can be filled by \texttt{generics-mrsop}. When it comes to pattern
functors, although \texttt{regular} and \texttt{multirec} already
exist, using those libraries imposes a significant overhead
when compared to \genericssimpl{}, for they do not support
combinator-based generic programming.  The updated table of generic
programming libraries is given in \Cref{fig:gp:gplibraries}, where we
place our libraries in the spectrum of generic programming variants.

  Unfortunately, the \texttt{generics-mrsop} heavy usage of type
families triggers a memory leak in the compiler. This renders the
library unusable for large families of mutually recursive datatypes at
the time of writing this thesis. Luckily, however, we were able to
work around that by dropping the sums of products structure but
maintaining a combinator-based approach in \genericssimpl{}, which
enabled us to run our experiments with real-world data, as discussed
in \Cref{chap:experiments}.

  Although both \texttt{generics-mrsop} and \genericssimpl{} are
quite similar, the sums-of-products structure of \texttt{generics-mrsop}
is more convenient to program with. We must pattern match on less
cases (first on sums, then on products) and we have access to more
combinators to disect the sums-of-products structure. Now, that being said,
not all generic programming applications will require that level of
control and some could still get by without it. The \texttt{hdiff} 
(\Cref{chap:pattern-expression-patches}) is an example of the later.
Our first implementation with \texttt{generics-mrsop} was more natural,
but we were still able to implement it using \genericssimpl{}. 
The advantages of \genericssimpl{} are twofold: (A) it uses significantly less
type families and does not run into the bugs that \texttt{generics-mrsop} did
and (B) it is simpler to use and it piggybacks on a number of
familiar features from \texttt{GHC.Generics}.

  While developing the \texttt{generics-mrsop} and \genericssimpl{} libraries,
which happened under close collaboration with Alejandro Serrano, we also
explored a number of variants of these libraries such as
\texttt{kind-generics}~\cite{Serrano2018}, which enables a user to
represent almost any Haskell datatype generically, including
\emph{GADTs}. These are out of the scope of this thesis since we do
not require all of that expressivity to write our differencing
algorithms.


\begin{figure}\centering
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors  & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \multirow{2}{*}{\textbf{\genericssimpl{}}} & \multirow{2}{*}{\textbf{\texttt{generics-mrsop}}} \\
  Mutual Recursion      &   &   \\
\bottomrule
\end{tabular}
\caption{Updated spectrum of generic programming libraries.}
\label{fig:gp:gplibraries}
\end{figure}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
