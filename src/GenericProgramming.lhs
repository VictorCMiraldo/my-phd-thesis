
  The syntax of many programming languages,
for instance, is expressed naturally using a mutually recursive
family. Consider Haskell itself, one of the possibilities of an
expression is to be a |do| block, while a |do| block itself is
composed by a list of statements which may include expressions.

\begin{myhs}
\begin{code}
data Expr  = ... | Do [Stmt] | ...
data Stmt  = Assign Var Expr | Let Var Expr
\end{code}
\end{myhs}

Another example is found in HTML and XML documents. 
They are better described by a Rose tree, 
which can be described by this family of datatypes:

\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

The mutual recursion becomes apparent once one instantiaties |a| to some
ground type, for instance:

\begin{myhs}
\begin{code}
data RoseI  =  Fork Int ListI
data ListI  =  Nil | RoseI : ListI
\end{code}
\end{myhs}
  
  In order to implement our prototyes and explore our ideas on
differencing abstract syntax trees, we had to improve that support for
programming with mutually recursive families.  The
\texttt{generics-mrsop} is in the intersection of both the
expressivity of \texttt{multirec}, allowing the encoding of mutually
recursive families, with the convenience of the more modern
\texttt{generics-sop} style. In fact, it is worth noting that neither
of the aforementioned libraries \emph{compete} with out work. We
extend both in orthogonal directions, resulting in a new design
altogether, that takes advantage of some modern Haskell extensions
that the authors of the previous work could not enjoy, as discussed in
\Cref{sec:background:generic-programming},

\section{Explicit Fixpoints}
\label{sec:gp:explicitfix}

  In this section we will start to look at our approach, essentially
combining the techniques from the \texttt{regular} and
\texttt{generics-sop} libraries. Later we extend the constructions to
handle mutually recursive families instead of simple recursion. In any
way, we need an explicit description of which fields of a constructor
are recursive and which are not.

  Introducing information about the recursive positions in a type
requires more expressive codes than in \Cref{sec:background:explicitsop}, where
our \emph{codes} were a list of lists of types, which could be
anything. Instead, we will now have a list of lists of |Atom| to be
our codes:

\begin{myhs}
\begin{code}
data Atom = I | KInt | dots

type family    CodeFix (a :: Star)   ::  P [ P [Atom] ]

type instance  CodeFix (Bin Int)  =   P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

  Where |I| is used to mark the recursive positions and |KInt, dots|
are codes for a predetermined selection of primitive types, which we
refer to as \emph{opaque types}.
Favoring the simplicity of the presentation, we will stick with only
hard coded |Int| as the only opaque type in the universe. Later on,
in \Cref{sec:gp:konparameter}, we parametrize the whole development
by the choice of opaque types.

  We can no longer represent polymorphic types in this universe
-- the \emph{codes} themselves are not polymorphic.  Back in
\Cref{sec:background:explicitsop} we have defined |CodeSOP (Bin a)|, and this
would work for any |a|. This might seem like a disadvantage at first,
but it is in fact the opposite. This allows us to provide a deep
conversion for free and drops the need to carry constraints
around. Beyond doubt one needs to have access to the |CodeSOP a| when
converting a |Bin a| to its deep representation. By specifying the
types involved beforehand, we are able to get by without having to
carry all of the constraints we needed, for instance, for |gsize| at
the end of \Cref{sec:background:explicitsop}.  We can benefit the most from this
in the simplicity of combinators we are able to write, as shown in
\Cref{sec:gp:combinators}.

  Wrapping our |toFix| and |fromFix| isomorphism into a type class and
writing the instance that witnesses that |Bin Int| has a |CodeFix| is
straightforward. We ommit the |toFix| function as it is the opposite
of |fromFix|:

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

  In order to define |RepFix| we just need a way to map an |Atom| into |Star|.
Since an atom can be either an opaque type, known statically, or some other
type that will be used as a recursive position later on, we simply receive
it as another parameter. The |NA| datatype relates an |Atom| to its semantics:

\begin{myhs}
\begin{code}
data NA :: Star -> Atom -> Star where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt

newtype  RepFix a x = Rep { unRep :: NS (NP (NA x)) (CodeFix a) }
\end{code}
\end{myhs}

  It is an interesting exercise to implement the |Functor| instance
for |(RepFix a)|.  We were only able to lift it to a functor by
recording the information about the recursive positions. Otherwise,
there would be no way to know where to apply |f| when defining |fmap
f|.

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
stating that |n < length sum|. |Lkup| performs list lookup at the type level.
In order to improve type error messages, we generate a |TypeError| whenever we
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

  Now we are able to easily pattern match and inject into and from
generic values.  Unfortunately, matching on |Tag| requires describing
in full detail the shape of the generic value using the elements of
|Constr|. Using pattern synonyms~\cite{Pickering2016} we can define
those patterns once and for all, and give them more descriptive names.
For example, here are the synonyms describing the constructors |Bin|
and |Leaf|. \footnote{Throughout this
paper we use the syntax |(Pat C)| to refer to the pattern describing a
view for constructor |C|.}

\begin{myhs}
\begin{code}
pattern (Pat Leaf)  x    = Tag CZ       (NA_K x :* NP0)
pattern (Pat Bin)   l r  = Tag (CS CZ)  (NA_I l :* NA_I r :* NP0)
\end{code}
\end{myhs}

The functions that perform the pattern matching and injection are the
|inj| and |sop| below.

\begin{myhs}
\begin{code}
inj  :: View    sop  x  -> RepFix  sop  x
sop  :: RepFix  sop  x  -> View    sop  x
\end{code}
\end{myhs}

  Having the core of the \emph{sums-of-products} universe defined,
we can turn our attention to writing the combinators that the programmer
will use. These will be defined by induction on the |CodeFix| instead of
having to rely on instances, like in \Cref{sec:background:patternfunctors}. 
For instance, lets look at |compos|, which applies a function |f| everywhere 
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
everywhere else.
  
\paragraph{Converting to a deep representation.}  The |fromFix|
function returns a shallow representation. But by constructing the
least fixpoint of |RepFix a| we can easily obtain the
deep\index{Generic Programming!Deep} encoding for free, by simply
recursively translating each layer of the shallow encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (GenericFix a) => a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . fromFix
\end{code}
\end{myhs}

  So far, we handle the same class of types as the
\texttt{regular}~\cite{Noort2008} library, but we are imposing the
representation to follow a \emph{sum-of-products} structure by the
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
  where
    crushFix :: Fix (RepFix a) -> b
    crushFix = cat . elimNS (elimNP go) . unFix

    go (NA_I x) = crushFix x
    go (NA_K i) = k i
\end{code}
\end{myhs}
\caption{Generic |crush| combinator}
\label{fig:crush}
\end{figure}

  Sometimes we actually want to consume a value and produce
a single value, but do not need the full expressivity of |fold|. 
Instead, if we know how to consume the opaque types and combine
those results, we can consume any |GenericFix| type using |crush|,
which is defined in \cref{fig:crush}. The behavior of |crush|
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

  At this point we have combined the insight from
the \texttt{regular} library of keeping track of recursive positions
with the convenience of the \texttt{generics-sop} for enforcing a
specific \emph{normal form} on representations. By doing so, we were
able to provide a \emph{deep} encoding for free. This essentially frees
us from the burden of maintaining complicated constraints needed for
handling the types within the topmost constructor. The information
about the recursive position allows us to write neat combinators like
|crush| and |compos| together with a convenient |View| type for
easy generic pattern matching. The only thing keeping us from
handling real life applications is the limited form of recursion. When
a user requires a generic programming library, chances are they need
to traverse and consume mutually recursive structures.

\section{Mutual Recursion}
\label{sec:gp:family}

  Conceptually, going from regular types (\Cref{sec:gp:explicitfix})
to mutually recursive families is simple. We just need to be able to
reference not only one type variable, but one for each element in the
family.  This is usually~\cite{Loh2011,Altenkirch2015} done by adding
an index to the recursive positions that represents which member of
the family we are recursing over.  As a running example, we use the
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
                             , (P [ (P []), P [ I Z, I (S Z)]])])
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
|NA| to the new |Atom|s. In order to interpret any |Atom| into |Star|,
we now need a way to interpret the different recursive positions. This
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
|FamRose|. In fact, we are simply performing a type level lookup in
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
relation explicit. The |Family| type class below realizes this
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
specify how to translate \emph{each} of the members of the family back
and forth the generic representation. This translation needs to know
which is the index of the datatype we are converting between in each
case, hence the additional |SNat ix| parameter. Pattern matching on
this singleton~\cite{Eisenberg2012} type informs the compiler about
the shape of the |Nat| index. Its definition is:

\begin{myhs}
\begin{code}
data SNat (n :: Nat) where
  SZ  ::              SNat (P Z)
  SS  ::  SNat n  ->  SNat ((P S) n)
\end{code}
\end{myhs}

  For example, in the case of
our family of rose trees, |fromMRec| has the following shape:

\begin{myhs}
\begin{code}
fromMRec SZ       (El (Fork x ch))  = Rep (Here (NA_K x :* NA_I ch :* NP0))
fromMRec (SS SZ)  (El [])        = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))  = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
\end{code}
\end{myhs}

  By pattern matching on the index, the compiler knows which family
member to expect as a second argument. This then allows the pattern
matching on the |El| to typecheck.

The limitations of the Haskell type system lead us to introduce |El|
as an intermediate datatype. Our |fromMRec| function does not take a
member of the family directly, but an |El|-wrapped one. However, to
construct that value, |El| needs to know its parameters, which amounts
to the family we are embedding our type into and the index in that
family. Those values are not immediately obvious, but we can use
Haskell's visible type application~\cite{EisenbergWA16} to work around
it. The |into| function injects a value into the corresponding |El|:

\begin{myhs}
\begin{code}
into  :: forall fam ty ix dot (ix ~ Idx ty fam , Lkup fam ix ~ ty) => ty -> El fam ix
into  = El
\end{code}
\end{myhs}

%format (TApp a) = "\HS{@}" a 

where |Idx| is a closed type family
implementing the inverse of |Lkup|, that is, obtaining the index of
the type |ty| in the list |fam|. Using this function we can turn a
|[Rose Int]| into its generic representation by writing |fromMRec
. into (TApp FamRose)|. The type application |(TApp FamRose)| is
responsible for fixing the mutually recursive family we are working
with, which allows the type checker to reduce all the constraints and
happily inject the element into |El|.
  
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
declare on which element of the family it is working on.

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
to manipulate them, which is more complex than what meets the eye. 
This could greatly hinder the usability of the library.

By looking a bit more closely, we find that we are not losing any type-safety
by allowing codes which reference an arbitrary number of recursive positions.
Users of our library are allowed to write the previous ill-defined code, but
when trying to write \emph{values} of the representation of that code, the
|Lkup| function detects the out-of-bounds index, raising a type error and
preventing the program from compiling.

\subsection{Parametrized Opaque Types}
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
|Int|s and |Float|s, so why bother ourselves with possibly ill-formed
representations and pattern matches which should never be reached?
\end{enumerate}

Our solution is to \emph{parametrize} |Atom|, 
giving programmers the choice of opaque types:

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

type  RepMRec (kappa :: kon -> Star) (phi :: Nat -> Star) (c :: [[Atom kon]])
      = NS (NP (NA kappa phi)) c
\end{code}
\end{myhs}

The |NA_K| constructor in |NA| makes use of an additional argument |kappa|.
The problem is that we are defining the code for the set of opaque types by
a specific kind, such as |Numeric| above. On the other hand, values which
appear in a field must have a type whose kind is |Star|. Thus, we require a mapping
from each of the codes to the actual opaque type they represent, this
is exactly the \emph{opaque type interpretation} |kappa|. Here is the
datatype interpreting |NumericK| into ground types:

\begin{myhs}
\begin{code}
data NumericI :: NumericK -> Star where
  IInt      :: Int      -> NumericI KInt
  IInteger  :: Integer  -> NumericI KInteger
  IFloat    :: Float    -> NumericI KFloat
\end{code}
\end{myhs}

The last piece of our framework which has to be updated to support
different sets of opaque types is the |Family| type class, as given in
\Cref{fig:int}. This type class provides an interesting use case for
the new dependent features in Haskell; both |kappa| and |codes| are
parametrized by an implicit argument |kon| which represents the set of
opaque types.

\begin{figure}
\begin{myhs}
\begin{code}
class Family (kappa :: kon -> Star) (fam :: [Star]) (codes :: [[[Atom kon]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix -> RepMRec kappa (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec kappa (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}
\caption{|Family| type class with support for different opaque types}
\label{fig:int}
\end{figure}

We stress that the parametrization over opaque types does \emph{not}
mean that we can use only closed universes of opaque types. It is
possible to provide an \emph{open} representation by choosing |(Star)|
-- the whole kind of Haskell's ground types -- as argument to
|Atom|. As a consequence, the interpretation ought to be of kind |Star
-> Star|, as follows:

\begin{myhs}
\begin{code}
data Value :: Star -> Star where
  Value :: t -> Value t
\end{code}
\end{myhs}

In order to use |(Star)| as an argument to a type, we must enable
the \texttt{TypeInType} language extension~\cite{Weirich2013,Weirich2017}.

%  All the generic operations implemented use
%parametrized version of |Atom|s and representations described in this section.
%For convenience we also provide a basic set of opaque types which includes the
%most common primitive datatypes.

\subsection{Some Useful Combinators}
\label{sec:gp:combinators}

  The advantages or a \emph{code based} approach to generic progrmming
becomes evident when we look at the generic combinators that
\texttt{generics-mrsop} provides.  We refer the reader for the
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

  More interesting than a map perhaps is a general eliminator. In
order to destruct a |RepMRec kappa phi c| we need a way for
eliminating every recursive position or opaque type inside the
representation and a way of combining these results.

\begin{myhs}
\begin{code}
elimRep  ::  (forall k   dot kappa  k   -> a)  ->  (forall ix  dot phi    ix  -> a)  ->  ([a] -> b) 
         ->  RepMRec kappa phi c -> b
elimRep f_K f_I cat = elimNS cat (elimNP (elimNA f_K f_I))
\end{code}
\end{myhs}

  Another handy operator, particularly when combined with |bimapRep| is
the |zipRep|, that works just like a regular |zip|. Our |zipRep|
will attempt to put two values of a representation ``side-by-side'', as long
as they are constructed with the same injection into the $n$-ary sum, |NS|.

\begin{myhs}
\begin{code}
zipRep  ::  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c
        ->  Maybe (RepMRec (kappa1 :*: kappa2) (phi1 :*: phi2) c)
zipRep r s = case (sop r , sop s) of
   (Tag cr pr , Tag cs ps) -> case testEquality cr pr of
      Just Refl -> inj cr <$$> zipWithNP zipAtom pr ps
\end{code}
\end{myhs}

  \victor{explain |testEquality|}

  Finally, we can start assembling these basic building blocks into
more practical functionality. For example, \Cref{fig:genericeq} shows
the definition generic propositional equality using \texttt{generics-mrsop}.
  
\begin{figure}
\begin{myhs}
\begin{code}
geq  ::  (Family kappa fam codes) 
     =>  (forall k dot kappa k -> kappa k -> Bool) 
     ->  El fam ix -> El fam ix -> Bool
geq eq_K x y = go (deepFrom x) (deepFrom y)
  where go (Fix x) (Fix y) 
      =  maybe False (elimRep (uncurry eq_K) (uncurry go) and) 
      $  zipRep x y  
\end{code} %$
\end{myhs}
\caption{Generic equality}
\label{fig:genericeq}
\end{figure}

\section{Template Haskell}
\label{sec:gp:templatehaskell}

  Having a convenient and robust way to get the |Family| instance for
a given selection of datatypes is paramount for the usability of our
library. In a real scenario, a mutually recursive family
may consist of many datatypes with dozens of
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
data Decl  var = dots
data Prog  var = dots
deriveFamily (tht (Prog String))
\end{code}
\end{myhs}

  The |deriveFamily| takes care of unfolding the (type level) recursion until it
reaches a fixpoint.  In this case, the type synonym |FamProgString = P [Prog
String , dots]| will be generated, together with its |Family|
instance. Optionally, one can also pass along a custom function to decide
whether a type should be considered opaque. By default, it uses a
selection of Haskell built-in types as opaque types.

\subsection{Unfolding the Family}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a
single member is conceptually divided into two disjoint
processes. First we unfold all definitions and follow all the
recursive paths until we reach a fixpoint. At that moment we know that
we have discovered all the types in the family. Second, we translate
the definition of those types to the format our library expects.
During the unfolding process we keep a key-value map in a |State|
monad, keeping track of the types we have seen, the types we have seen
\emph{and} processed and the indices of those within the family.

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

  The first thing that happens is registering that we seen the type
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
perform some amount of $\beta$-reduction at the type level before
inspecting its fields.  The rest of the process is the same that for
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
type  FamRoseInt
      = P [ Rose Int                    , [Rose Int] ]
type  CodesRoseInt
      = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
\end{code}
\end{myhs}

  Pattern synonyms are useful for convenient pattern matching and injecting into
the |View| datatype. We produce two different kinds of pattern synonyms.
First, synonyms for generic representations, one per constructor. Second,
synonyms which associate each type in the recursive family with their
position in the list of codes.

\vspace{.1cm}
\begin{myhs}
%format forkP = "\HT{\overline{Fork}}" 
%format nilP  = "\HT{\overbar{[]}}" 
%format consP = "\HT{\overline{:}}" 
\begin{code}
pattern forkP x xs  = Tag SZ       (NA_K x :* NA_I xs :* NP0)
pattern nilP        = Tag SZ       NP0
pattern x consP xs  = Tag (SS SZ)  (NA_I x :* NA_I xs :* NP0)
pattern (Pat RoseInt)      = SZ
pattern (Pat ListRoseInt)  = SS SZ
\end{code}
\end{myhs}

  The actual |Family| instance is exactly as the one shown in
\Cref{sec:gp:family}

\begin{myhs}
\begin{code}
instance Family Singl FamRoseInt CodesRoseInt where dots
\end{code}
\end{myhs}


\section{Metadata}
\label{sec:gp:metadata}

  There is one final ingredient missing to make
\texttt{generics-mrsop} fully usable in practice. We must to maintain
the \emph{metadata} information of our datatypes.  This metadata
includes the datatype name, the module where it was defined, and the
name of the constructors. Without this information we would never be
able to pretty print the generic code in a satisfactory way. This
includes conversion to semi-structured formats, such as JSON, or
actual pretty printing.

  Like in \texttt{generics-sop}~\cite{deVries2014}, having the code
for a family of datatypes available allows for a completely separate
treatment of metadata. This is yet another advantage of the
sum-of-products approach when compared to the more traditional pattern
functors. In fact, our handling of metadata is heavily inspired from
\texttt{generics-sop}, so much so that we will start by explaining a
simplified version of their handling of metadata, and then outline the
differences to our approach.

  The general idea is to store the meta information following the
structure of the datatype itself. So, instead of data, we keep track
of the names of the different parts and other meta information that
can be useful. It is advantageous to keep metadata separate from the
generic representation as it would only clutter the definition of
generic functionality.  This information is tied to a datatype by
means of an additional type class |HasDatatypeInfo|.  Generic
functions may now query the metadata by means of functions like
|datatypeName|, which reflect the type information into the term
level.  The definitions are given in \Cref{fig:sopmeta}.

\begin{figure}
\begin{myhs}
\begin{code}
data DatatypeInfo :: [[Star]] -> Star where
  ADT  :: ModuleName -> DatatypeName -> NP  ConstrInfo cs       
       -> DatatypeInfo cs
  New  :: ModuleName -> DatatypeName ->     ConstrInfo (P [c])  
       -> DatatypeInfo (P [ P [ c ]])

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
\caption{Definitions related to metadata from \texttt{generics-sop}}
\label{fig:sopmeta}
\end{figure}

  Our library uses the same approach to handle metadata. In fact, the
code remains almost unchanged, except for adapting it to the larger
universe of datatypes we can now handle. Unlike \texttt{generic-sop},
our list of lists representing the sum-of-products structure does not
contain types of kind |Star|, but |Atom|s. All the types representing
metadata at the type level must be updated to reflect this new
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
for types which are the result of type level applications, such as
|Rose Int| and |[Rose Int]|.  The shape of the metadata information in
|DatatypeInfo|, a module name plus a datatype name, is not enough to
handle these cases.  We replace the uses of |ModuleName| and
|DatatypeName| in |DatatypeInfo| by a richer promoted type |TypeName|,
which can describe applications, as required.

\begin{myhs}
\begin{code}
data TypeName  =  ConT ModuleName DatatypeName
               |  TypeName :@: TypeName
data DatatypeInfo :: [[Atom kon]] -> Star where
  ADT  ::  TypeName  -> NP  ConstrInfo cs
       ->  DatatypeInfo cs
  New  ::  TypeName  ->     ConstrInfo (P [c])
       ->  DatatypeInfo (P [ P [ c ]])
\end{code}
\end{myhs}

  The most important difference to \texttt{generics-sop}, perhaps, 
is that the metadata is not defined for a single type, but
for a type \emph{within} a family. This is reflected in the new signature of 
|datatypeInfo|, which receives proxies for both the family and the type.
The type equalities in that signature reflect the fact that the given type
|ty| is included with index |ix| within the family |fam|. This step is needed
to look up the code for the type in the right position of |codes|.
\begin{myhs}
\begin{code}
class (Family kappa fam codes)
       =>  HasDatatypeInfo kappa fam codes ix 
       |   fam -> kappa codes where
  datatypeInfo  ::  (ix ~ Idx ty fam , Lkup ix fam ~ ty)
                =>  Proxy fam -> Proxy ty
                ->  DatatypeInfo (Lkup ix codes)
\end{code}
\end{myhs}

  The Template Haskell will then generate something similar to
the instance below for the first type in the family, |Rose Int|:

\begin{myhs}
\begin{code}
instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _ 
    =  ADT (ConT "E" "Rose" :@: ConT "Prelude" "Int")
    $  (Constructor "Fork") :* NP0
\end{code} %$
\end{myhs}

\subsection{Revisiting \texttt{GDiff}}

\victor{How about we show gdiff in \texttt{generics-mrsop}?}
