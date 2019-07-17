
The novelty in our work is in the
intersection of both the expressivity of \texttt{multirec}, allowing
the encoding of mutually recursive families, with the convenience of
the more modern \texttt{generics-sop} style. In fact, it is worth
noting that neither of the aforementioned libraries \emph{compete}
with out work. We extend both in orthogonal directions, resulting in a
new design altogether, that takes advantage of some modern Haskell
extensions that the authors of the previous work could not enjoy. In
the next few paragraphs let us take a look at the different aspects of
the design space of generic programming libraries in Haskell.


\paragraph{Mutually recursive datatypes.}

We have described several axes taken by different approaches to
generic programming in Haskell. Unfortunately, most of the approaches
restrict themselves to \emph{regular} types, in which recursion always
goes into the \emph{same} datatype, which is the one being
defined. Sometimes one would like to have the mutually recursive
structure handy, though.  The syntax of many programming languages,
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

The \texttt{multirec} library~\cite{Yakushev2009} is a generalization
of \texttt{regular} which handles mutually recursive families using
this very technique.  The mutual recursion is central to some
applications, in particular, to our application of computing
differences over values of abstract syntax trees.

In fact, the need for \texttt{generics-mrsop} arises from the desire
of having the concise structure that \emph{codes} give to the
\emph{representations}, together with the information for recursive
positions in a mutually recursive setting.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



\subsection{Explicit Fixpoints}
\label{sec:explicitfix}

  In this section we will start to look at our approach, essentially
combining the techniques from the \texttt{regular} and \texttt{generics-sop}
libraries. Later we extend the constructions to handle mutually recursive
families instead of simple recursion. As we discussed in the introduction,
a fixpoint view over generic functionality is required
to implement some functionality like the |Zipper| generically.
In other words, we need an explicit description of which fields of
a constructor are recursive and which are not.

  Introducing information about the recursive positions in a type
requires more expressive codes than in \Cref{sec:explicitsop}, where
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
in \Cref{sec:konparameter}, we parametrize the whole development
by the choice of opaque types.

  We can no longer represent polymorphic types in this universe
-- the \emph{codes} themselves are not polymorphic.  Back in
\Cref{sec:explicitsop} we have defined |CodeSOP (Bin a)|, and this
would work for any |a|. This might seem like a disadvantage at first,
but it is in fact the opposite. This allows us to provide a deep
conversion for free and drops the need to carry constraints
around. Beyond doubt one needs to have access to the |CodeSOP a| when
converting a |Bin a| to its deep representation. By specifying the
types involved beforehand, we are able to get by without having to
carry all of the constraints we needed, for instance, for |gsize| at
the end of \Cref{sec:explicitsop}.  We can benefit the most from this
in the simplicity of combinators we are able to write, as shown in
\Cref{sec:combinators}.

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
  fromFix (Leaf x) 
    = Rep (         Here  (NA_K x  :* NP0))
  fromFix (Bin l r)
    = Rep (There (  Here  (NA_I l  :* NA_I r :* NP0)))
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

newtype  RepFix a x
         = Rep { unRep :: NS (NP (NA x)) (CodeFix a) }
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
respective product of fields by the |View| type. 

\begin{myhs}
\begin{code}
data Nat = Z | S Nat

data View :: [[ Atom ]] -> Star -> Star where
  Tag  ::  Constr n t -> NP (NA x) (Lkup t n) ->  View t x
\end{code}
\end{myhs}

\noindent A value of |Constr n
sum| is a proof that |n| is a valid constructor for |sum|,
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

  The |View| type and the hability to split a value into a choice
of constructor and its fields is very handy for writing generic functions,
as we can see in \Cref{sec:alphaequivalence}.

  Having the core of the \emph{sums-of-products} universe defined,
we can turn our attention to writing the combinators that the programmer
will use. These will be defined by induction on the |CodeFix| instead of
having to rely on instances, like in \Cref{sec:patternfunctors}. 
For instance, lets look at |compos|, which applies a function |f| everywhere 
on the recursive structure.

\begin{myhs}
\begin{code}
compos :: (GenericFix a) => (a -> a) -> a -> a
compos f = toFix . fmap f . fromFix
\end{code}
\end{myhs}

  Although more interesting in the mutually recursive setting,
\Cref{sec:family}, we can illustrate its use for traversing a
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
  
\paragraph{Converting to a deep representation.}  The |fromFix| function
returns a shallow representation. But by constructing the least
fixpoint of |RepFix a| we can easily obtain the deep encoding for
free, by simply recursively translating each layer of the shallow
encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (GenericFix a) => a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . fromFix
\end{code}
\end{myhs}

  So far, we handle the same class of types
as the \texttt{regular}~\cite{Noort2008} library, but we are imposing 
the representation to follow a \emph{sum-of-products} structure
by the means of |CodeFix|. Those types are guaranteed to have an
initial algebra, and indeed, the generic fold is defined
as expected: 

\begin{myhs}
\begin{code}
fold :: (RepFix a b -> b) -> Fix (RepFix a) -> b
fold f = f . fmap (fold f) . unFix
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
crush  ::  (GenericFix a)
       =>  (forall x dot Int -> b) -> ([b] -> b)
       ->  a -> b
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

  Let us take a step back and reflect upon what we have achieved
so far. We have combined the insight from
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Mutual Recursion}
\label{sec:family}

  Conceptually, going from regular types (\Cref{sec:explicitfix}) to
mutually recursive families is simple. We just need to be able to reference
not only one type variable, but one for each element in the family.
This is usually~\cite{Loh2011,Altenkirch2015} done by adding an index to the
recursive positions that represents which member of the family we are recursing over.
As a running example, we use the \emph{rose tree} family from the
introduction.
\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

The previously introduced |CodeFix| is not expressive enough to
describe this datatype. In particular, when we try to write
|CodeFix (Rose Int)|, there is no immediately recursive appearance of
|Rose| itself, so we cannot use the atom |I| in that position. Furthermore
|[Rose a]| is not an opaque type either, so we cannot
use any of the other combinators provided by |Atom|. We would
like to record information about |[Rose Int]| referring to itself via another datatype.

Our solution is to move from codes of datatypes to \emph{codes for families of
datatypes}. We no longer talk about |CodeFix (Rose Int)| or
|CodeFix [Rose Int]| in isolation. Codes only make sense
within a family, that is, a list of types. Hence, we talk about
the codes of the two types in the family:
|CodeMRec (P [Rose Int,  [Rose Int]])|. 
Then we extend the language
of |Atom|s by appending to |I| a natural number which specifies 
the member of the family to recurse into:
\begin{myhs}
\begin{code}
data Atom  = I Nat | KInt | dots
\end{code}
\end{myhs}
The code of this recursive family of datatypes can finally be described as:
\begin{myhs}
\begin{code}
type FamRose           = P [Rose Int, [Rose Int]]

type CodeMRec FamRose  = (P  [ (P [ (P [ KInt, I (S Z)])])
                             , (P [ (P []), P [ I Z, I (S Z)]])])
\end{code}
\end{myhs}
Let us have a closer look at the code for |Rose Int|, which appears in the
first place in the list. There is only one constructor which has an |Int| field,
represented by |KInt|, and another in which we recurse via the second member of 
our family (since lists are 0-indexed, we represent this by |S Z|). Similarly,
the second constructor of |[Rose Int]| points back to both |Rose Int|
using |I Z| and to |[Rose Int]| itself via |I (S Z)|.

  Having settled on the definition of |Atom|, we now need to adapt |NA| to
the new |Atom|s. In order to interpret any |Atom| into |Star|, we now need
a way to interpret the different recursive positions. This information is given
by an additional type parameter |phi| that maps natural numbers into types.
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
type  RepMRec (phi :: Nat -> Star) (c :: [[Atom]])
      = NS (NP (NA phi)) c
\end{code}
\end{myhs}
The only piece missing here is tying the recursive knot. If we want our
representation to describe a family of datatypes, the obvious choice
for |phi n| is to look up the type at index |n| in |FamRose|. In fact,
we are simply performing a type level lookup in the family,
so we can reuse the |Lkup| from \Cref{sec:explicitfix}.

In principle, this is enough to provide a ground representation for the family
of types. Let |fam| be a family of types, like
|(P [Rose Int, [Rose Int]])|, and |codes| the corresponding list
of codes. Then the representation of the type at index |ix| in the list |fam|
is given by:
\begin{myhs}
\begin{code}
RepMRec (Lkup fam) (Lkup codes ix)
\end{code}
\end{myhs}
This definition states that to obtain the representation of the type at index
|ix|, we first lookup its code. Then, in the recursive positions we interpret
each |I n| by looking up the type at that index in the original family. This
gives us a \emph{shallow} representation. As an example, below is the expansion
for index 0 of the rose tree family. Note how it is isomorphic to the representation
that \texttt{GHC.Generics} would have chosen for |Rose Int|:
\begin{myhs}
\begin{code}
 RepMRec  (Lkup FamRose) (Lkup (CodeMRec FamRose) Z)
  =    RepMRec  (Lkup FamRose)      (P [ (P [ KInt, I (S Z)])])
  =    NS (NP (NA (Lkup FamRose)))  (P [ (P [ KInt, I (S Z)])])
  ==   K1 R Int :*: K1 R (Lkup FamRose (S Z))
  =    K1 R Int :*: K1 R [Rose Int] 
  =    RepGen (Rose Int)
\end{code}
\end{myhs}

Unfortunately, Haskell only allows saturated, that is, fully-applied type
families. Hence, we cannot partially apply |Lkup| like we did it in the example above.
As a result, we need to introduce an intermediate datatype |El|,
\begin{myhs}
\begin{code}
data El :: [Star] -> Nat -> Star where
  El :: Lkup fam ix -> El fam ix
\end{code}
\end{myhs}
The representation of the family |fam| at index |ix| is thus given by
|RepMRec (El fam) (Lkup codes ix)|. We only need to use |El| in the first
argument, because that is the position in which we require partial application.
The second position has |Lkup| already fully-applied, and can stay as is.

  We still have to relate a family of types to their respective codes.
As in other generic programming approaches, we want to make their
relation explicit. The |Family| type class below realizes this
relation, and introduces functions to perform the conversion between
our representation and the actual types. Using |El| here spares us from using
a proxy for |fam| in |fromMRec| and |toMRec|:

\begin{myhs}
\begin{code}
class Family (fam :: [Star]) (codes :: [[[Atom]]]) where
  
  fromMRec  ::  SNat ix  
            ->  El fam ix -> RepMRec (El fam) (Lkup codes ix)
  toMRec    ::  SNat ix
            ->  RepMRec (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}

One of the differences between other approaches and ours is that we do not
use an associated type to define the |codes| for the family
|fam|. One of the reasons to choose this path is that it alleviates the
burden of writing the longer |CodeMRec fam| every time we want to
refer to |codes|. Furthermore, there are types like lists which appear in
many different families, and in that case it makes sense to speak about a
relation instead of a function. In any case, we can choose the other point of
the design space by moving |codes| into an associated type or introduce a
functional dependency |fam -> codes|.

Since now |fromMRec| and |toMRec| operate on families, we have
to specify how to translate \emph{each} of the members of the family back and
forth the generic representation. This translation needs to know which is the
index of the datatype we are converting between in each case,  hence the
additional |SNat ix| parameter. Pattern matching on this singleton~\cite{Eisenberg2012} 
type informs the compiler about the shape of the |Nat| index. Its definition is:
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
fromMRec SZ       (El (Fork x ch))
  = Rep (          Here (NA_K x :* NA_I ch :* NP0))
fromMRec (SS SZ)  (El [])           
  = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))     
  = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
\end{code}
\end{myhs}
By pattern matching on the index, the compiler knows which family member
to expect as a second argument. This then allows the pattern matching on
the |El| to typecheck.

The limitations of the Haskell type system lead us to introduce |El| as an
intermediate datatype. Our |fromMRec| function does not take a member of
the family directly, but an |El|-wrapped one. However, to construct that value,
|El| needs to know its parameters, which amounts to the family we are 
embedding our type into and the index in that family. Those values are not
immediately obvious, but we can use Haskell's visible type
application~\cite{EisenbergWA16} to work around
it. The |into| function injects a value into the corresponding |El|:

\begin{myhs}
\begin{code}
into  :: forall fam ty ix dot (ix ~ Idx ty fam , Lkup fam ix ~ ty) 
      => ty -> El fam ix
into  = El
\end{code}
\end{myhs}

%format (TApp a) = "\HS{@}" a
where |Idx| is a closed type family implementing the inverse of |Lkup|, that is,
obtaining the index of the type |ty| in the list |fam|. Using this function
we can turn a |[Rose Int]| into its generic representation by writing
|fromMRec . into (TApp FamRose)|. The type application |(TApp FamRose)| is responsible
for fixing the mutually recursive family we are working with, which
allows the type checker to reduce all the constraints and happily inject the element
into |El|.
  
\paragraph{Deep representation.} In \Cref{sec:explicitfix} we have described a
technique to derive deep representations from shallow representations. We can
play a very similar trick here. The main difference is the definition of the
least fixpoint combinator, which receives an extra parameter of kind |Nat| indicating
which |code| to use first:
\begin{myhs}
\begin{code}
newtype Fix (codes :: [[[Atom]]]) (ix :: Nat)
  = Fix { unFix :: RepMRec (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}
Intuitively, since now we can recurse on different positions, we need to keep
track of the representations for all those positions in the type. This is the
job of the |codes| argument. Furthermore, our |Fix| does not represent a single
datatype, but rather the \emph{whole} family. Thus, we need each value to have an
additional index to declare on which element of the family it is working on.

As in the previous section, we can obtain the deep representation by iteratively
applying the shallow representation. Earlier we used |fmap| since the |RepFix|
type was a functor. |RepMRec| on the other hand cannot be given a |Functor|
instance, but we can still define a similar function |mapRec|,
\begin{myhs}
\begin{code}
mapRep  ::  (forall ix dot phi1 ix -> phi2 ix)
        ->  RepMRec phi1 c -> RepMRec phi2 c
\end{code}
\end{myhs}
This signature tells us that if we want to change the |phi1| argument in 
the representation, we need to provide a natural transformation from
|phi1| to |phi2|, that is, a function which works over each
possible index this |phi1| can take and does not change this index. 
This follows from |phi1| having kind |Nat -> Star|. 
\begin{myhs}
\begin{code}
deepFrom  ::  Family fam codes
          =>  El fam ix -> Fix (RepMRec codes ix)
deepFrom = Fix . mapRec deepFrom . fromMRec
\end{code}
\end{myhs}

\paragraph{Only well-formed representations are accepted.}
At first glance, it may seem like the |Atom| datatype gives too much freedom:
its |I| constructor receives a natural number, but there is no apparent static check
that this number refers to an actual member of the recursive family we
are describing. For example, the list of codes
|(P [ (P [ (P [ KInt, I (S (S Z))])])])|  is accepted by the compiler
although it does not represent any family of datatypes. 

A direct solution to this problem is to introduce yet another index, this
time in the |Atom| datatype, which specifies which indices are allowed.
The |I| constructor is then refined to take not any natural number, but only
those which lie in the range -- this is usually known as |Fin n|.
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
\label{sec:konparameter}

Up to this point we have considered |Atom| to include a predetermined selection of
\emph{opaque types}, such as |Int|, each of them represented by one of the
constructors other than |I|. This is far from ideal, for two conflicting reasons:

\begin{enumerate}
\item The choice of opaque types might be too narrow. For example, the user
of our library may decide to use |ByteString| in their datatypes. Since that
type is not covered by |Atom|, nor by our generic approach, this implies that
\texttt{generics-mrsop} becomes useless to them.
\item The choice of opaque types might be too wide. If we try to encompass any
possible situation, we end up with a huge |Atom| type. But for a
specific use case, we might be interested only in |Int|s and |Float|s, so why
bother ourselves with possibly ill-formed representations and pattern matches
which should never be reached?
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
The last piece of our framework which has to be updated to support different
sets of opaque types is the |Family| type class,
as given in \Cref{fig:int}. This type class provides an
interesting use case for the new dependent features in Haskell; both |kappa|
and |codes| are parametrized by an implicit argument |kon| which represents
the set of opaque types.
\begin{figure*}
\begin{myhs}
\begin{code}
class Family (kappa :: kon -> Star) (fam :: [Star]) (codes :: [[[Atom kon]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix -> RepMRec kappa (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec kappa (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}
\caption{|Family| type class with support for different opaque types}
\label{fig:int}
\end{figure*}

We stress that the parametrization over opaque types does \emph{not}
mean that we can use only closed universes of opaque types. It is possible
to provide an \emph{open} representation by choosing |(Star)| -- the whole
kind of Haskell's ground types -- as argument to |Atom|. As a consequence,
the interpretation ought to be of kind |Star -> Star|, as follows:
\begin{myhs}
\begin{code}
data Value :: Star -> Star where
  Value :: t -> Value t
\end{code}
\end{myhs}
In order to use |(*)| as an argument to a type, we are required to enable
the \texttt{TypeInType} language extension~\cite{Weirich2013,Weirich2017}.

%  All the generic operations implemented use
%parametrized version of |Atom|s and representations described in this section.
%For convenience we also provide a basic set of opaque types which includes the
%most common primitive datatypes.

\subsection{Combinators}
\label{sec:combinators}

  In the remainder of this section we wish to showcase a selection of particularly
powerful combinators that are simple to define by exploiting the
\emph{sums-of-products} structure coupled with the mutual recursion information.
Defining the same combinators in \texttt{multirec} would produce much more complicated
code. In \texttt{GHC.Generics} these are even impossible to write due to the
absence of recursion information.

For the sake of fostering intuition instead of worrying about
notational overhead, we write values of |RepMRec kappa phi c| just like
we would write normal Haskell values. They have the same \emph{sums-of-products} 
structure anyway. Whenever a function is defined
using the |^=| symbol, |C x_1 dots x_n| will stand for a value of the corresponding
|RepMRec kappa phi c|, that is, |There (dots (Here (x_1 :* dots :* x_n :* NP0)))|. 
Since each of these |x_1 dots x_n| might be a recursive type or an opaque type,
whenever we have two functions |f_I| and |f_K| in scope, |fSq x_j| will
denote the application of the correct function for recursive positions, |f_I|,
or opaque types |f_K|. For example, here is the actual code of the function
which maps over a |NA| structure:
\begin{myhs}
\begin{code}
bimapNA f_K f_I  (NA_I  i)  = NA_I  (f_I  i)
bimapNA f_K f_I  (NA_K  k)  = NA_K  (f_K  k)
\end{code}
\end{myhs}
which following this convention becomes:
\begin{myhs}
\begin{code}
bimapNA f_K f_I x ^= fSq x
\end{code}
\end{myhs}

The first obvious combinator which we can write using the sum-of-products
structure is |map|. 
Our |RepMRec kappa phi c| is no longer a regular functor, but a higher
bifunctor. In other words, it requires two functions, one for mapping over
opaque types and another for mapping over |I| positions.

\begin{myhs}
\begin{code}
bimapRep  ::  (forall k   dot kappa1  k   -> kappa2  k)  ->  (forall ix  dot phi1    ix  -> phi2    ix) 
          ->  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c
bimapRep f_K f_I (C x_1 dots x_n) ^= C (fSq x_1) dots (fSq x_n)
\end{code}
\end{myhs}

  More interesting than a map perhaps is a general eliminator. In order to
destruct a |RepMRec kappa phi c| we need a way for eliminating every recursive position
or opaque type inside the representation and a way of combining these results. 

\begin{myhs}
\begin{code}
elimRep  ::  (forall k   dot kappa  k   -> a)  ->  (forall ix  dot phi    ix  -> a)  ->  ([a] -> b) 
         ->  RepMRec kappa phi c -> b
elimRep f_K f_I cat (C x_1 dots x_n) ^= cat [ fSq x_1 , dots , fSq x_n ]
\end{code}
\end{myhs}

  Being able to eliminate a representation is useful, but it becomes even
more useful when we are able to combine the data in different values of
the same representation with a |zip| like combinator. Our |zipRep|
will attempt to put two values of a representation ``side-by-side'', as long
as they are constructed with the same injection into the $n$-ary sum, |NS|.

\begin{myhs}
\begin{code}
zipRep  ::  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c
        ->  Maybe (RepMRec (kappa1 :*: kappa2) (phi1 :*: phi2) c)
zipRep (C x_1 dots x_n) (D y_1 dots y_m)
  | C == D     ^=  Just (C (x_1 :*: y_1) dots (x_n :*: y_n))
                   -- if C == D, then also n == m!
  | otherwise  ^=  Nothing
\end{code}
\end{myhs}

  This definition |zipRep| can be translated  to work with an arbitrary
|(Alternative f)| instead of |Maybe|. The |compos|
combinator, already introduced in \Cref{sec:explicitfix}, shows up in
a yet more expressive form.  We are now able to change every subtree
of whatever type we choose inside an arbitrary value of the mutually
recursive family in question.

\begin{myhs}
\begin{code}
compos  ::  (forall iy dot El fam iy -> El fam iy)
        ->  El fam ix -> El fam ix
compos f = toMRec . bimapRep id f . fromMRec
\end{code}
\end{myhs}

  Defining these combinators in \texttt{multirec} is not impossible,
but involves a much bigger effort. Everything has to be implemented
by the means of type classes and each supported combinator must
have one instance. 

  It is worth noting that although we presented pure versions
of these combinators, \texttt{generics-mrsop} defines monadic
variants of these and suffixes them with a \texttt{M}, following the
standard Haskell naming convention. We will need these monadic
combinators in \Cref{sec:alphaequivalence}.

\section{Examples}
\label{sec:mrecexamples}

In this section we present two applications of our generic programming
approach, namely equality and $\alpha$-equivalence. Our goal
is to show that our approach is at least as powerful as any other comparable
library, but brings in the union of their advantages. 
Even though some examples use a single recursive
datatype for the sake of conciseness, those can be readily generalized to
mutually recursive families. Another common benchmark for the power of
a generic library, zippers, is described in \Cref{sec:zipper} due to lack
of space.

There are many other applications for generic programming which
greatly benefit from supporting mutual recursion, if not requiring it.
One great source of examples consists of operations on abstract syntax
trees of realistic languages, such as generic
diffing~\cite{Miraldo2017} or
pretty-printing~\cite{Magalhaes2010}.

\subsection{Equality}

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

  As usually done in generic programming papers,
we should define generic equality in our own framework. 
In fact, with \texttt{generics-mrsop} we can define a particularly
elegant version of generic equality, given in \Cref{fig:genericeq}.

  Reading through the code we see that we convert both
arguments of |geq| to their deep representation, then compare their
top level constructor with |zipRep|. If they agree
we go through each of their fields calling either the equality on
opaque types |eq_K| or recursing.

\subsection{$\alpha$-Equivalence}
\label{sec:alphaequivalence}

A more involved exercise is the definition of
\emph{$\alpha$-equivalence} for a language.
In this section we start by
showing a straightforward version for the $\lambda$-calculus and then move
on to a more elaborate language. Although such problem has already been treated
using generic programming~\cite{Weirich2011}, it provides a good
example to illustrate our library. 

  Regardless of the language, determining whether two programs are
$\alpha$-equivalent requires one to focus on the constructors that
introduce scoping, declare variables or reference variables. All the
other constructors of the language should just
combine the recursive results. Let us warm up with untyped
$\lambda$-calculus:

%format LambdaTerm = "\HT{Term_{\lambda}}"
\begin{myhs}
\begin{code}
data LambdaTerm  =  Var  String |  Abs  String LambdaTerm |  App  LambdaTerm  LambdaTerm
\end{code}
\end{myhs}

  Let us explain the process step by step. First, for |t_1, t_2 :: LambdaTerm|
to be $\alpha$-equivalent, they have to have the constructors
on the same positions. Otherwise, they cannot be
$\alpha$-equivalent. Then we check the bound variables: we 
traverse both terms at the same time and
every time we go through a binder, in this case |Abs|, we register a
new \emph{rule} saying that the bound variable names are equivalent
for the terms under that scope. Whenever we find a reference to a
variable, |Var|, we check if the referenced variable is 
equivalent under the registered \emph{rules} so far.

  Let us abstract away this book-keeping functionality by the means of
a monad with a couple of associated functions. The idea is that monad |m| will
keep track of a stack of scopes, and each scope will register a list
of \emph{name-equivalences}. Indeed, this is very close to how one
should go about defining equality for \emph{nominal terms}~\cite{Calves2008}.

\begin{myhs}
\begin{code}
class Monad m => MonadAlphaEq m where
  scoped    :: m a -> m a
  addRule   :: String -> String -> m ()
  (=~=)     :: String -> String -> m Bool
\end{code}
\end{myhs}

  Running a |scoped f| computation will push a new scope for running |f|
and pop it after |f| is done. The |addRule v_1 v_2| function registers an equivalence
of |v_1| and |v_2| in the top of the scope stack. Finally, |v_1 =~= v_2| is defined
by pattern matching on the scope stack. If the stack is empty, then |(=~=) v_1 v_2 = (v_1 == v_2)|.
Otherwise, let the stack be |s:ss|. We first traverse |s| gathering the rules
referencing either |v_1| or |v_2|. If there are none, we check if |v_1 =~= v_2| under |ss|.
If there are rules referencing either variable name in the topmost stack, we must
ensure there is only one such rule, and it states a name equivalence between |v_1| and |v_2|.
The implementation of these functions for |MonadAlphaEq (State [[ (String , String) ]])| is available as part of our library.

\begin{figure}[b]
%format TermP  = "\HT{Term\_}"
%format VarP   = "\HT{Var\_}"
%format AbsP   = "\HT{Abs\_}"
\begin{myhs}
\begin{code}
alphaEq :: LambdaTerm -> LambdaTerm -> Bool
alphaEq x y =  flip runState [[]] 
               (galphaEq (deepFrom x) (deepFrom y)) 
  where
    galphaEq x y = maybe False (go (Pat Term)) (zipRep x y)

    step = elimRepM   (return . uncurry (==))
                      -- opaque types have to be equal!
                      (uncurry galphaEq)  -- recursive step
                      (return . and)      -- combine

    go (Pat LambdaTerm) x = case sop x of
      (Pat Var) (v_1 :*: v_2) -> v_1 =~= v_2
      (Pat Abs) (v_1 :*: v_2) (t_1 :*: t_2) 
         -> scoped (addRule v_1 v_2 >> galphaEq t_1 t_2)
      _  -> step x
\end{code}
\end{myhs}
\caption{$\alpha$-equivalence for a $\lambda$-calculus}
\label{fig:alphalambda}
\end{figure}

  Returning to our main focus and leaving book-keeping functionality
aside, we define in \Cref{fig:alphalambda} our alpha equivalence decision procedure by encoding what to do
for |Var| and |Abs| constructors. The |App| can be eliminated generically.

\begin{figure*}
\begin{myhs}
\begin{code}
data Stmt  =  SAssign  String  Exp 
           |  SIf      Exp     Stmt Stmt
           |  SSeq     Stmt    Stmt
           |  SReturn  Exp
           |  SDecl    Decl
           |  SSkip

data Decl  =  DVar String
           |  DFun String String Stmt

data Exp   =  EVar   String
           |  ECall  String  Exp
           |  EAdd   Exp     Exp
           |  ESub   Exp     Exp
           |  ELit   Int
\end{code}
\end{myhs}

\begin{myhs}
\begin{code}
go (Pat Stmt)  x = case sop x of
      (Pat SAssign) (v_1 :*: v_2) (e_1 :*: e_2)             ->  addRule v_1 v_2 >> galphaEq e_1 e_2
      _                                                     ->  step x
go (Pat Decl)  x = case sop x of
      (Pat DVar) (v_1 :*: v_2)                              ->  addRule v_1 v_2 >> return True
      (Pat DFun) (f_1 :*: f_2) (x_1 :*: x_2) (s_1 :*: s_2)  ->  addRule f_1 f_2
                                                            >>  scoped (addRule x_1 x_2 >> galphaEq s_1 s_2)
      _                                                     ->  step x
go (Pat Exp)   x = case sop x of
      (Pat EVar) (v_1 :*: v_2)                              ->  v_1 =~= v_2
      (Pat ECall) (f_1 :*: f_2) (e_1 :*: e_2)               ->  (&&) <$$> f_1 =~= f_2 <*> galphaEq e_1 e_2 
      _                                                     ->  step x 
go _      x = step x
\end{code}
\end{myhs}
\caption{$\alpha$-equivalence for a toy imperative language}
\label{fig:alphatoy}
\end{figure*}

  There is a number of remarks to be made for this example. First,
note the application of |zipRep|. If two |LambdaTerm|s are made with different
constructors, |galphaEq| will already return |False| because |zipRep| will fail.
When |zipRep| succeeds though, we get access to one constructor with
paired fields inside. The |go| is then responsible for performing
the necessary semantic actions for the |Var| and |Abs|
constructors and applying a general eliminator for anything else.
In the actual library, the \emph{pattern synonyms} |(Pat LambdaTerm)|, |(Pat Var)|,
 and |(Pat Abs)| are automatically 
generated as we will see in \Cref{sec:templatehaskell}.

  One might be inclined to believe that the generic programming here
is more cumbersome than a straightforward pattern matching definition
over |LambdaTerm|. If we consider a more intricate language,
however, manual pattern matching becomes almost intractable
very fast.

Take the toy imperative language defined in \Cref{fig:alphatoy}.
$\alpha$-equivalence for this language can be defined with just a 
couple of changes to the definition for |LambdaTerm|.
For one thing, |alphaEq|, |step| and |galphaEq| remain the same.  We just need to
adapt the |go| function. Here writing
$\alpha$-equivalence by pattern matching is not straightforward anymore.
Moreover, if we decide to change this language and
add more statements or more expressions, the changes to the |go|
function are minimal, none if we do not introduce any additional construct
which declares or uses variables. As long as we do not touch the
constructors that |go| patterns matches on, we can even use the very same
function.

  In this section we have shown several recurring examples from the
generic programming community. \texttt{generics-mrsop} gives
both expressive power and convenience.
%  The overall selection of examples show that by keeping the good ideas from
%the generic programming community and putting them all under the same roof
%we are able to achieve powerful functionality in a convenient fashion.
  The last point we have to address is that we still have to write
the |Family| instance for the types we want to use. For instance,
the |Family| instance for example in \Cref{fig:alphatoy} is not going
to be fun. Deriving these automatically is possible, but non-trivial;
we give a full account in \Cref{sec:templatehaskell}   

\section{Conclusion and Future Work}

  Generic programming is an ever changing field. The more the
Haskell language evolves, the more interesting generic programming
libraries we can create. Indeed, some of the language extensions we require 
in our work were not available at the time that some of the
libraries in the related work were developed.  

  Future work involves expanding the universe of datatypes that our
library can handle. Currently, every type involved in a recursive
family must be a ground type (of kind |Star| in Haskell terms); our
Template Haskell derivations acknowledges this fact by implementing
some amount of reduction for types.  This limits the functions we can
implement generically, for example we cannot write a generic |fmap|
function, since it operates on types of kind |Star -> Star|.
\texttt{GHC.Generics} supports type constructors with exactly one
argument via the \texttt{Generic1} type class. 
We intend to combine the approach in this paper with that of
\cite{Serrano2018}, in which atoms have a wider choice of shapes.

  The original sum-of-products approach does not handle all the ground
types either, only regular ones~\cite{deVries2014}. We inherit this
restriction, and cannot represent recursive families which involve
existentials or GADTs. The problem in this case is representing the
constraints that each constructor imposes on the type arguments.

  Our \texttt{generics-mrsop} is a powerful library for generic
programming that combines the advantages of previous approaches to
generic programming. We have carefully blended the information about
(mutually) recursive positions from \texttt{multirec}, with the
sums-of-products codes introduced by \texttt{generics-sop}, while maintaining the
advantages of both. The programmer is now able to use
simple, combinator-based generic programming for a more expressive
class of types than the sums-of-products approach allows. This is
interesting, especially since mutually recursive types were hard 
to handle in a generic fashion previous to \texttt{generics-mrsop}.






