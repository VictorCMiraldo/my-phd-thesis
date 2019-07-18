\section{Tree Edit Distance}
\label{sec:background:tree-edit-dist}

  The notion of \emph{tree edit distance} is vague and varies from
author to author \cite{Bille2005}.  Abstractly, it is a number that
represents the \emph{cost} of transforming a source tree into a
destination tree. Whereas this transformation is performed by a select
number of \emph{edit operations}. Which operations to consider will
heavily influence the cost of transforming a tree into another and,
consequently, the algorithms for computing the minimal sequence of
said operations. The most common choice of operations are insertions,
deletions and relabelings, whih stems from the edit operations that
are generally used in the \emph{string edit distance}~\cite{Bergroth2000}
domain. The \unixdiff{}, however, does not consider relabelings
as a basic operation, for example.

\victor{more glue???}

  On this section we will review some of the important notions and
background work on edit distance. We start by looking at the string
edit distance, \Cref{sec:background:string-edit-distance} and
then we generalize it to untyped trees, in \Cref{sec:background:tree-edit-distance}, as it is classically portrayed in the literature. Finally,
we discuss some of the consequences of working with typed trees
in \Cref{sec:background:typed-tree-edit-distance}.

\victor{
The diffing problem can be portrayed in a variety of different flavors.
The untyped approach has been thoroughly studied in both its
linear~\cite{Bergroth2000} and
tree~\cite{Akutsu2010,Demaine2007,Klein1998,Bille2005,Autexier2015,Chawathe1997}
variations. The canonical solution for the untyped linear scenario is
the well known Unix \texttt{diff}~\cite{McIlroy1976}. For the
tree-structured variation, though, a variety of
implementations~\cite{Farinier2015,Hashimoto2008,Falleri2014}
has arisen in the last few years. In this paper, however, we have explored
how to exploit the \emph{type structure} of trees to give a more
precise account of our diff algorithm.

Beyond diffing, there is a great deal of work on version control
systems.  The canonical example of a \emph{formal} VCS is
Darcs~\cite{Darcs}. The system itself is built around the \emph{theory
  of patches} developed by the same team. A formalization of such
theory using inverse semigroups was done by
Jacobson~\cite{Jacobson2009}. Another example is the Pijul VCS,
inspired by Mimram~\cite{Mimram2013}. This uses category theory to
define and reason about patches.  The base category on which their
work is built, however, handles files as a list of lines, thus
providing only a theoretical framework on top of the already existing
Unix \texttt{diff}. Swierstra and L\"{o}h~\cite{Swierstra2014} apply
separation logic and Hoare calculus to be able to define a logic for
reasoning about patches. Separation logic is particularly useful to
prove the \emph{disjointedness} of patches -- and guarantee that their
associated apply functions commute.  Finally, Anguiuli et
al.~\cite{Angiuli2014} have developed a model of patch theory within
Homotopy Type Theory. Although their model considers various patches
and repositories, it does not provide a generic account for
arbitrary data types as done here.
}

\subsection{String Edit Distance and \unixdiff{}}
\label{sec:background:string-edit-distance}
 
\subsection{Classic Tree Edit Distance}
\label{sec:background:tree-edit-distance}

\subsection{Typed Tree Edit Distance}
\label{sec:background:typed-tree-edit-distance}

\section{Generic Programming}
\label{sec:background:generic-programming}

  \emph{(Datatype-)generic programming}\index{Generic Programming}
provides a mechanism to write functions by induction on the structure
of algebraic datatypes~\cite{Gibbons2006}.  A well-known example is
the |deriving| mechanism in Haskell, which frees the programmer from
writing repetitive functions such as equality~\cite{haskell2010}. A
vast range of approaches were available as preprocessors, language
extensions, or libraries for Haskell~\cite{Rodriguez2008,Magalhaes2012}.  

  The core idea behind generic programming is the fact that a number
of datatypes can be described in a uniform fashion.  Hence, if a
programmer were to write programs that work over this uniform
representation, these programs would immediately work over a variety
of datatypes. We are interested in writing differencing algorithms for
abstract syntax trees, hence our datatypes will be mutually recursive
families.  Our programs must operate over \emph{any} such
family. Consequently, we must have a powerful generic programming
approach that is capable of (A) representing mutually recursive
datatypes and (B) easily operating over them by the means of
expressive combinators. At the time of writing thesis, no such
library existed. In fact, one of the contributions of this
thesis is the \texttt{generics-mrsop}~\cite{Miraldo2018} library,
\Cref{chap:generic-programming} which provides such a combinator-based
approach to generic programming with mutually recursive types.
In this section, however, we explore the approaches that existed
before \texttt{generics-mrsop} and outline their main differences.

  Consider the following datatype representing binary trees
with data stored in their leaves:

\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}

  A value of type |Bin a| consists of a choice between two
constructors.  For the first choice, it also contains a value of type
|a| whereas for the second it contains two subtrees as children. This
means that the |Bin a| type is isomorphic to |Either a (Bin a , Bin
a)|. Different libraries differ on how they define their underlying
generic descriptions.  For example,
\texttt{GHC.Generics}~\cite{Magalhaes2010}, which
comes bundled with GHC, defines the representation of |Bin| as the
following datatype:

\begin{myhs}
\begin{code}
Rep (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}

which is a direct translation of |Either a (Bin a , Bin a)|, but using
the combinators provided by \texttt{GHC.Generics}, namely |:+:| and
|:*:|. In addition, we require two conversion functions |from :: a ->
Rep a| and |to :: Rep a -> a| which form an isomorphism between |Bin
a| and |Rep (Bin a)|.  Finaly, all is tied to the original datatype
using a type class:

\begin{myhs}
\begin{code}
class Generic a where
  type Rep a :: Star
  from  :: a      -> Rep a 
  to    :: Rep a  -> a
\end{code}
\end{myhs}

  Most generic programming libraries follow a similar pattern of
defining the \emph{description} of a datatype in the provided uniform
language by some type level information, and two functions witnessing
an isomorphism. The most important feature of such library is how this
description is encoded and which are the primitive operations for
constructing such encodings, \Cref{sec:designspace}. Some libraries,
mainly deriving from the \texttt{SYB}
approach~\cite{Lammel2003,Mitchell2007}, use the |Data| and |Typeable|
type classes instead of static type level information to provide
generic functionality.  These are a completely different strand of
work from what we seek. The other approach relies on type level
representations of datatypes. \Cref{fig:gplibraries} shows the main
libraries relying on the typed approach. These can be compared in their
treatment of recursion and on their choice of type level combinators
used to represent generic values.

\begin{figure}\centering
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \multirow{2}{*}{\textbf{\texttt{generics-mrsop}}} \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
\caption{Spectrum of static generic programming libraries}
\label{fig:gplibraries}
\end{figure}

\paragraph{Recursion Style.}

  There are two ways to define the representation of values. Those
that have information about which fields of the constructors of 
the datatype in question are recursive versus those that do not. 

If we do not mark recursion explicitly, \emph{shallow}\index{Generic
Programming!Shallow} encodings are our sole option, where only one
layer of the value is turned into a generic form by a call to |from|.
This is the kind of representation we get from \texttt{GHC.Generics}.
The other side of the spectrum would be the \emph{deep}\index{Generic
Programming!Deep} representation, in which the entire value is turned
into the representation that the generic library provides in one go.

Marking the recursion explicitly, like in
\texttt{regular}~\cite{Noort2008}, allows one to choose between
\emph{shallow} and \emph{deep} encodings at will. These
representations are usually more involved as they need an extra
mechanism to represent recursion.  In the |Bin| example, the
description of the |Bin| constructor changes from ``this constructor
has two fields of the |Bin a| type'' to ``this constructor has two
fields in which you recurse''. Therefore, a \emph{deep} encoding
requires some explicit \emph{least fixpoint} combinator -- usually
called |Fix| in Haskell.

Depending on the use case, a shallow representation might be more
efficient if only part of the value needs to be inspected. On the
other hand, deep representations are sometimes easier to use, since
the conversion is performed in one go, and afterwards one only has to
work with the constructs from the generic library. 

The fact that we mark explicitly when recursion takes place in a
datatype gives some additional insight into the description.
Some functions really need the information
about which fields of a constructor are recursive and which are not,
like the generic |map| and the generic |Zipper| -- we describe
the latter in \Cref{sec:mrecexamples}.
This additional power has also been used to define regular
expressions over Haskell datatypes~\cite{Serrano2016}. 

\paragraph{Pattern Functors versus Codes.}

Most generic programming libraries build their type level descriptions
out of three basic combinators: (1) \emph{constants}, which indicate a
type is atomic and should not be expanded further; (2) \emph{products}
(usually written as |:*:|) which are used to build tuples; and (3)
\emph{sums} (usually written as |:+:|) which encode the choice between
constructors. The |Rep (Bin a)| shown before is expressed in this
form. Note, however, that there is no restriction on \emph{how} these
can be combined. These combinators are usually refered to as
\emph{pattern functors}\index{Pattern Functor} The \emph{pattern
functor}-based libraries are too permissive though, for instance, |K1
R Int :*: Maybe| is a perfectly valid \texttt{GHC.Generics}
\emph{pattern functor} but will break generic functions, i.e., |Maybe|
is not a combinator.

 In practice, one can always use a sum of products to represent a
datatype -- a sum to express the choice of constructor, and within
each constructor a product to declare which fields you have. The
\texttt{generic-sop} library~\cite{deVries2014} explicitly uses a list
of lists of types, the outer one representing the sum and each inner
one thought of as products. The $\HS{'}$ sign in the code below marks
the list as operating at the type level, as opposed to term-level
lists which exist at run-time. This is an example of Haskell's
\emph{datatype} promotion~ \cite{Yorgey2012}.

\begin{myhs}
\begin{code}
CodeSOP (Bin a) = P [ P [a], P [Bin a, Bin a] ]
\end{code}
\end{myhs}

  The shape of this description follows more closely the shape of
Haskell datatypes, and make it easier to implement generic
functionality.

  Note how the \emph{codes} are different than the
\emph{representation}.  The latter being defined by induction on the
former.  This is quite a subtle point and it is common to see both
terms being used interchangeably.  Here, the \emph{representation} is
mapping the \emph{codes}, of kind |P [ P [ Star ] ]|, into |Star|. The
\emph{code} can be seen as the format that the \emph{representation}
must adhere to. Previously, in the pattern functor approach, the
\emph{representation} was not guaranteed to have a certain
structure. The expressivity of the language of \emph{codes} is
proportional to the expressivity of the combinators the library can
provide.

\subsection{GHC Generics}
\label{sec:patternfunctors}

  Since version $7.2$, GHC supports the
\texttt{GHC.Generics}~\cite{Magalhaes2010} library, which exposes the
\emph{pattern functor} of a datatype. This allows one to define a
function for a datatype by induction on the structure of its (shallow)
representation using \emph{pattern functors}\index{Pattern Functor}.

  These \emph{pattern functors} are parametrized versions of tuples,
sum types (|Either| in Haskell lingo), and unit, empty and constant
functors. These provide a unified view over data: the generic
\emph{representation} of values.  The values of a suitable type |a|
are translated to this representation by means of the function
|fromGen :: a -> RepGen a|. Note that the subscripts are there 
solely to disambiguate names that appear in many libraries. Hence,
|fromGen| is, in fact, the |from| in module |GHC.Generics|.

  Defining a generic function is done in two
steps. First, we define a class that exposes the function
for arbitrary types, in our case, |size|, which we implement
for any type via |gsize|:

\begin{myhs}
\begin{code}
class Size (a :: Star) where
  size :: a -> Int

instance (Size a) => Size (Bin a) where
  size = gsize . fromGen
\end{code}
\end{myhs}

  Next we define the |gsize| function that operates on the level of the 
representation of datatypes. We have to use another class
and the instance mechanism to encode a definition by induction on
representations:

\begin{myhs}
\begin{code}
class GSize (rep :: Star -> Star) where
  gsize :: rep x -> Int
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}
\end{myhs}

  We still have to handle the cases where 
we might have an arbitrary type in a position, modeled by the
constant functor |K1|. We require an instance of |Size|
so we can successfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size x) => GSize (K1 R x) where
  gsize (K1 x) = size x
\end{code}
\end{myhs}

\begin{figure}\centering
{\small
$\begin{array}{l}
  |size (Bin (Leaf 1) (Leaf 2))| \\
  \;  = |gsize (fromGen (Bin (Leaf 1) (Leaf 2)))| \\
  \;  = |gsize (R1 (K1 (Leaf 1) :*: K1 (Leaf 2)))| \\
  \;  = |gsize (K1 (Leaf 1)) + gsize (K1 (Leaf 2))| \\
  \;  \overset{\dagger}{=} |size (Leaf 1) + size (Leaf 2)| \\
  \;  = |gsize (fromGen (Leaf 1)) + gsize (fromGen (Leaf 2))|\\
  \;  = |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
  \;  = |size (1 :: Int) + size (2 :: Int)|   
\end{array}$}
\caption{Reduction of |size (Bin (Leaf 1) (Leaf 2))|}
\label{fig:sizederiv}
\end{figure}

  To finish the description of the generic |size|,
we also need instances for the
\emph{unit}, \emph{void} and \emph{metadata} pattern functors,
called |U1|, |V1|, and |M1| respectively. Their |GSize| is
rather uninteresting, so we omit them for the sake of conciseness.

  This technique of \emph{mutually recursive classes} is quite
specific to the \texttt{GHC.Generics} flavor of generic programming.
\Cref{fig:sizederiv} illustrates how the compiler goes about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|.  In the end,
we just need an instance for |Size Int| to compute the final
result. Literals of type |Int| illustrate what we call \emph{opaque
types}\index{Generic Programming!Opaque Types}: those types that
constitute the base of the universe and are \emph{opaque} to the
representation language.


\subsection{Explicit Sums of Products}
\label{sec:explicitsop}

  The other side of the coin to pattern functors is restricting
the shape of the generic values to \emph{sums-of-products}.
This was first done by L\"{o}h and de Vries\cite{deVries2014}
in the \texttt{generics-sop} library.

  The main difference is in the introduction of
\emph{Codes}\index{Generic Programming!Codes}, that limit the
structure of representations. Had we had access to a representation of
the \emph{sum-of-products} structure of |Bin|, we could have defined
our |gsize| function following an informal description: sum up the
sizes of the fields inside a value, ignoring the constructor.

  Unlike \texttt{GHC.Generics}, the representation of values is
defined by induction on the \emph{code} of a datatype, this
\emph{code} is a type level list of lists of kind |Star|, whose
semantics is consonant to a formula in disjunctive normal form.  The
outer list is interpreted as a sum and each of the inner lists as a
product.  This section provides an overview of \texttt{generic-sop} as
required to understand the techniques we use in
\Cref{chap:generic-programming}, we refer the reader to the original
paper~\cite{deVries2014} for a more comprehensive explanation.

  Using a \emph{sum-of-products} approach one could write the same |gsize|
function shown in \Cref{sec:patternfunctors} as easily as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of |gsize| for a moment, let us focus just on
its high level structure. Remembering that |from| now returns a
\emph{sum-of-products} view over the data, we are using an eliminator,
|elim|, to apply a function to the fields of the constructor used to
create a value of type |a|. This eliminator then applies |map size| to
the fields of the constructor, returning something akin to a
|[Int]|. We then |sum| them up to obtain the final size.

  Codes consist of a type level list of lists. The outer
list represents the constructors of a type, and will be interpreted as
a sum, whereas the inner lists are interpreted as the fields of the
respective constructors, interpreted as products.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: Star) :: P ([ (P [Star]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  The \emph{representation} is then defined by induction on
|CodeSOP| by the means of generalized $n$-ary sums, |NS|, and $n$-ary products,
|NP|. With a slight abuse of notation, one can view |NS| and |NP|
through the lens of the following type isomorphisms:

\vspace{-0.4cm}
{\small
\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}}
\vspace{-0.4cm}

  If we define |RepSOP| to be |NS (NP (K1 R))|, where |data K1 R a = K1 a| is borrowed from
\texttt{GHC.Generics} we get exaclty the representation that \texttt{GHC.Generics}
would issue for |Bin a|. Nevertheless, note how we already need the parameter |f| to
pass |NP| to |NS| here. 

\vspace{-0.4cm}
{\small
\begin{align*}
  |RepSOP (Bin a)|
  &\equiv | NS (NP (K1 R)) (CodeSOP (Bin a))| \\
  &\equiv |K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))| \\
  &\equiv |RepGen (Bin a)|
\end{align*}
}
\vspace{-0.4cm}

  It makes no sense to go through all the trouble of adding the
explicit \emph{sums-of-products} structure to forget this information
in the representation. Instead of piggybacking on \emph{pattern
functors}, we define |NS| and |NP| from scratch using
\emph{GADTs}~\cite{Xi2003}.  By pattern matching on the values of |NS|
and |NP| we inform the type checker of the structure of |CodeSOP|.

\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f k      -> NS f (k (P (:)) ks)
  There  :: NS f ks  -> NS f (k (P (:)) ks)

data NP :: (k -> Star) -> [k] -> Star where
  NP0   ::                    NP f (P [])
  (:*)  :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}
\end{myhs}

  Finally, since our atoms are of kind |Star|, we can use the identity
functor, |I|, to interpret those and define the final representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: Star) = I { unI :: a }
\end{code}
\end{myhs}

  To support the claim that one can define general combinators for
working with these representations, let us look at |elim| and |map|,
used to implement the |gsize| function in the beginning of the section.
The |elim| function just drops the constructor index and applies |f|,
whereas the |map| applies |f| to all elements of a product.

\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x

map :: (forall k dot f k -> a) -> NP f ks -> [a]
map f  NP0        = []
map f  (x :* xs)  = f x : map f xs
\end{code}
\end{myhs}

  Reflecting on the current definition of |size|, 
comparing it to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one fewer type class, |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  There are still downsides to this approach. A notable
one is the need to carry constraints around: the actual |gsize|
written with the \texttt{generics-sop} library and no sugar
reads as follows.

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a , All2 Size (CodeSOP a)) => a -> Int
gsize  =  sum  .  hcollapse
       .  hcmap (Proxy :: Proxy Size) (mapIK size) .  fromSOP
\end{code}
\end{myhs}

  Where |hcollapse| and |hcmap| are analogous to the |elim| and |map|
combinators defined above. The |All2 Size (CodeSOP a)| constraint
tells the compiler that all of the types serving as atoms for |CodeSOP
a| are an instance of |Size|.  Here, |All2 Size (CodeSOP (Bin
a))| expands to |(Size a , Size (Bin a))|.  The |Size| constraint also
has to be passed around with a |Proxy| for the eliminator of the
$n$-ary sum. This is a direct consequence of a \emph{shallow}
encoding: since we only unfold one layer of recursion at a time, we
have to carry proofs that the recursive arguments can also be
translated to a generic representation. We can relieve this burden by
recording, explicitly, which fields of a constructor are recursive or
not, which is exactly how we start to shape \texttt{generics-mrsop}
in \Cref{chap:generic-programming}.