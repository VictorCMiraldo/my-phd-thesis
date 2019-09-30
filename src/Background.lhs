\victor{
Planned Skeleton
\begin{itemize}
  \item explain edit-scripts
  \item make point: least-cost ES is arbitrary! 
  \item make point: ES are easy to compute but hard to merge!
  \item explain some generic programming
\end{itemize}}

  The problem of tree edit distance~\cite{Bergroth2000} has been showing
up in many different areas. 

  ted in bioinformatics: \cite{Akutsu2010b,Henikoff1992,McKenna2010}

  ted in tutorin systems: \cite{Paassen2017,Rohan2016}

  For more, check surveys \cite{Bille2005,Paassen2018}

\section{Tree Edit Distance}
\label{sec:background:tree-edit-dist}

\victor{this is bad; I need a better intro to it}
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
edit distance, \Cref{sec:background:string-edit-distance} and then we
generalize it to untyped trees, in
\Cref{sec:background:tree-edit-distance}, as it is classically
portrayed in the literature. Finally, we discuss some of the
consequences of working with typed trees in
\Cref{sec:background:typed-tree-edit-distance}.

\subsection{String Edit Distance and \unixdiff{}}
\label{sec:background:string-edit-distance}

  The distance between two strings, |s| and |d|, is defined by the
cost of transforming |s| into |d| by the means of some edit
operations.  The \emph{Levenshtein Distance}~\cite{Levenshtein1966} is
the most widespread metric for edit distance~\cite{Bergroth2000}. It
considers insertions, deletions and substitutions of characters as its
edit operations. Each of those operations has an associated cost, as
shown below.

\begin{myhs}
\begin{code}
data EOp = Ins Char | Del Char | Subst Char Char

cost :: EOp -> Int
cost (Ins _)      = 1
cost (Del _)      = 1
cost (Subst c d)  = if c == d then 0 else 1
\end{code}
\end{myhs}

  Note how the cost of a \emph{copy} operation is 0, and a non-identity
|Subst| costs less than deleting then inserting the given characters.
This ensures that the algorithm looking for the list of edit operations
with the minimum cost will prefer substitutions over deletions
and insertions. Said list of edit operations represents, in fact, 
a partial function that \emph{performs the transformation}.

\begin{myhs}
\begin{code}
apply :: [EOp] -> String -> Maybe String
apply []                  []         = Just []
apply (Ins c:ops)               ss   = (c :) <$$> apply ops ss
apply (Del c:ops)         (s :  ss)  = guard (c == s) >> apply ops ss
apply (Subst c d  : ops)  (s :  ss)  = guard (c == s) >> (d :) <$$> apply ops ss
\end{code}
\end{myhs}


  We can compute the \emph{edit script}\index{Edit Script}, i.e. a
list of edit operations, with the minimum cost quite easily with a
naive, inefficient, recursive implementation.  In fact, the problem of
computing the \emph{longest common subsequence} of a set of strings,
usually two, is closely related to computing the \emph{edit
distance}. It differs from the longest common substring for sequences
need not be consecutive within the original strings.

\begin{figure}
\begin{myhs}
\begin{code}
lcs :: String -> String -> [EOp]
lcs []      []      = []
lcs (x:xs)  []      = Del x : lcs xs []
lcs []      (y:ys)  = Ins y : lcs [] ys
lcs (x:xs)  (y:ys)  = 
  let  i = Ins y      : lcs (x:  xs)      ys
       d = Del x      : lcs      xs  (y:  ys)
       s = Subst x y  : lcs      xs       ys
   in minimumBy cost [i , d , s]
\end{code}
\end{myhs}
\caption{Definition of the function that returns a longest
common subsequence of two strings}
\label{fig:string-lcs}        
\end{figure}

  Running the |lcs x y| function, \Cref{fig:string-lcs}, will yield an
\emph{edit script} with minimum \emph{Levenshtein Distance} and
enables us to read out one longest common subsequence of |x| and
|y|. Note that longest common subsequences are not unique, in
general. Consider the case of |lcs "ab" "ba"| for instance.

  The \unixdiff{}~\cite{McIlroy1976} performs a slight generalization
by considring the distance between two \emph{files}, seen as a list of
\emph{strings}, opposed to a list of \emph{characters}. Moreover, it
does not consider |Subst| as an operation. Instead, it choses to only
allow for insertions, deletions and copies.

\begin{myhs}
\begin{code}
data EOp = Ins String | Del String | Cpy

cost :: EOp -> Int
cost (Ins _)  = 1
cost (Del _)  = 1
cost Cpy      = 0
\end{code}
\end{myhs}

  A practical implementation of the \unixdiff{} will use a number of
algorithmic techniques that make it performant. For starter, it is
essential to use a memoized |lcs| function to avoid recomputing
subproblems. It is also common to hash the data being compared to have
amortized constant time comparisson. More intricate, however, is the
usage of a number of heuristics that tend to perform well in certain
situations.  One example is the \texttt{diff --patience} algorithm~\cite{patienceDiff},
that will emphasize the matching of lines that appear only once in the
source and destintion files.

\victor{More detail? Less detail?}
 
\subsection{Classic Tree Edit Distance}
\label{sec:background:tree-edit-distance}


  The \unixdiff{} conceptually generalizes the notion of string edit
distance to a notion of edit distance between two arbitrary lists.
The notion of (untyped) tree edit
distance~\cite{Akutsu2010,Demaine2007,Klein1998,Bille2005,Autexier2015,Chawathe1997}
goes one step further, and considers \emph{arbitrary} trees as the
objects under scrutiny. Because of that, there is a lot of freedom on
the edit operations that we can consider in this untyped scenario. To
name a few we can have flattening insertions and deletions, where the
children of the deleted node are inserted or removed in-place in the
parent node. Another operation that only exists in the untyped world
is node relabeling, among others. This degree of variation is
responsible for the high number of different approaches and techniques we
see in practice~\cite{Farinier2015,Hashimoto2008,Falleri2014,Paassen2018}.
  
  Basic tree edit distance~\cite{Demaine2007}, however, considers only
node insertions, deletions and copies. The cost function is borrowed
entirely from string edit distance and so is the longest common
subsequence function, that instead of working with |[a]| will work
with |[Tree]|. The interpretation of the edit operations, shown in
\Cref{fig:apply-tree-edit} illustrates these modifications.

\begin{figure}
\begin{myhs}
\begin{code}
data EOp  = Ins Label | Del Label | Cpy
data Tree = Node Label [Tree]

arity :: Label -> Int

apply :: [EOp] -> [Tree] -> Maybe [Tree]
apply [] [] = Just []
apply (Cpy : ops) ts
  = apply (Ins l : Del l : ops) ts
apply (Del l : ops) (Node l' xs:ts)
  = guard (l == l') >> apply ops (xs ++ ts)
apply (Ins l : ops) ts
  = (\(args , rest) -> Node l args : rest) . takeDrop (arity l)
    <$$> apply ops ts
\end{code}
\end{myhs}
\caption{Definition of |apply| for tree edit operations}
\label{fig:apply-tree-edit}
\end{figure}

  We label these approaches as ``untyped'' because there exists edit
scripts that yield non-well formed trees. For example, imagine |l| is
a label with arity 2, that is, it is supposed to receive two
arguments. Now consider the edit script |Ins l : []|, which will yield
the tree |Node l []| once applied to the empty forest. If the objects
under differencing are required to abide by a certain schema, think of
abstract syntax trees, for example, this becomes an issue.  This is
particularly important when one wants the ability to manipulate
patches independently of the objects they have been created from.
Imagine a merge function that needs to construct a patch
based on two other patches. A wrong implementation of said merge function
can yield programs that are unparseable.

  It is possible to use the Haskell type system to our advantage and
write |EOp| in a way that it is guaranteed to return well typed
results. Labels will be the different constructors of the family of
types in question and their arity comes from how many fields each
constructor expects. Edit scripts will then be indexes by two lists of
types: the types of the trees it consumes and the types of the trees
it produces. We will come back to this in more detail in  
\Cref{sec:gp:well-typed-tree-diff}, where we review the approach of
Lempsink and L\"{o}h~\cite{Lempsink2009} at adapting this untyped framework
to be type-safe by construction.

  Although edit scripts provide a very intuitive notion of local
transformations over a tree, they are very redundant. Making it hard to 
develop algorithms based solely on edit scripts. It is often the case
that the community adopts the notion of \emph{tree mapping} as
a \emph{normal form} version of edit scripts. 

\begin{definition}[Tree Mapping]
Let |t| and |u| be two trees, a tree mapping 
between |t| and |u| is a partial injective order preserving mapping between the
nodes of a flattened representation of |t| and |u| according
to their preorder traversal.
\end{definition}

   The tree mapping determines the nodes where either a copy or substitution
must be performed. Everything else must be deleted or inserted and the
order of deletions and insertions is irrelevant, which removes the redundancy
of edit scripts. Nevertheless, the definition of tree mapping is still very restrictive:
(i) the ``injective mapping'' does not enable trees to be shared or contracted;
(ii) the ``order preserving'' does not enbale trees to be permuted or moved
accross ancestor boundaries. In turn, this imposes a burden of choice on any
algorithm that has its underlying base in edit-scripts, regardless of whether
it uses tree mappings internally or not. 
  
\subsection{Shortcommings of Edit Scripts}

\victor{
\begin{enumerate}
  \item Non-cannonicity
  \item Can't express commonly seen changes (are they really commonly seen?)
  \item Many longest-common-subsequences
  \item algorithms are heavily heuristic
  \item typed approach is very hard to merge
\end{enumerate}}

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
constructing such encodings. Some libraries,
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
like the generic |map| and the generic |Zipper|. 
This additional power has also been used to define regular
expressions over Haskell datatypes~\cite{Serrano2016}, for example.

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
one thought of as products. The $\HS{'}$ sign in the code below marks the list
as operating at the type level, as opposed to term-level lists which
exist at run-time. This is an example of Haskell's \emph{datatype}
promotion~\cite{Yorgey2012}.


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
\label{sec:background:patternfunctors}

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
\label{sec:background:explicitsop}

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
function shown in \Cref{sec:background:patternfunctors} as easily as:

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

  It makes no sense to go through the trouble of adding the
explicit \emph{sums-of-products} structure to forget this information
in the representation. Instead of piggybacking on \emph{pattern
functors}, we define |NS| and |NP| from scratch using
\emph{GADTs}~\cite{Xi2003}.  By pattern matching on the values of |NS|
and |NP| we inform the type checker of the structure of |CodeSOP|.

\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f k      -> NS f (k Pcons ks)
  There  :: NS f ks  -> NS f (k Pcons ks)

data NP :: (k -> Star) -> [k] -> Star where
  NP0   ::                    NP f (P [])
  (:*)  :: f x -> NP f xs ->  NP f (x Pcons xs)
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

