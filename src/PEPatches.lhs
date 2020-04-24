  The \texttt{stdiff} approach gave us a first representation of
tree-structured patches over tree-structured data but was still deeply
connected to edit-scripts: subtrees could only be copied once and
could not be permuted. This means we still suffered from ambiguous
patches, and, consequently, a computationally expensive |diff|
algorithm. Overcoming the drawback of ambiguity requires a shift in
perspective and abandoning edit-script based
differencing algorithms. In this section we will explore the
\texttt{hdiff} approach, where patches allow for trees to be
arbitrarily permuted, duplicated or contracted (contractions are
dual to duplications).

  Classical tree differencing algorithms start by computing tree
matchings (\Cref{sec:background:tree-edit-distnace}), which identify
the subtrees that should be copied. These tree matchings, however, must
be restricted to order-preserving partial injections to be
efficiently translated to edit-scripts later.  The \texttt{hdiff}
approach never translates to edit-scripts, which means the tree
matchings we compute are subject to \emph{no} restrictions.  In fact,
\texttt{hdiff} uses these unrestricted tree matchings as \emph{the patch},
instead of translating them \emph{into} a
patch.

  Suppose we want to describe a change that modifies the left element
of a binary tree. If we had the full Haskell programming language
available as the patch language, we could write something similar to
function |c|, in \Cref{fig:pepatches:example-01:A}. Observing the
function |c| we see it has a clear domain -- a set of |Tree|s that
when applied to |c| yields a |Just| -- which is specified by the
pattern and guards. Then, for each tree in the domain we compute a
corresponding tree in the codomain.  The new tree is obtained from the
old tree by replacing the |10| by |42| in-place.  Closely inspecting
this definition, we can interpret the matching of the
pattern as a \emph{deletion} phase and the construction of the
resulting tree as a \emph{insertion} phase.  The \texttt{hdiff}
approach represents the change in |c| exactly as that: a pattern and a
expression. Essentially, we write |c| as |Chg (Bin (Leaf 10) y) (Bin
(Leaf 42) y)| -- represented graphically as in
\Cref{fig:pepatches:example-01:B}.

% An important aspect here is that the
% graphical notation makes it evident which constructors were copied
% until we reach the point where a change must be made. The notation
% $\digemFormatMetavar{\square}$ is used to indicate $\square$ is a
% metavariable, that is, given a successful matching of the deletion
% context against an element, $\digemFormatMetavar{\square}$ will be
% given a value.

\begin{figure}
\centering
\subfloat[Haskell function |c|]{%
\begin{myhsFig}[0.4\textwidth]
\begin{code}
p :: Tree -> Maybe Tree
p (Bin (Leaf x) y)
  | x == 10    = Just (Bin (Leaf 42) y)
  | otherwise  = Nothing
p _            = Nothing
\end{code}
\end{myhsFig}\label{fig:pepatches:example-01:A}}\qquad\qquad
\subfloat[|c| represented as a \emph{change}]{%
\begin{myforest}
[,change
[|Bin|
  [|Leaf| [|10|]]
  [y,metavar]]
[|Bin|
  [|Leaf| [|42|]]
  [y,metavar]]
]
\end{myforest}\label{fig:pepatches:example-01:B}}
\caption{Haskell function and its graphical representation as a change.
The change here modifies the left child of a binary node. Notation |metavar y| is used to indicate |y| is
a metavariable.}
\label{fig:pepatches:example-01}
\end{figure}

  With the added expressivity of referring to subtrees
with metavariables we can represent more transformations
than before. Take, for example, the change that swaps two subtrees, which cannot
even be written using an edit-script based approach, here it is
given by |Chg (Bin x y) (Bin y x)|. Another helpful consequence of
our design is that we effectively bypass the \emph{choice} phase of the
algorithm. When computing the differences between |Bin Leaf Leaf|
and |Leaf|, for example, we do not have to chose one |Leaf| to copy
because we can copy both with the help of a contraction operation,
with a change such as: |Chg (Bin x x) x|. This aspect is crucial
and enables us to write a linear |diff| algorithm.

  In this chapter we explore the representation and computation
aspects of \texttt{hdiff}.  The big shift in paradigm of
\texttt{hdiff} also requires a more careful look into the metatheory
and nuances of the algorithm, which were not present in our original
paper~\cite{Miraldo2019}. The material in this chapter is a
developed from our ICFP'19 publication~\cite{Miraldo2019}, shifting
to the \genericssimpl{} library.

\victor{Maybe we write another paper with Pierre about it?}

%% The closest approach to \texttt{hdiff}
%% in the literature is perhaps \texttt{XyDiff}~\cite{Marian2002}, which
%% uses hashes to compute tree matchings but still relies on edit-scripts
%% with the additon of a `move' operation. Such `move' operation is only
%% possible because \texttt{XyDiff} operataes over XML, which is untyped.
%% Therefore we can always remove a child of a node and move it somewhere
%% else.

\section{Changes}

\subsection{A Concrete Example}
\label{sec:pepatches:concrete-changes}

  Before exploring the generic implementation of our algorithm, let us
look at a simple, concrete instance first, which sets the stage for
the the generic implementation that will follow.  Throughout this
section we will explore the central ideas from our algorithm
instantiated for a type of 2-3-trees:

\begin{myhs}
\begin{code}
data Tree  = Leaf Int | Bin Tree Tree | Tri Tree Tree Tree
\end{code}
\end{myhs}

  The central concept of \texttt{hdiff} is the encoding of a \emph{change}.
Unlike previous work~\cite{Loh2009,Miraldo2017,Klein1998} which is
based on tree-edit-distance~\cite{Bille2005} and hence, uses only
insertions, deletions and copies of the constructors encountered
during the preorder traversal of a tree (\Cref{sec:gp:well-typed-tree-diff}), we
go a step further. We explicitly model permutations, duplications and
contractions of subtrees within our notion of \emph{change}. Where
contraction here denotes the partial inverse of a duplication. The
representation of a \emph{change} between two values of type |Tree|,
then, is given by identifying the bits and pieces that must be copied
from source to destination making use of permutations and duplications
where necessary.

  A new datatype, |TreeC phi|, enables us to annotate a value of
|Tree| with holes of type |phi|. Therefore, |TreeC Metavar|
represents the type of |Tree| with holes carrying metavariables.
These metavariables correspond to arbitrary trees that are
\emph{common subtrees} of both the source and destination of the
change.  These are exactly the bits that are being copied from the
source to the destination tree.  We refer to a value of |TreeC| as a
\emph{context}.  For now, the metavariables will be simple |Int|
values but later on we will need to carry additional information.

\begin{myhs}
\begin{code}
type Metavar = Int

data TreeC phi = Hole   phi | LeafC  Int | BinC   TreeC TreeC | TriC   TreeC TreeC TreeC
\end{code}
\end{myhs}

  A \emph{change} in this setting is a pair of such contexts. The first
context defines a pattern that binds some metavariables, called the
deletion context; the second, called the insertion context,
corresponds to the tree annotated with the metavariables that are supposed
to be instantiated by the bindings given by the deletion context.

\begin{myhs}
\begin{code}
type Change phi = (TreeC phi , TreeC phi)
\end{code}
\end{myhs}

\begin{figure}
\centering
\subfloat[|diff (Bin t u) (Bin u t)|]{%
\begin{myforest}
[,change [|Bin| [0,metavar] [1,metavar]]
         [|Bin| [1,metavar] [0,metavar]]]
\end{myforest}
}\qquad
\subfloat[|diff (Bin t u) (Tri t a u)|]{%
\begin{myforest}
[,change [|Bin| [0,metavar]       [1,metavar]]
         [|Tri| [0,metavar] [|a|] [1,metavar]]]
\end{myforest}
}
\caption{Illustration of two changes. Metavariables are denoted
with |metavar x|.}
\label{fig:pepatches:first-change}
\end{figure}

  The change that transforms |Bin t u| into |Bin u t|, for example, is
represented by a pair of |TreeC|, |(BinC (Hole 0) (Hole 1) , BinC
(Hole 1) (Hole 0))|, as seen in \Cref{fig:pepatches:first-change}.
This change works on any tree built using the |Bin| constructor and
swaps the children of the root. Note that it is impossible to define
such swap operations in terms of insertions and deletions---as used by
most diff algorithms.

\subsubsection{Applying Changes}

  Applying a change to a tree is done by unifying the the
metavariables in the deletion context with said tree, and later
instantiating the the insertion context with the obtained
substitution.

\begin{myhs}
\begin{code}
chgApply :: Change Metavar -> Tree -> Maybe Tree
chgApply (d , i) x = del d x >>= ins i
\end{code}
\end{myhs}

  Naturally, if the term |x| and the deletion context |d| are
\emph{incompatible}, this operation will fail. Contrary to regular
pattern-matching we allow variables to appear more than once on both
the deletion and insertion contexts. Their semantics are dual:
duplicate variables in the deletion context must match equal trees,
and are referred to as contractions, whereas duplicate variables in the
insertion context will duplicate trees.
Given a deletion context |ctx| and source tree |t|, the |del|
function tries to associate all the metavariables in the context with
a subtree of the input |tree|. This can be done with standard unification
algorithms, as will be the case in the generic setting. Here, however,
we use implement a simple auxiliary function to do so.

\begin{myhs}
\begin{code}
del :: TreeC Metavar -> Tree -> Maybe (Map Metavar Tree)
del ctx t = go ctx t empty
\end{code}
\end{myhs}

  The |go| function, defined below, closely follows the structure of trees and
contexts. Only when we reach a |Hole|, do we check whether we have
already instantiated the metavariable stored there or not. If we have
encountered this metavariable before, we check that both occurrences
of the metavariable correspond to the same tree; if this is the first
time we have encountered this metavariable, we simply instantiate the
metavariable with the current tree.

\begin{myhs}
\begin{code}
go :: TreeC -> Tree -> Map Metavar Tree -> Maybe (Map Metavar Tree)
go (LeafC n)     (Leaf n')    m = guard (n == n') >> return m
go (BinC x y)    (Bin a b)    m = go x a m >>= go y b
go (TriC x y z)  (Tri a b c)  m = go x a m >>= go y b >>= go z c
go (Hole i)      t            m = case lookup i m of
                                        Nothing  -> return (M.insert i t m)
                                        Just t'  -> guard (t == t') >> return m
go _             _            m = Nothing
\end{code}
\end{myhs}

  Once we have computed the substitution that unifies |ctx| and |t|,
above, we instantiate the variables in the insertion context with
their respective values, to obtain the final tree.  This phase fails
only when the change contains unbound variables. The |ins| function is
defined below.

\begin{myhs}
\begin{code}
ins :: TreeC Metavar -> Map Metavar Tree -> Maybe Tree
ins (LeafC n)     m  = return (Leaf n)
ins (BinC x y)    m  = Bin <$$> ins x m <*> ins y m
ins (TriC x y z)  m  = Tri <$$> ins x m <*> ins y m <*> ins z m
ins (Hole i)      m  = lookup i m
\end{code}
\end{myhs}

\subsubsection{Computing Changes}

  Next we will define the |chgTree| function, which
produces a change from a source and a destination.
Intuitively, the |chgTree| function should
try to exploit as many copy opportunities as possible. For now, we delegate
the decision of whether a subtree should be copied or not to an
oracle: assume we have access to a function |wcs :: Tree -> Tree ->
Tree -> Maybe Metavar|, short for \emph{``which common subtree''}.  The
call |wcs s d x| returns |Nothing| when |x| is \emph{not} a subtree of
|s| and |d|; if |x| is a subtree of both |s| and |d|, it returns |Just
i|, for some metavariable |i|.  The only condition we impose is
injectivity of |wcs s d|: that is, if |wcs s d x == wcs s d y == Just
j|, then |x == y|. In other words, equal metavariables correspond to
equal subtrees.

  There is an obvious inefficient implementation for |wcs|, that
traverses both trees searching for shared subtrees -- hence postulating
the existence of such an oracle is not a particularly strong
assumption to make. In \Cref{sec:pepatches:concreteoracle}, we provide an efficient
implementation. For now, assuming the oracle exists allows for
a clear separation of concerns.  The |chgTree| function merely
has to compute the deletion and insertion contexts, using said
oracle -- the inner workings of the oracle are abstracted away cleanly.

\begin{myhs}
\begin{code}
chgTree :: Tree -> Tree -> Change Metavar
chgTree s d  = let f = wcs s d in (extract f s, extract f d)
\end{code}
\end{myhs}

  The |extract| function receives an oracle and a tree.  It traverses
its argument tree, looking for opportunities to copy subtrees. It
repeatedly consults the oracle, to determine whether or not the
current subtree should be shared across the source and destination.
If that is the case, we want our change to \emph{copy} such
subtree. That is, we return a |Hole| whenever the second argument of
|extract| is a common subtree according to the oracle.  If the oracle
returns |Nothing|, we move the topmost constructor to the context
being computed and recurse over the remaining subtrees.

\begin{myhs}
\begin{code}
extract :: (Tree -> Maybe Metavar) -> Tree -> TreeC Metavar
extract o t = maybe (peel t) Hole (o t)
  where  peel (Leaf n)     = LeafC n
         peel (Bin a b)    = BinC (extract o a) (extract o b)
         peel (Tri a b c)  = TriC (extract o a) (extract o b) (extract o c)
\end{code}
\end{myhs}

  Note that had we used a version of |wcs| that only returns a boolean
value we would not know what metavariable to use when a subtree is
shared.  Returning a value that uniquely identifies a subtree allows
us to keep the |extract| function linear in the number of constructors
in |x| (disregarding the calls to our oracle for the moment).

  This iteration of the |chgTree| function has a subtle bug, however.
It does \emph{not} produce correct changes, that is,
it is not the case that |apply (chg s d) s == Just d| for all |s| and |d|.
The problem can be observed when we pass a source and
a destination trees where a common subtree occurs
by itself but also as a subtree of another common subtree.
Such situation is illustrated in \Cref{fig:pepatches:extract-problem}.
In particular, the patch shown in \Cref{fig:pepatches:extract-problem:res}
cannot be applied since the deletion context does not instantiate
the metavariable |metavar y|, which required by the insertion context.

\begin{figure}
\subfloat[|s|]{%
\begin{myforest}
[|Bin| [|Bin| [t] [u]] [k]]
\end{myforest}%
}\hfill%
\subfloat[|d|]{%
\begin{myforest}
[|Bin| [|Bin| [t] [u]] [t]]
\end{myforest}
}\hfill%
\subfloat[Illustration of |wcs s d|]{%
\begin{myhsFig}[.3\textwidth]%
\begin{code}
wcs s d (Bin t u)  = Just (metavar x)
wcs s d t          = Just (metavar y)
wcs s d u          = Just (metavar z)
wcs _ _ _          = Nothing
\end{code}
\end{myhsFig}
}\hfill%
\subfloat[Result of |chg s d|]{%
\begin{myforest}
[,change
  [|Bin| [x,metavar] [k]]
  [|Bin| [x,metavar] [y,metavar]]
]
\end{myforest}
\label{fig:pepatches:extract-problem:res}}%
\caption{Context extraction must care to produce
well-formed changes. The nested occurrence of |t| within |Bin t u|
here yields a change with an undefined variable on its insertion
context.}
\label{fig:pepatches:extract-problem}
\end{figure}

\begin{figure}
\centering
\subfloat[Do not share nested common subtrees.]{%
\begin{myforest}
[,change
  [|Bin| [x,metavar] [k]]
  [|Bin| [x,metavar] [t]]
]
\end{myforest}
\label{fig:pepatches:extract-sol-01:nonest}}%
\qquad\qquad
\subfloat[Expand metavariables pursuing all sharing opportunities]{%
\begin{myforest}
[,change
  [|Bin| [|Bin| [y,metavar] [z,metavar]] [k]]
  [|Bin| [|Bin| [y,metavar] [z,metavar]] [y,metavar]]
]
\end{myforest}
\label{fig:pepatches:extract-sol-01:proper}}%
\caption{Two potential solutions to the problem of nested common
subtrees, illustrated in \Cref{fig:pepatches:extract-problem}}
\label{fig:pepatches:extract-sol-01}
\end{figure}

  There are many ways to address the issue illustrated in
\Cref{fig:pepatches:extract-problem}.  We could replace |metavar y| by
|t| and ignore the sharing or we could replace |metavar x| by |Bin
(metavar y) (metavar z)|, pushing the metavariables to the leaves
maximizing sharing. These would give rise to the changes shown in
\Cref{fig:pepatches:extract-sol-01}. There is a clear dichotomy
between wanting to maximize the spine but at the same time wanting to
copy the larger trees, closer to the root. On the one hand, copies
closer to the root are intuitively easier to merge and less sharing
means it is easier to isolate changes to separate parts of the tree.
On the other hand, sharing as much as possible might capture the
change being represented more closely.

  A third, perhaps less intuitive, solution to the problem in
\Cref{fig:pepatches:extract-problem} is to only share uniquely
occurring subtrees, effectively simulating the \unixdiff{} with the
\texttt{patience} option, which only copies uniquely occurring
lines. In fact, to make this easy to experiment with, we will parameterize
our final |extract| with which \emph{context extraction
mode} should be used to computing changes.

\begin{myhs}
\begin{code}
data ExtractionMode  =  NoNested |  ProperShare |  Patience
\end{code}
\end{myhs}

  The |NoNested| mode will forget sharing in favor of copying larger
subtrees.  It would drop the sharing of |t| producing
\Cref{fig:pepatches:extract-sol:nonest}.  The |ProperShare| mode is
the opposite. It would produce
\Cref{fig:pepatches:extract-sol:proper}. Finally, |Patience| only
share subtrees that occur only once in the source and once in the
destination. For the inputs in
\Cref{fig:pepatches:extract-problem-01}, extracting contexts under
|Patience| mode would produce the same result as |NoNested|, but they
are not the same in general. In fact,
\Cref{fig:pepatches:extraction-01} illustrates the changes that would
be extracted following each |ExtractionMode| for the same source and
destination.

  In short, the |extract| function receives the \emph{sharing map} and
extracts the deletion and insertion context making up the change,
caring that the produced change is well-scoped. We will give the final
|extract| function when we get to its generic implementation. For the
time being, let us move on to the intuition behind computing the |wcs|
function efficiently for the concrete case of the |Tree| datatype.

\begin{figure}
\centering
\subfloat[Source and Destination]{%
\begin{myforest}
[,phantom, for children={fit=band}
  [|Tri|,name=r
    [|Bin| [a] [b]]
    [|Bin| [a] [b]]
    [k]]
  [|Tri|
    [|Bin| [b] [a]]
    [|Bin| [a] [b]]
    [k]]
]
\node at ($ (r) - (1.0,0) $) {|extract m|};
\end{myforest}}%
\quad
\subfloat[|m = Patience|]{%
\begin{myforest}
[,change
  [|Tri| [|Bin| [a] [b]]
         [|Bin| [a] [b]]
         [z,metavar]]
  [|Tri| [|Bin| [b] [a]]
         [|Bin| [a] [b]]
         [z,metavar]]
]
\end{myforest}
\label{fig:pepatches:extraction-01:patience}}%

\subfloat[|m = NoNest|]{%
\begin{myforest}
[,change
  [|Tri| [x,metavar]     [x,metavar] [y,metavar]]
  [|Tri| [|Bin| [b] [a]] [x,metavar] [y,metavar]]
]
\end{myforest}
\label{fig:pepatches:extraction-01:nonest}}%
\quad
\subfloat[|m = ProperShare|]{%
\begin{myforest}
[,change
  [|Tri| [|Bin| [x,metavar] [y,metavar]]
         [|Bin| [x,metavar] [y,metavar]]
         [z,metavar]]
  [|Tri| [|Bin| [y,metavar] [x,metavar]]
         [|Bin| [x,metavar] [y,metavar]]
         [z,metavar]]
]
\end{myforest}
\label{fig:pepatches:extraction-01:proper}}
\quad
\caption{Different extraction methods for the same pair or trees.}
\label{fig:pepatches:extraction-01}
\end{figure}

\subsubsection{Defining the Oracle for |Tree|}
\label{sec:pepatches:concreteoracle}

  In order to have a working version of our differencing algorithm for
|Tree| we must provide the |wcs| implementation. Recall that the |wcs|
function, \emph{which common subtree}, has type |Tree -> Tree -> Tree
-> Maybe Metavar|. Given a fixed |s| and |d|, |wcs s d x| returns
|Just i| if |x| is the $i^{\textrm{th}}$ subtree of |s| and |d| and
|Nothing| if |x| does not appear in |s| or |d|.  One implementation of
this function computes the intersection of all the subtrees in |s| and
|d|, and then search for the subtree |x| the resulting list.
Enumerating all the subtrees of any |Tree| is straightforward:

\begin{myhs}
\begin{code}
subtrees :: Tree -> [Tree]
subtrees (Leaf n)     = [Leaf n]
subtrees (Bin x y)    = Bin x y    : (subtrees x ++ subtrees y)
subtrees (Tri x y z)  = Tri x y z  : (subtrees x ++ subtrees y ++ subtrees z)
\end{code}
\end{myhs}

It is now straightforward to implement the |wcs| function: we compute
the intersection of all the subtrees of |s| and |d| and use this list
to determine whether the argument tree occurs in both |s| and
|d|. This check is done with |elemIndex| which returns the index of
the element, when it occurs in the list.

\begin{myhs}
\begin{code}
wcs :: Tree -> Tree -> Tree -> Maybe Metavar
wcs s d x = elemIndex x (subtrees s intersect sutrees d)
\end{code}
\end{myhs}

This implementation, however, is not particularly efficient.  The
inefficiency comes from two places: firstly, checking trees for
equality is linear in the size of the tree; furthermore, enumerating
all subtrees is exponential.  If we want our algorithm to be efficient
we \emph{must} have an amortized constant-time |wcs|.

  Defining |wcs s d| efficiently consists, firstly, in computing a set
of trees which contains the subtrees of |s| and |d|, and secondly, in
being able to efficiently query this set for membership.  Symbolic
manipulation software, such as Computer Algebra Systems, perform
similar computations frequently and their performance is just as
important. These systems often rely on a technique known as
\emph{hash-consing}~\cite{Goto1974,Filliatre2006}, which is part
of the canon of programming folklore. Hash-consing arises as a means of
\emph{maximal sharing} of subtrees in memory and constant time
comparison -- two trees are equal if they are stored in the same
memory location -- but it is by far not limited to it. We will be using a
variant of \emph{hash-consing} to define |wcs s d|.

  To efficiently compare trees for equality we will be using
cryptographic hash functions~\cite{Menezes1997} to construct a fixed
length bitstring that uniquely identifies a tree modulo hash
collisions.  Said identifier will be the hash of the root of the tree,
which will depend on the hash of every subtree, much like a
\emph{merkle tree}~\cite{Merkle1988}. Suppose we have a function
|merkleRoot| that computes some suitable identifier for every tree, we
can compare trees efficiently by comparing their associated
identifiers:

\begin{myhs}
\begin{code}
instance Eq Tree where
  t == u = merkleRoot t == merkleRoot u
\end{code}
\end{myhs}

  The definition of |merkleRoot| function is straightforward. It is
important that we use the |merkleRoot| of the parts of a |Tree|
to compute the |merkleRoot| of the whole. This construction,
when coupled with a cryptographic hash function, call it |hash|,
is what guarantee injectivity modulo hash collisions.

\begin{myhs}
\begin{code}
merkleRoot :: Tree -> Digest
merkleRoot (LeafH n)    = hash (concat ["1" , encode n])
merkleRoot (Bin x y)    = hash (concat ["2" , merkleRoot x , merkleRoot y])
merkleRoot (Tri x y z)  = hash (concat ["3" , merkleRoot x , merkleRoot y , merkleRoot z])
\end{code}
\end{myhs}

  Note that although it is theoretically possible to have false
positives, when using a cryptographic hash function the chance of
collision is negligible and hence, in practice, they never
happen~\cite{Menezes1997}. Nonetheless, it would be easy to detect when a
collision has occurred in our algorithm; consequently, we chose to
ignore this issue.

  Recall we are striving for a constant time comparison,
but the |(==)| definition comparing merkle roots is still linear
as it must recompute the |merkleRoot| on every comparison.
We fix this by caching the hash
associated with every node of a |Tree|.  This is done by the
|decorate| function, illustrated \Cref{fig:pepatches:decorate-conc}.

\begin{myhs}
\begin{code}
type TreeH   = (TreeH' , Digest)

data TreeH'  = LeafH | BinH TreeH  TreeH | TriH TreeH  TreeH  TreeH

decorate :: Tree -> TreeH
\end{code}
\end{myhs}

\begin{figure}
\centering
\begin{myforest}
[,phantom , s sep'+=60pt
[|Bin| , name=A [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]] [|Leaf| [|84|]]]
[|Bin, "0f42ab"|, tikz+={
        \draw [hdiff-black,->] (A.east) [out=25, in=165]to node[midway,above]{|decorate|} (!c.west);
      }
  [|Bin, "310dac"| , name=ex1
    [|Leaf, "0021ab"| [|42, "004200"|]]
    [|Leaf, "0021ab"| [|42, "004200"|]]
  ]
  [|Leaf, "4a32bd"|
    [|84, "008400"|]
  ]
]
]
\end{myforest}
%}
\caption{Example of decorating a tree with hashes, through the
|decorate| function.}
\label{fig:pepatches:decorate-conc}
\end{figure}

  We omit the implementation of |decorate| for now, even if it is
straightforward. Moreover, a generic version is introduced in
\Cref{sec:pepatches:diff}. The |TreeH| datatype carries round the
|merkleRoot| of its first component, hence, enabling us
to define |(==)| in constant time.

  The second source of inefficiency, enumerating all possible
subtrees, can be addressed by choosing a better data structure.  In
order to check whether a tree |x| is a subtree of a fixed |s| and |d|,
it suffices to check whether the merkle root of |x| appears in a
``database'' of the common merkle roots of |s| and |d|. Given that a
|Digest| is just a |[Word]|, the optimal choice for such ``database''
is a Trie~\cite{Brass2008} mapping a |[Word]| to a |Metavar|. Trie
lookups are efficient and hardly depend on the number of elements in
the trie. In fact, our lookups run in amortized constant time here, as
the length of a |Digest| is fixed.

  Finally, we are able to write our efficient |wcs| oracle that
concludes the implementation of our algorithm for the concrete
|Tree| type.  The |wcs| oracle will now receive |TreeH|, i.e.,
trees annotated with their merkle roots at every node, and will
populate the ``database'' of common digests.

\begin{myhs}
\begin{code}
wcs :: TreeH -> TreeH -> TreeH -> Maybe Metavar
wcs s d = lookup (mkTrie s intersect mkTrie d) . merkleRoot
  where  (intersect)  :: Trie k v  -> Trie k u  -> Trie k v
         lookup       :: Trie k v  -> [k]       -> Maybe v
         mkTrie       :: TreeH     -> Trie Word Metavar
\end{code}
\end{myhs}

  The use of cryptographic hashes is unsurprising. They are almost
folklore for speeding up a variety of computations. It is important to
notice that the efficiency of the algorithm comes from the novel
representation of patches combined with a amortized constant time
|wcs| function. Without being able to duplicate or permute subtrees,
the algorithm would have to backtrack in a number of situations.

%   Our technique for detecting shared subtrees is similar to
% \emph{hash-consing}~\cite{Filliatre2006} in spirit. We come back to a
% more detailed description in \Cref{secsec:related-work}.  Another
% similar line of work is the minimization of finite automata, which can
% be done in linear time~\cite{Bubenzer2014}, hence, one could imagine
% adapting such techniques for detecting shared trees without the use of
% cryptographic hashes. Nevertheless, the details are non-trivial and
% further exploration is left for future work.

\subsection{Representing Changes Generically}

  Having seen how |TreeC| played a crucial role in defining changes
for the |Tree| datatype, we continue with its generic implementation.
In this section, we generalize the construction of \emph{contexts}
to any datatype supported by the \genericssimpl{} library.

  Recall a \emph{context} over a datatype |T| is just a value of |T|
augmented with an additional constructor used to represent
\emph{holes}. This can be done with the \emph{free monad} construction
provided by the \genericssimpl{} library: |HolesAnn kappa fam ann
h| datatype (\Cref{sec:gp:simplistic:holes}) is a free monad in |h|.
We recall its definition ignoring annotations below.

\begin{myhs}
\begin{code}
data Holes kappa fam h a where
  Hole  ::                                  h a  -> Holes kappa fam h a
  Prim  :: (PrimCnstr kappa fam a)      =>  a    -> Holes kappa fam h a
  Roll  :: (CompoundCnstr kappa fam a)  =>  SRep (Holes kappa fam h) (Rep a) -> Holes kappa fam h a
\end{code}
\end{myhs}

  The |TreeC Metavar| datatype, defined in
\Cref{sec:pepatches:concrete-changes} to represent a value of type
|Tree| augmented with metavariables is isomorphic to |Holes (P [ Int ]) (P [ Tree ]) (Const Int)|.
Abstracting away the specific family for |Tree|, the datatype |Holes
kappa fam (Const Int)| gives a functor mapping an element of the
family into its representation augmented with integers, used to
represent metavariables. But in this generic setting, it does not yet
enable us to infer whether a metavariable matches over an opaque type
or a recursive position, which will come to be important soon enough.
Consequently, we will keep the information about whether the
metavariable matches over an opaque value or not:

\begin{myhs}
\begin{code}
data Metavar kappa fam at where
  MV_Prim  :: (PrimCnstr kappa fam at)      => Int -> Metavar kappa fam at
  MV_Comp  :: (CompoundCnstr kappa fam at)  => Int -> Metavar kappa fam at
\end{code}
\end{myhs}

  With |Metavar| above, we can always retrieve the |Int| identifying
the metavar, with the |metavarGet| function, but we maintain all the type-level
information we could need to inspect at run-time.
The |HolesMV| datatype below is convenient since most of the times
our |Holes| structures will contain metavariables.

\begin{myhs}
\begin{code}
metavarGet :: Metavar kappa fam at -> Int

type HolesMV kappa fam = Holes kappa fam (Metavar kappa fam)
\end{code}
\end{myhs}

  A \emph{change} consists in a pair of a deletion context and an
insertion context for the same type.  These contexts are
values of the mutually recursive family in question augmented with
metavariables.


\begin{myhs}
\begin{code}
data Chg kappa fam at = Chg  {  chgDel  :: HolesMV kappa fam at
                             ,  chgIns  :: HolesMV kappa fam at }
\end{code}
\end{myhs}

  Applying a generic change |c| to an element |x| consists in unifying |x|
with |chgDel c|, yielding a substitution |sigma| which
can be applied to |chgIns c|. This provides the usual denotational semantics
of changes as partial functions.

\begin{myhs}
\begin{code}
chgApply  :: (All Eq kappa) => Chg kappa fam at -> SFix kappa fam at -> Maybe (SFix kappa fam at)
chgApply (Chg d i) x = either  (const Nothing) (holesMapM uninstHole . flip substApply i)
                               (unify d (sfixToHoles x))
  where uninstHole _ = error "uninstantiated hole: (Chg d i) not well-scoped!"
\end{code}
\end{myhs}

  In a call to |chgApply c x|, since |x| has no holes a successful
unification means |sigma| assigns a term (no holes) for each
metavariable in |chgDel c|. In turn, when applying |sigma| to |chgIns
c| we must guarantee that every metavariable in |chgIns c|
gets substituted, yielding a term with no holes as a result.
Attempting to apply a non-well-scoped change is a violation of
the contract of |applyChg|. We throw an error on that case
and distinguish it from a change |c| not being able to be applied to |x|
because |x| is not an element of the domain of |c|.
The |uninstHole| above will be called in the precise situation
where holes were left uninstantiated in |substApply sigma (chgIns c)|

  In general, we expect a value of type |Chg| to be well-scoped, that
is, all the variables that are present in the insertion context must
also occur on the deletion context, in Haskell:

\begin{myhs}
\begin{code}
vars        :: HolesMV kappa fam at -> Map Int Arity

wellscoped  :: Chg kappa fam at -> Bool
wellscoped (Chg d i) = keys (vars i) == keys (vars d)
\end{code}
\end{myhs}

  A |Chg| is very similar to a \emph{tree matching}
(\Cref{sec:background:tree-edit-distance}) with less restrictions. In
other words, it arbitrarily maps subtrees from the source to the
destination. From an algebraic point of view, this already gives us a
desirable structure, as we will explore next in \Cref{sec:pepatches:meta-theory}.
In fact, we argue that there is no need to translate the tree matching
into an edit-script, like most traditional algorithms do. The
tree matching should be used as the representation of change.

\subsection{Meta Theory}
\label{sec:pepatches:meta-theory}

%% POTENTIAL NOTATION:
%{

%format (app (p))   = "\mathopen{\HT{\llbracket}}" p "\mathclose{\HT{\rrbracket}}\>"
%format after p q   = p "\mathbin{\HT{\bullet}}" q
%format after'      = "\HT{\bullet}"
%format iff         = "\HS{\iff}"
%format cpy         = "\HTNI{\epsilon}"
%format emptyset    = "\HVNI{\emptyset}"

  On this section we will look into how |Chg| admits a simple
composition operation which makes a partial monoid.  Through the
remainder of this section we will assume changes have all been
$\alpha$-converted to never capture names and denote the application
function of a change, |applyChg c|, as |app c|.  We will also abuse
notation and denote |substApply sigma p| by |sigma p|, whenever the
context makes it clear that |sigma| is a substitution. Finally, we
will abide by the Barendregt convention~\cite{Barendregt1984} in our
proofs and metatheory -- that is, all changes that appear in in some
mathematical context have their bound variable names independent of
each other, to put it differently, no two changes will accidentally 
share a variable name.


\begin{figure}
\subfloat[Change |p|]{%
\begin{myforest}
[,change [w,metavar] [|Bin| [w,metavar] [t]]]
\end{myforest}}\quad
\subfloat[Change |q|]{%
\begin{myforest}
[,change [|Bin| [x,metavar] [y,metavar]]
         [|Bin| [y,metavar] [x,metavar]]]
\end{myforest}}\quad
\subfloat[Composition |after p q|]{%
\begin{myforest}
[,change [|Bin| [x,metavar] [y,metavar]]
         [|Bin| [|Bin| [y,metavar] [x,metavar]] [t]]]
\end{myforest}}\enspace
\subfloat[Composition |after q p|]{%
\enspace
\begin{myforest}
[,change [w,metavar] [|Bin| [t] [w,metavar]]]
\end{myforest}\enspace}
\caption{Example of change composition. The composition usually can be applied to
less elements than its parts and is clearly not commutative.}
\label{fig:pepatches:comp-01}
\end{figure}

  The composition of two changes, say, |p| after |q|,
returns a change that maps a subset of the domain of |q|
into a subset of the image of |p|. \Cref{fig:pepatches:comp-01},
for example, illustrates two changes and their two different compositions.
In the case of \Cref{fig:pepatches:comp-01} both |after p q| and |after q p|
exist, but this is not the case generally.
The composition of two changes |after p q| is defined if and only if
the image of |app q| has elements in common with the domain of |app p|.
In other words, when |chgIns q| is unifiable with |chgDel p|.
In fact, let |sigma = unify (chgIns q) (chgDel p)|, the
composition |after p q| is given by |Chg (sigma (chgDel q)) (sigma (chgIns p))|.

\begin{myhs}
\begin{code}
(after') :: Chg kappa fam at -> Chg kappa fam at -> Maybe (Chg kappa fam at)
after p q = case unify (chgDel p) (chgIns q) of
    Left   _      -> Nothing
    Right  sigma  -> Just (Chg (substApply sigma (chgDel q)) (substApply sigma (chgIns p)))
\end{code}
\end{myhs}

  Note that it is inherent that purely structural composition of two changes
|p| after |q| yields a change, |after p q|, that potentially misses sharing
opportunities. Imagine that |p| inserts a subtree |t| that was
deleted by |q|. Our composition algorithm posses no information
that this |t| is to be treated as a copy. This also occurs in
the edit-script universe: composing patches yields worse patches
than recomputing differences. We can imagine that a more complicated
composition algorithm might be able to recover the copies
in those situations.

  We do not particularly care whether composition produces \emph{the best}
change possible or not. We do not even have a notion of \emph{best}
at the moment. It is vital, however, that it produces a correct change. That
is, the composition of two patches is indistinguishable from
the composition of their application functions.

\begin{lemma}[Composition Correct] \label{lemma:pepatches:comp-correct}
For any changes |p| and |q| and trees |x| and |y| aptly typed; we have
|app (after p q) x == Just y| if and only if
|exists z dot (app q) x == Just z && app p z == Just y|.
\end{lemma}
\begin{proof}
\begin{description}
\item[if.]
Assuming |app (after p q) x == Just y|, we want to prove there exists
|z| such that |app q x == Just z| and |app p z == Just y|. Let |sigma|
be the result of |unify (chgDel p) (chgIns q)|, witnessing |after p q|;
let |gamma| be the result of |unify (sigma (chgDel q)) x|, witnessing the
application.

Take |z = (gamma . sigma) (ctxIns q)|, and let us prove |gamma . sigma|
unifies |ctxDel p| and |z|.
\begin{squiggol}[tight]
|(gamma . sigma) (ctxDel p) == (gamma . sigma) z|
\reasonRel{\iff}{|z| \text{ has no variables}}
|(gamma . sigma) (ctxDel p) == z|
\reasonRel{\iff}{\text{definition of } |z|}
|(gamma (sigma (ctxDel p)) == gamma (sigma (ctxIns q))|
\reasonRel{\;\Longleftarrow\;}{\text{hypothesis}}
|sigma (ctxDel p) == sigma (ctxIns q)|
\end{squiggol}

Hence, |p| can be applied to |z|, and the result is |(gamma . sigma) (ctxIns p)|,
which by hypothesis, is equal to |y|.

\item[only if.]
Assuming there exists |z| such that |app q x == Just z| and
|app p z == Just y|, we want to prove that |app (after p q) x == Just y|.
Let |alpha| be such that |alpha (ctxDel q) == x|, hence, |z == alpha (ctxIns q)|;
Let |beta| be such that |beta (ctxDel p) == z|, hence |y == beta (ctxIns p)|.
\begin{enumerate}
\item First we prove that |after p q| is defined, that is,
there exists |sigma'| that unifies |ctxIns q| and |ctxDel p|.
Recall |alpha| and |beta| have disjoint variables
because we assume |p| and |q| have a
disjoint set of names. Let |sigma' = alpha `union` beta|,
which corresponds to |alpha . beta| or
|beta . alpha| because of they have disjoint set of names.
%
\begin{squiggol}[tight]
|sigma'  (ctxIns q)  ==  sigma'  (ctxDel p)|
\reasonRel{\iff}{\text{disjoint supports}}
|alpha (ctxIns q) == beta (ctxDel p)|
\reasonRel{\iff}{\text{definition of } |z|}
|z == beta (ctxDel p)|
\end{squiggol}

Since |sigma'| unifies |ctxIns q| and |ctxDel p|, let
|sigma| be their \emph{most general unifier}.
Then, |sigma' == gamma . sigma| for some |gamma| and
|after p q == Chg (sigma (ctxDel q)) (sigma (ctxIns p))|.

\item Next we prove |app (after p q) x == Just y|.
First we prove |sigma (ctxDel q)| unifies with |x|.
%
\begin{squiggol}[tight]
|x == beta (ctxDel q)|
\reasonRel{\iff}{\text{Disj. supports};\text{Def. }|sigma'|}
|x == gamma (sigma (ctxDel q))|
\reasonRel{\iff}{|x| \text{ has no variables}}
|gamma x == gamma (sigma (ctxDel q))|
\end{squiggol}

Hence, |app (after p q) x| evaluates to |gamma (sigma (ctxIns p))|.
Proving it coincides with |y| is a straightforward calculation:
%
\begin{squiggol}[tight]
|gamma (sigma (ctxIns p)) == y|
\reasonRel{\iff}{\text{Def. }|y|}
|gamma (sigma (ctxIns p)) == alpha (ctxIns p)|
\reasonRel{\iff}{\text{Disj. supports};\text{Def. }|sigma'|}
|gamma (sigma (ctxIns p)) == gamma (sigma (ctxIns p))|
\end{squiggol}
\end{enumerate}
\end{description}
\end{proof}

  Once we have established that composition is correct with respect to
application, we would like to ensure composition is associative. But
first we need to specify what we mean by \emph{equal} changes. We will
consider an extensional equality over changes. Two changes are said to
be equivalent if and only if they are indistinguishable through their
application semantics.

%format ~~ = "\HT{\approx}"
\begin{definition}[Change Equivalent]
Two changes |p| and |q| are said to be equivalent, denoted |p ~~ q|,
if and only if |forall x dot (app p x) == (app q x)|
\end{definition}

\begin{lemma}[Definability of Composition] \label{lemma:pepatches:comp-def}
Let |p|, |q| and |r| be aptly typed changes, then,
|after (after p q) r| is defined if and only if |after p (after q r)|
is defined.
\end{lemma}
\begin{proof}
\begin{description}
\item[if.] Assuming |after (after p q) r| is defined,
Let |sigma| and |theta| be such that |sigma (ctxDel p) == sigma (ctxIns q)|
and |theta (sigma (ctxDel q)) == theta (ctxIns r)|.
We must prove that (a) |ctxIns r| unifies with |ctxDel q| through some
substitution |theta'| and (b) |sigma' (ctxIns q)| unifies with |ctxDel p|.
Take |theta' = theta . sigma|, then:
%
\begin{squiggol}[tight]
|(theta . sigma) (ctxIns r) == (theta . sigma) (ctxDel q)|
\reasonRel{\iff}{|support sigma intersect vars r == emptyset|}
|theta (ctxIns r) == (theta . sigma) (ctxDel q)|
\end{squiggol}

Let |zeta| be the idempotent \emph{most general unifier} of |ctxIns r| and
|ctxDel q|, it follows that |theta' = gamma . zeta| for some |gamma|.
Consequently, |after q r = Chg (zeta (ctxDel r)) (zeta (ctxIns q))|.

Now, we must construct |sigma'| to unify |ctxDel p| and |zeta (ctxIns q)|,
which enables the construction of |after p (after q r)|.
Let |sigma' = theta . sigma| and reduce it to one of our assumptions:
%
\begin{squiggol}[tight]
|theta (sigma (ctxDel p)) == theta (sigma (zeta (ctxIns q)))|
\reasonRel{\iff}{|theta . sigma == gamma . zeta|}
|theta (sigma (ctxDel p)) == gamma (zeta (zeta (ctxIns q)))|
\reasonRel{\iff}{|zeta|\text{ idempotent}}
|theta (sigma (ctxDel p)) == gamma (zeta (ctxIns q))|
\reasonRel{\iff}{|theta . sigma == gamma . zeta|}
|theta (sigma (ctxDel p)) == theta (sigma (ctxIns q))|
\noreasonRel{\;\Longleftarrow\;}
|sigma (ctxDel p) == sigma (ctxIns q)|
\end{squiggol}

\item[only if.] Analogous.
\end{description}
\end{proof}

\begin{lemma}[Associativity of Composition] \label{lemma:pepatches:comp-assoc}
Let |p|, |q| and |r| be aptly typed changes such
that |after (after p q) r| is defined, then
|after (after p q) r ~~ after p (after q r)|.
\end{lemma}
\begin{proof}
Straightforward application of \Cref{lemma:pepatches:comp-def} and
\Cref{lemma:pepatches:comp-correct}.
\end{proof}

\begin{lemma}[Identity of Composition] \label{lemma:pepatches:comp-id}
Let |p| be a change, then |cpy = Chg (metavar x) (metavar x)| is
the identity of composition. That is, |after p cpy ~~ p ~~ after cpy p|.
\end{lemma}
\begin{proof}
Trivial; |cpy| unifies with all possible terms.
\end{proof}

  \Cref{lemma:pepatches:comp-assoc,lemma:pepatches:comp-id} establish
a partial monoid structure for |Chg| and |after| under extensional
change equality, |~~|. As we shall see next, however, it is not
trivial to squeeze more structure out of this change representation.
\digress{I would have enjoyed to be able to spend more time studying
the metatheory. Obviously, it is not because the options discussed
next failed that there exists no options to extend the metatheory
whatsoever. It is still worth discussing the difficulties I encountered
while trying to use standard techniques, below.}

\subsubsection{Loose Ends}

%format (inv p) = p "^{\HVNI{-1}}"
  The first thing that comes to mind is the definition of
the inverse of a change. Since changes are well-scoped, that is,
|vars (chgDel p) == vars (chgIns p)| for any change |p|,
defining the inverse of a change |p|, denoted |inv p|, is trivial:

\begin{myhs}
\begin{code}
inv :: Chg kappa fam at -> Chg kappa fam at
inv p = Chg (chgIns p) (chgDel p)
\end{code}
\end{myhs}

  Naturally, then, we would expect that |after p (inv p) ~~ cpy|, but
that is not the case. The domain of |cpy| is the entire set of trees,
but the domain of |after p (inv p)| is generally strictly smaller.
Consequently, we can easily find a tree |t| such that |app cpy t ==
Just t| but |app (after p (inv p)) == Nothing|. Take, for example,
the change shown in \Cref{fig:pepatches:inv-not-id}.

\begin{figure}
\centering
\subfloat[Change |p|]{%
\begin{myforest}
[,change [|Bin| [|Leaf| [|42|]] [x,metavar]] [x,metavar]]
\end{myforest}}%
\quad
\subfloat[Change |inv p|]{%
\begin{myforest}
[,change [x,metavar] [|Bin| [|Leaf| [|42|]] [x,metavar]]]
\end{myforest}}%
\quad
\subfloat[|after (inv p) p|]{%
\begin{myforest}
[,change [|Bin| [|Leaf| [|42|]] [x,metavar]] [|Bin| [|Leaf| [|42|]] [x,metavar]]]
\end{myforest}}
\caption{Example of a change, its inverse and their composition}
\label{fig:pepatches:inv-not-id}
\end{figure}

%format subseteq = "\HS{\subseteq}"

  The problem with inverses above stems from |after p
(inv p)| being \emph{less general} than the identity, since it has a
smaller domain.  In other words, |after p (inv p)| works on a subset
of the domain of |cpy|, but it performs the same action as |cpy| for
the elements it is defined. It is natural then to attempt to talk about
changes modulo their domain. We could think of stating |p <= q| whenever
|(app p) subseteq (app q)|. That is, when |p| and |q| are the same
except that the domain of |q| is larger. This |<=| is known
as the usual \emph{extension order}~\cite{Robinson1988}, and when
instantiated for our particular case, yields the definition below.

\begin{definition}[Extension Order]
Let |p| and |q| be two aptly typed changes; we say that |q| is
an extension of |p|, denoted |p <= q|, if and only if
|forall x `elem` dom p dot (app p) x == (app q) x|.
In other words, |p <= q| when |q| coincides with |p| in a restriction
of its domain.
\end{definition}

%format ~  = "\HS{\sim}"
%format /~ = "\HS{\nsim}"

  This gives us a partial order on changes and it is the case that
|after p (inv p) <= cpy| and |after (inv p) p <= cpy|. Attempting
to identify |after p (inv p)| as somehow equivalent to |cpy| using |<=|
will not work, however.

  We could think of defining a notion of \emph{approximate changes},
denoted |p ~ q|, by estabilishing whether |p| and |q| are comparable
under |<=|. Since |<=| is not total, however. this would not yeild
an equivalence relation (transitivity does not hold, illustrated in
\Cref{pepatches:approx-not-equiv}).

\begin{figure}
\centering
\subfloat[Change |p|]{%
\begin{myforest}
[,change
  [|Bin| [|Bin| [a,metavar] [b,metavar]] [c,metavar]]
  [|Bin| [c,metavar] [|Bin| [a,metavar] [b,metavar]]]]
\end{myforest}
\label{fig:pepatches:approx-not-equiv:A}}
\quad
\subfloat[Change |q|]{%
\begin{myforest}
[,change
  [|Bin| [t,metavar] [u,metavar]]
  [|Bin| [u,metavar] [t,metavar]]]
\end{myforest}
\label{fig:pepatches:approx-not-equiv:B}}
\quad
\subfloat[Change |r|]{%
\begin{myforest}
[,change
  [|Bin| [x,metavar] [|Bin| [y,metavar] [z,metavar]]]
  [|Bin| [|Bin| [y,metavar] [z,metavar]] [x,metavar]]]
\end{myforest}
\label{fig:pepatches:approx-not-equiv:C}}
\caption{Three changes such that |p ~ q| (because |p <= q|) and |q ~ r| (because |r <= q|). Yet, |p /~ r| since its not the case that |r <= p| or |p <= r| holds.}
\label{fig:pepatches:approx-not-equiv}
\end{figure}

  The extension order cannot be used to define the \emph{best}
change between two elements |x| and |y|. Take |x| to be |Bin (Bin a b) a|
and |y| to be |Bin (Bin b a) a|, for which two uncomparable candidate
changes are shwon in \Cref{fig:pepatches:ext-ord-not-cost}.

  This short discussion does not mean that there is \emph{no} suitable
way to compare the changes in \Cref{fig:pepatches:ext-ord-not-cost} or
to define |~| in such a way that the changes in
\Cref{fig:pepatches:approx-not-equiv} can be considered equivalent. It
does mean, however, that simply comparing the domain of changes is a
weak definition and a robust definition will probably be significantly
more involved.

\begin{figure}
\centering
\subfloat[Change |p|]{%
\begin{myforest}
[,change
  [|Bin| [|Bin| [x,metavar] [y,metavar]] [a]]
  [|Bin| [|Bin| [y,metavar] [x,metavar]] [a]]]
\end{myforest}
\label{fig:pepatches:approx-not-equiv:A}}
\quad
\subfloat[Change |q|]{%
\begin{myforest}
[,change
  [|Bin| [|Bin| [a,metavar] [y,metavar]] [a,metavar]]
  [|Bin| [|Bin| [y,metavar] [a,metavar]] [a,metavar]]]
\end{myforest}
\label{fig:pepatches:approx-not-equiv:B}}
\caption{Two changes that could be used to transform the same element |x|
but are not comparable under the extension order |(<=)|.}
\label{fig:pepatches:ext-ord-not-cost}
\end{figure}



%}
%%% END OF TEMPORARY NOTATION


\subsection{Computing Changes}
\label{sec:pepatches:diff}

  Having seen how |Chg| have the basic properties we would expect, we
move on to how to computing them. In this section we will define the generic
counterpart to the |chgTree| function, from
\Cref{sec:pepatches:concrete-changes}. Recall that the differencing
algorithm starts by computing the \emph{sharing map} of its source |s|
and destination |d|, which enable us to efficiently decide if a given
tree |x| is a subtree of |s| and |d|.  Later, a second pass uses this
sharing map and \emph{extracts} the deletion and insertion contexts,
according to some of the extraction modes.  The extraction modes
ensure we will produce well-scoped changes, \Cref{fig:pepatches:extract-sol-01}.

\begin{myhs}
\begin{code}
data ExtractionMode  =  NoNested | ProperShare | Patience
\end{code}
\end{myhs}

  The \emph{sharing map} is central to the efficiency of the
differencing algorithm, but it marks subtrees for sharing regardless
of underlying semantics, which can be a problem when the trees in
question represent complex structures such as abstract syntax
trees. We must be careful not to \emph{overshare} trees.  Imagine a
local variable declaration \verb!int x = 0;! inside an arbitrary
function. This declaration should \emph{not} be shared with another
syntactically equal declaration in another function.  A careful
analysis of what can and cannot be shared would require
domain-specific knowledge of the programming language in question.
Nevertheless, we can impose different restrictions that make it
\emph{unlikely} that values will be shared across scope boundaries.  A
simple and effective such measure is not sharing subtrees with height
strictly less than one (or a configurable parameter). This keeps
constants and most variable declarations from being shared,
effectively avoiding the issue.  \digress{I would like to reiterate
the \emph{avoiding-the-issue} aspect of this decision. I did attempt
to overcome this with a few methods which will be discussed later
(\Cref{sec:pepatches:discussion}). None of my attempts at solving the
issue were successful, hence, the best option really became avoiding
the issue by making sure that we can easily exclude certain trees from
being shared.}

\subsubsection{Which Common Subtree, Generically}

  Similarly to the concrete example from \Cref{sec:pepatches:concrete-patches},
the first thing we must do is annotate our trees with hashes at
every point. Gladly, the |Holes| datatype from \genericssimpl{}
also supports annotations. Unlike the concrete example, however,
we will also keep the height of each tree to enable us to easily
forbid sharing trees smaller than a certain height.
The |PrepFix| datatype, defined below, serves the same purpose as
the simpler |TreeH|, from our concrete example.

\begin{myhs}
\begin{code}
data PrepData a = PrepData { getDigest :: Digest , getHeight :: Int }

type PrepFix kappa fam = SFixAnn kappa fam PrepData
\end{code}
\end{myhs}

  The |decorate| function can be written with the help of
synthesized attributes (\Cref{sec:gp:annfix}). The homonym
|synthesize| function from \genericssimpl{} serves this very purpose.
We omit the algebra passed to synthesize but invite the interested
reader to check |Data.HDiff.Diff.Preprocess| in the source
(\Cref{chap:where-is-the-code}).

\begin{myhs}
\begin{code}
decorate  :: (All Digestible kappa) => SFix kappa fam at -> PrepFix kappa fam at
decorate  = synthesize dots
\end{code}
\end{myhs}

%% \begin{figure}
%% %{
%% %format WD c ha he = "\begin{array}{c} \HS{hash}\HS{=}" ha " \\ \HS{height}\HS{=}" he " \\"  c " \end{array}"
%% \centering
%% \begin{myforest}
%% [,phantom , s sep'+=60pt
%% [|Bin| , name=A [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]] [|Leaf| [|84|]]]
%% [|WD Bin "0f42ab" 3|, tikz+={
%%         \draw [hdiff-black,->] (A.east) [out=25, in=165]to node[midway,above]{|decorate|} (!c.west);
%%       }
%%   [|WD Bin "310dac" 2| , name=ex1
%%     [|WD Leaf "0021ab" 1| [|WD 42 "004200" 0|]]
%%     [|WD Leaf "0021ab" 1| [|WD 42 "004200" 0|]]
%%   ]
%%   [|WD Leaf "4a32bd" 1|
%%     [|WD 84 "008400" 0|]
%%   ]
%% ]
%% ]
%% \end{myforest}
%% %}
%% \caption{Example of decorating a tree with hashes, through the
%% |decorate| function.}
%% \label{fig:pepatches:decorate}
%% \end{figure}

  The algebra used by |decorate|, above, computes a hash at each constructor
of the tree. The hashes are computed from the a unique identifier per constructor
and a concatenation of the hashes of the subtrees. The hash of the
root in \Cref{fig:pepatches:decorate-conc}, for example, is computed with
a call to |hash (concat ["Main.Tree.Bin", "310dac", "4a32bd"])|.  This
ensures that hashes uniquely identify a subtree modulo hash
collisions.

  After preprocessing the input trees we traverse them and insert
every hash we see in a hash map from hashes to integers.  These
integers count how many times we have seen a tree, indicating the
arity of a subtree. Shared subtrees occur with arity of at least two:
once in the deletion context and once in the insertion context.  The
underlying datastructure is a |Int64|-indexed trie~\cite{Brass2008} as
our datastructure. \digress{I would like to also implemented this
algorithm with a big-endian Patricia Tree~\cite{Okasaki1998} and
compare the results. I think the difference would be small, but worth
considering when working on a production implementation}.

\begin{myhs}
\begin{code}
type Arity = Int

buildArityMap :: PrepFix a kappa fam ix -> Trie Arity
\end{code}
\end{myhs}

  A call to |buildArityMap| with the annotated tree shown in
\Cref{fig:pepatches:decorate-conc}, for example, would
yield the following map.

\begin{myhs}
\begin{code}
fromList  [("0f42ab",  1),  ("310dac",  1),  ("0021ab",  2) ,("004200",  2), dots]
\end{code}
\end{myhs}

  After processing the \emph{arity} maps for both
the source tree and destination tree, we construct the \emph{sharing}
map. Which consists in the intersection of the arity maps and a final
pass adding a unique identifier to every key. We also keep
track of how many metavariables were assigned, so we can always
allocate fresh names without having to go inspect the whole map again.
This is just a technical consequence of working with binders explicitly.

\begin{myhs}
\begin{code}
type MetavarAndArity = MAA {getMetavar :: Int , getArity :: Arity}

buildSharingMap  :: PrepFix a kappa fam ix -> PrepFix a kappa fam ix
                 -> (Int , Trie MetavarAndArity)
buildSharingMap x y  =   T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
                     $$  T.zipWith (+) (buildArityMap x) (buildArityMap y)
\end{code}
\end{myhs}

  The final |wcs s d| is straightforward: we preprocess the trees
with their hash and height then compute their sharing map, which
is used to lookup the common subtrees. Yet, the whole point
of preprocessing the trees was to avoid the unnecessary recomputation
of their hashes. Consequently, we are better off carrying these
preprocessed trees everywhere through the computation of changes. The
final |wcs| function will have its type slightly adjusted and is
defined below.

\begin{myhs}
\begin{code}
wcs  :: (All Digestible kappa) => PrepFix kappa fam at -> PrepFix kappa fam at
     -> PrepFix kappa fam at -> Maybe Int
wcs s d =  let m = buildSharingMap s d
           in famp getMetavar . flip T.lookup m . getDigest . getAnnot
\end{code}
\end{myhs}

  Let |f = wcs s d| for some |s| and |d|. Computing |f| itself
is linear and takes $\mathcal{O}(n + m)$ time, where |n| and |m|
are the number of constructors in |s| and |d|. A call to |f x| for
some |x|, however, is answered in $\mathcal{O}(1)$ due to the
bounded depth of the patricia tree.

  We chose to use a cryptographic hash function~\cite{Menezes1997}
and ignore the remote possibility of hash collisions,
even if it would not be hard to detect these collisions whilst
computing the arity map. To do so, we should store the tree with its associated
hash instead of only storing the hash. Then, on every insertion we could check
that the inserted tree matches with the tree already in the map.
\digress{If I had used a non-cryptographic hash, which are much faster to
compute than cryptographic hash functions, I would have had to
employ the collision detection mechanism above. This would
cost a significant amount of time. Hence, it is worth paying the
price for a more expensive hash function.}

\subsubsection{Context Extraction}
\label{sec:pepatches:extract}

  After computing the set of common subtrees, we must decide which of
those subtrees should be shared. Shared subtrees are abstracted by a
metavariable in every location they would occur in the deletion and
insertion contexts.

  Recall we chose to never share subtrees with height
smaller than a given parameter. Our choice is very pragmatic in the
sense that we can preprocess the necessary information and
it effectively avoids most of the oversharing without involving
domain specific knowledge. The |CanShare| below is a synonym for
a predicate over trees used to decide whether we can share a
given tree or not.

\begin{myhs}
\begin{code}
type CanShare kappa fam = forall ix dot PrepFix kappa fam ix -> Bool
\end{code}
\end{myhs}

  The |extract| function takes an |ExtractionMode|, a sharing map
and a |CanShare| predicate and two preprocessed fixpoints to extract
contexts from. The reason we receive two trees at the same time and produce two
contexts is because modes like |NoNested| perform some
cleanup that depends on global information.

\begin{myhs}
\begin{code}
extract  :: ExtractionMode -> CanShare kappa fam -> IsSharedMap
         -> (PrepFix kappa fam :*: PrepFix kappa fam) at -> Chg kappa fam at
\end{code}
\end{myhs}

  \digress{To some extent, we could compare context extraction to the
translation of tree mappings into edit-scripts: our tree matching is
encoded in |wcs| and instead of computing an edit-scripts, we compute
terms with metavariables.  Classical algorithms are focused in
computing the \emph{least cost} edit-script from a given tree
mapping. In our case, the notion of \emph{least cost} hardly makes
sense -- besides not having defined a cost semantics to our changes,
we are interested in those that merge better which might not
necessarily be those that insert and delete the least amount of
constructors. Consequently, there is a lot of freedom in defining our
context extraction techniques. We will look at three particular
examples next, but I sketch other possibilities later
(\Cref{sec:pepatches:discussion}).}

\paragraph{Extracting with |NoNested|}
Extracting contexts with the |NoNested| mode happens in two passes.
We first extract the contexts naively, then make a second pass
removing the variables that appear exclusively in the insertion.
To keep the extraction algorithm linear is important to \emph{not}
forget which common subtrees have been substituted on the first pass.
Hence, we create a context that contains metavariables and their
associated tree.

\begin{myhs}
\begin{code}
noNested1  :: CanShare kappa fam -> Trie MetavarAndArity -> PrepFix kappa fam at
           -> Holes kappa fam (Const Int :*: PrepFix a kappa fam) at
noNested1 h sm x@(PrimAnn _    xi) = Prim xi
noNested1 h sm x@(SFixAnn ann  xi)
  =  if h x  then  maybe recurse (mkHole x) $$ lookup (getDigest ann) sm
             else  recurse
 where  recurse     = Roll (repMap (noNested1 h sm) xi)
        mkHole x v  = Hole (Const (getMetavar v) :*: x)
\end{code}
\end{myhs}

  The second pass maps over the holes in the output from the first pass
and decides whether to transform the
|Const Int| into a |Metavar kappa fam| or whether to forget this was a
potential shared tree and keep the tree instead. We will omit the
implementation of the second pass. It consists in a straightforward
traversal of the output of |noNested1|, we direct the interested
reader to check |Data.HDiff.Diff.Modes| in the source code for more
details (\Cref{chap:where-is-the-code}).

\paragraph{Extracting with |Patience|}
The |Patience| extraction can be done in a single pass.
Unlike |noNested1| above, instead of simply looking a hash up
in the sharing map, it will further check that the given hash
occurs with arity two -- indicating the tree in question
occurs once in the source tree and once in the destination.
This completely bypasses the issue with |NoNested| producing
insertion contexts with undefined variables and requires
no further processing. The reason for it is that the variables
produced will appear with the same arity as the trees they abstract,
and in this case, it will always be two: once in the deletion context
and once in the insertion context.

\begin{myhs}
\begin{code}
patience  :: CanShare kappa fam -> Trie MetavarAndArity -> PrepFix a kappa fam at
          -> Holes kappa fam (Metavar kappa fam) at
patience h sm x@(PrimAnn _    xi) = Prim xi
patience h sm x@(SFixAnn ann  xi)
  =  if h x  then  maybe recurse (mkHole x) $$ lookup (getDigest ann) sm
             else  recurse
 where  recurse     = Roll (repMap (patience h sm) xi)
        mkHole x v  | getArity v == 2  = Hole (MV_Comp (getMetavar v))
                    | otherwise        = sfixToHoles x
\end{code}
\end{myhs}

\paragraph{Extracting with |ProperShares|}
The |ProperShares| method prefers sharing smaller subtrees more times
instead of but bigger subtrees, which might shadow nested commonly occurring
subtrees (\Cref{fig:pepatches:extract-problem}).

  Given a source |s| and a destination |d|,
we say that a tree |x| is a \emph{proper-share} between |s| and
|d| whenever no subtree of |x| occurs in |s| and |d| with arity greater
than that of |x|. In other words, |x| is a proper-share if
and only if all of its subtrees occur only as subtrees of
other occurrences of |x|. For the two trees below, |u| is a proper-share
but |Bin t u| is not: |t| occurs once \emph{outside} |Bin t u|.

\begin{center}
\begin{myforest}
[,phantom,l=0mm,s sep=12mm
  [|Bin| [|Bin| [t] [u]] [k]]
  [|Bin| [|Bin| [t] [u]] [t]]]
\end{myforest}
\end{center}

  Extracting contexts with under the |ProperShare| mode
consists in annotating the source and destination trees with
a boolean indicating whether or not they are a proper share,
then proceeding just like |Patience|, but instead of checking
that the arity must be two, we check that the tree is classified
as a \emph{proper-share}. It is important to use annotated fixpoints
to maintain performance, but the code is very similar to the previous
two methods and, hence, omitted.


\paragraph{The |chg| function.}  Finally, the generic |chg| function
receives a source and destination trees, |s| and |d|, and computes a
change that encodes the information necessary to transform the source
into the destination according to some extraction mode |extMode|.
In our prototype, the extraction mode comes from a command line option.

\begin{myhs}
\begin{code}
chg  :: (All Digestible kappa) => SFix kappa fam at -> SFix kappa fam at -> Patch kappa fam at
chg x y =  let  dx             = decorate x
                dy             = decorate y
                (_, sh)        = buildSharingMap opts dx dy
            in extract extMode canShare (dx :*: dy)
 where
   canShare t = 1 < treeHeight (getConst (getAnn t))
\end{code}
\end{myhs}

\section{The Type of Patches}
\label{sec:pepatches:patches}

\begin{figure}
\centering
\subfloat{%
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [z,metavar]]
  [|Bin| [|Leaf| [|84|]] [|Bin| [z,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-04:B}}%
\quad\quad\quad
\subfloat{%
\begin{myforest}
[,change
  [|Bin| [x,metavar] [|Leaf| [|5|]]]
  [|Bin| [x,metavar] [|Leaf| [|6|]]]
]
\end{myforest}
\label{fig:pepatches:example-04:A}}%
\caption{Simple Example of disjoint changes. The leftmost change operates solely
on the left child of the root whereas the rightmost change operates
solely on the right child.}
\label{fig:pepatches:example-04}
\end{figure}

  Up until now we have sen how how \emph{changes}
consisting in a deletion and a insertion context are a suitable
representation for encoding transformations between trees.
In fact, changes are very similar to \emph{tree matchings}
(\Cref{sec:background:tree-edit-distance}) with less restrictions.
From a synchronization point of view, however, these \emph{changes}
are very difficult to merge. They do not explicitly encode
enough information for that.

  Synchronizing changes requires us to understand which
constructors in the deletion context are, in fact, just being copied
over in the insertion context. Take \Cref{fig:pepatches:example-04},
where one change operates exclusively on the right child of a binary
tree whereas the other alters the left child and duplicates the right
child in-place.  These changes are clearly \emph{disjoint}, since they
modify the content of different subtrees of the source. Consequently
it should be possible to be automatically synchronize them.
To recognize them as \emph{disjoint} changes, though
will require more information than what is provided by |Chg|.

  Observing the definition of |Chg| reveals that the deletion context
might \emph{delete} many constructors that that are being inserted,
in the same place, by the insertion context. The changes from
\Cref{fig:pepatches:example-04}, for example, conceal the fact that the |Bin| at the root of the source tree is, in fact, being copied in both changes.
Following the \texttt{stdiff} nomenclature, the |Bin| at
the root of both changes in \Cref{fig:pepatches:example-04} should be
places in the \emph{spine} of the patch.  That is, it is copied over
from source to destination but it leads to changes further down the
tree.

\begin{figure}
\centering
\subfloat[Insertion as a \emph{change}]{%
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Bin| [|Leaf| [|42|]] [|Bin| [|Leaf| [| 84|]] [x,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-02:chg}}%
\quad\quad\quad
\subfloat[Insertion as a \emph{patch}]{%
\begin{myforest}
[|Bin|,s sep = 5mm%make it wider
  [|Leaf| [|42|]]
  [,change [x,metavar] [|Bin| [|Leaf| [|84|]] [x,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-02:patch}}%
\caption{A change with redundant information on the left
and its minimal representation on the right, with an
evident \emph{spine}.}
\label{fig:pepatches:example-02}
\end{figure}

  A \emph{patch}, then, captures the idea of many individual
changes operating over separate parts of the source tree. It consists in
a spine that leads to changes in its leaves, and is defined by the type
|Patch| below.

\begin{myhs}
\begin{code}
type Patch kappa fam = Holes kappa fam (Chg kappa fam)
\end{code}
\end{myhs}

  \Cref{fig:pepatches:example-02} illustrates the
difference between patches and changes graphically.  In
\Cref{fig:pepatches:example-02:chg} we see |Bin (Leaf 42)| being
repeated in both contexts -- whereas in
\Cref{fig:pepatches:example-02:patch} it has been placed in the spine
and consequently, is clearly identified as a copy.

% Two changes that operate on disjoint
% subtrees -- have different paths from the root -- are trivially
% disjoint and, therefore, trivially synchronizable.  This does not
% immediately means that two changes that operate on the same subtree
% are \emph{not} disjoint, but that will require more refined
% checks. The important takeaway is that working with monolithic changes
% that operate over the whole tree is undesirable from the perspective of
% defining a merge operation.

\begin{figure}
\centering
\subfloat[\emph{well-scoped} swap, as a |Chg|]{%
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [|Bin| [x,metavar] [y,metavar]]]
  [|Bin| [|Leaf| [|42|]] [|Bin| [y,metavar] [x,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-03:A}}

\subfloat[\emph{globally-scoped} swap patch]{%
\begin{myforest}
[|Bin|, s sep = 5mm
 [|Leaf| [|42|]]
 [|Bin|,s sep = 5mm%make it wider
  [,change [x,metavar] [y,metavar]]
  [,change [y,metavar] [x,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-03:B}}%
\quad\quad\quad
\subfloat[\emph{locally-scoped} swap patch]{%
\begin{myforest}
[|Bin|, s sep = 5mm
 [|Leaf| [|42|]]
 [,change
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-03:C}}%
\caption{A change that swaps some elements; naive anti-unification of the
deletion and insertion context breaking scoping; and finally the
patch with minimal changes.}
\label{fig:pepatches:example-03}
\end{figure}

  Patches are computed from changes by
extracting common constructors from the
deletion and insertion contexts into the spine. In other words, we
would like to push the changes down towards the leaves of the
tree. There are two different ways for doing so, illustrated by
\Cref{fig:pepatches:example-03}.  On one hand we can consider the
patch metavariables to be \emph{globally-scoped}, yielding
structurally minimal changes, \Cref{fig:pepatches:example-03:B}.  On
the other hand, we could strive for \emph{locally-scoped}, where each
change might still contain repeated constructors as long as they are
necessary to ensure the change is \emph{closed}, as in
\Cref{fig:pepatches:example-03:C}.

  The first option, of \emph{globally-scoped} patches, is
very easy to compute. All we have to do is to compute the
anti-unification of the insertion and deletion context.

\begin{myhs}
\begin{code}
globallyScopedPatch :: Chg ki codes at -> PatchPE ki codes at
globallyScopedPatch (Chg d i) = holesMap (uncurry' Chg) (lgg d i)
\end{code}
\end{myhs}

  \emph{Globally-scoped} patches are easy to compute but contribute
little information from a synchronization point of view.  To an
extent, it makes merging even harder. Take
\Cref{fig:pepatches:misalignment}, where a globally scoped patch is
produced from a change.  It is harder to understand that the |(: 42)|
is being deleted by looking at the globally-scoped patch than by
looking at the change.  This is because the first |(:)| constructor is
considered to be in the spine by the naive anti-unification algorithm,
which proceeds top-down.  A bottom-up approach is also unpractical, we
would have to decide which leaves to pair together and it would suffer
similar issues for data inserted on the tail of linearly-structured
data.


\begin{figure}
\centering
\subfloat[Change that deletes |42| at the head of a list.]{%
\begin{myforest}
[,change , s sep=1mm
  [|(:)| [|42|] [|(:)| [x,metavar] [|(:)| [y,metavar] [z,metavar]]]]
  [|(:)| [x,metavar] [|(:)| [y,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:misalignment:A}}
\quad\quad
\subfloat[Top-down spine obscuring deletion at head.]{%
\begin{myforest}
[|(:)| , s sep=-3mm
  [,change [|42|] [x,metavar]]
  [|(:)|, s sep=4mm
    [,change [x,metavar] [y,metavar]]
    [,change [|(:)| [y,metavar] [z,metavar]] [z,metavar]]]]
\end{myforest}
\label{fig:pepatches:misalignment:B}}%
\caption{Globally-scoped patches resulting
in misalignment of metavariables due to deletions
in the head of linearly-structured data.}
\label{fig:pepatches:misalignment}
\end{figure}

  \emph{Locally-scoped} patches implies that
changes might still contain repeated constructors in the root
of their deletion and insertion contexts -- hence they will not be
structurally minimal. Although more involved to compute, they
give us a change to address insertions and deletions
of constructors before we end up misaligning copies.

  Independently of global or local scoping,
ignoring the information about the spine yields a forgetful
functor from patches back into changes, named |chgDistr|.
Its definition is straightforward thanks to to the free monad structure
of |Holes|, which gives us the necessary monadic multiplication.
We must care that |chgDistr| will not
capture variables, that is,
all metavariables must have already been properly $\alpha$-converted.
We cannot enforce this invariant directly in the |chgDistr| function for
performance reasons, consequently, we must manually ensure that all
scopes contains disjoint sets of names and therefore can be
safely distributed whenever applicable. This is a usual difficulty
when handling objects with binders, in general.
\digress{I wonder how an
implementation using De Bruijn indexes would look like. I'm not
immediately sure it would be easier to enforce correct indexes. Through
the bowels of the code we ensure two changes have disjoint sets of
names by adding the successor of the maximum variable of one over the
other.}

\begin{myhs}
\begin{code}
holesMap    :: (forall x dot phi x -> psi x) => Holes kappa fam phi at -> Holes kappa fam psi at

holesJoin   :: Holes kappa fam (Holes kappa fam) at -> Holes kappa fam at

chgDistr    :: Patch ki codes at -> Chg ki codes at
chgDistr p  = Chg  (holesJoin (holesMap chgDel p)) (holesJoin (holesMap chgIns p))
\end{code}
\end{myhs}

  The application semantics of |Patch| is independent of the scope
choices, and is easily defined in terms of |chgApply|. First we
computing a global change that corresponds to the patch in question,
then use |chgApply|. The |apply| function below works for locally and
globally scoped patches, as long as we care that the precondition for
|chgDistr| is maintained.

\begin{myhs}
\begin{code}
apply  :: (All Eq kappa) => Patch kappa fam at -> SFix kappa fam at -> Maybe (SFix kappa fam at)
apply p = chgApply (chgDistr p)
\end{code}
\end{myhs}

  Overall, we find ourselves in a dilemma. On the one hand we have
\emph{globally-scoped} patches, which have larger spines but can
produce results that are difficult to understand and synchronize, as
in \Cref{fig:pepatches:misalignment}. On the other hand,
\emph{locally-scoped} patches are more involved to compute, as we will
study next, \Cref{sec:pepatches:closures}, but they forbid
misalignments and also enable us to process small changes
independently of one another in the tree.  This is particularly
important for being able to develop an industrial synchronizer at some
point, as it keeps \emph{conflicts} small and isolated.

  We propose that the actual solution will consist in using a
combination of both scopings variants. First we will produce a
locally-scoped patch, which forbids situations as in
\Cref{fig:pepatches:misalignment}. This patch will consist in an
\emph{outer} spine leading to closed localy-scoped changes.  This
gives us an opportunity to identifying deletions and insertions that
could cause copies to be misaligned, essentially producing a
globally-scoped \emph{alignment} inside each of those
changes. Alignments will be discussed in more detail shortly
(\Cref{sec:pepatches:alignments}).

\subsection{Computing Closures}
\label{sec:pepatches:closures}

\begin{figure}
\centering
\subfloat[Not minimal; |Bin| is repeated and not necessary
to maintain scope.]{%
\enspace
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Bin| [|Leaf| [|84|]] [x,metavar]]
]
\end{myforest}
\enspace
\label{fig:pepatches:example-minimal:A}}%
\quad
\subfloat[Patch with minimal changes that results from |close| applied to \ref{fig:pepatches:example-minimal:A}]{%
\enspace
\begin{myforest}
[|Bin|, s sep=2mm
  [|Leaf| [,change [|42|] [|84|]]]
  [,change [x,metavar] [x,metavar]]
]
\end{myforest}
\enspace
\label{fig:pepatches:example-minimal:B}}%
\quad
\subfloat[Minimal; |Bin| is necessary to maintain scope.]{%
\enspace
\begin{myforest}
[,change, s sep=2mm
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]
]
\end{myforest}
\enspace
\label{fig:pepatches:example-minimal:C}}%

\subfloat[Minimal; root constructor modified.]{%
\quad
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Tri| [|Leaf| [|42|]] [x,metavar] [|Leaf| [|84|]]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:D}}%
\quad\quad
\subfloat[Not closed; |metavar x| appears in two separate changes.]{%
\quad
\begin{myforest}
[|Bin| , s sep=4mm
 [,change
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]]
 [,change [x,metavar] [x,metavar]]]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:E}}%

\caption{Some non-minimal-closed and minimal-closed changes examples.}
\label{fig:pepatches:example-minimal}
\end{figure}

  Computing locally-scoped patches consists of first computing the
largest possible spine, like we did with globally-scoped patches, then
enlarging the resulting changes until they are well-scoped and closed.
\Cref{fig:pepatches:example-03} illustrates this process. Computing
the closure of \Cref{fig:pepatches:example-03:A} starts with
\Cref{fig:pepatches:example-03:B}, then \emph{enlarging} the changes
to so that they contain the |Bin| constructor, which fixes their scope
(resulting in \Cref{fig:pepatches:example-03:C}).

  We say a change is closed when it has no free metavariables and,
additionally, its metavariables occur nowhere else.
The changes produced by the |chg| function are
closed, for example, but they might not be as small as they could be.
We say a change is \emph{minimal} when the root constructors
in its deletion and insertion context are either different
or necessary to maintain scope. \Cref{fig:pepatches:example-minimal}
illustrates different combinations of \emph{closed} and \emph{minimal}
changes. The intuition behind \emph{minimal-closed} changes is that
two such changes should not interfere with one another.

%% %{
%% %format dn = "\HSVar{d_n}"
%% %format in = "\HSVar{i_n}"
%% %format dj = "\HSVar{d_j}"
%% %format ij = "\HSVar{i_j}"
%% 
%%   Formally, we say a change |c| is in \emph{minimal-closed}
%% form if and only if it is closed with respect to some global scope
%% and, either: (A) |chgDel c| and |chgIns c| have different constructors
%% at their root or (B) they contain the same constructor to maintain
%% well-scopedness. More formally, when |chgDel c| and |chgIns c| contain
%% the same constructor, let |chgDel c == X d0 dots dn| and |chgIns c == X
%% i0 dots in|, we say |X| is necessary to maintain well-scopedness if
%% there exists an index |j| and variable |v| such that |v| occurs in
%% |ij| but is not defined in |dj|.  This means we cannot place |X| in
%% the spine whilst maintaining all changes
%% well-scoped.
%% %}

  Producing locally-scoped minimal-closed changes can be difficult under
arbitrary renamings. Take \Cref{fig:pepatches:example-minimal:E}, one
could argue that: if the occurrences of |metavar x| in each individual
change are, in fact, different, then the changes are
minimal-closed. To avoid these. In our case, however, we always start
from a large well-scoped change produced with |chg|. Consequently, we
know that every occurence of |metavar x| refers to \emph{the same}
tree in the source of the patch. This is another technicality of
dealing with names explicitly and provides good reason to enforce that
names are always different, even when occuring in separate scopes.

  In general, then, we can only know that a change is in fact closed
if we know how many times each variable is used globally.  Say a
variable |metavar z| is used |n + m| times in total within a change
|c|, and it has |n| and |m| occurrences in the deletion and insertion
contexts of |c|, respectively.  Then |metavar z| does not occur
anywhere else but within |c|, in other words, |metavar z| is
\emph{local} to |c|. If all variables of |c| are \emph{local} to |c|
with respect to some global scope, we say |c| is closed.
Given a multiset of variables for the global scope, we
can define |isClosedChg| in Haskell as:

\begin{myhs}
\begin{code}
isClosedChg :: Map Int Arity -> Chg kappa fam at -> Bool
isClosedChg global (Chg d i) = isClosed global (vars d) (vars i)
  where isClosed global ds us = unionWith (+) ds us `isSubmapOf` global
\end{code}
\end{myhs}

  The |close| function, shown in \Cref{fig:pepatches:close}, is
responsible for pushing constructors through the least general
generalization until they represent minimal-closed changes. It calls an
auxiliary version that receives the global scope and keeps track of
the variables it has seen so far.  The worst case scenario happens when
the we need \emph{all} constructors of the spine to close the change,
in which case, |close c = Hole c|; yet, if we pass a non-well-scoped
change change to |close|, it cannot produce a result and throws
an error instead.

  Efficiently computing closures requires us to keep track of the
variables that have been declared and used in a change -- that is,
we have seen occurrences in the deletion and insertion context
respectively.  Recomputing this multisets would result in a slower
algorithm.  The |annWithVars| function below computes the variables
that occur in two contexts and annotates a change with them:

\begin{myhs}
\begin{code}
data WithVars x at = WithVars  { decls , uses  :: Map Int Arity , body :: x at }

withVars :: (HolesMV kappa fam :*: HolesMV kappa fam) at -> WithVars (Chg kappa fam) at
withVars (d :*: i) = WithVars (vars d) (vars i) (Chg d i)
\end{code}
\end{myhs}


\begin{figure}
\begin{myhs}[0.99\textwidth]
\begin{code}
close :: Chg kappa fam at -> Holes kappa fam (Chg kappa fam) at
close c@(Chg d i) = case closeAux (chgVars c) (holesMap withVars (lgg d i)) of
                 InL _  -> error "invariant failure: c was not well-scoped."
                 InR b  -> holesMap body b

closeAux  :: M.Map Int Arity -> Holes kappa fam (WithVars (Chg kappa fam)) at
        -> Sum (WithVars (Chg kappa fam)) (Holes kappa fam (WithVars (Chg kappa fam))) at
closeAux _  (Prim x)  = InR (Prim x)
closeAux gl (Hole cv) = if isClosed gl cv then InR (Hole cv) else InL cv
closeAux gl (Roll x) =
  let aux = repMap (closeAux gl) x
   in case repMapM fromInR aux of
        Just res  -> InR (Roll res)
        Nothing   -> let  res = chgVarsDistr (Roll (repMap (either' Hole id) aux))
                      in  if isClosed gl res then InR (Hole res) else InL res
  where
    fromInR   :: Sum f g x -> Maybe (g x)
\end{code}
\end{myhs}
\caption{Complete generic definition of |close| and |closeAux|.}
\label{fig:pepatches:close}
\end{figure}

  The |chgVarsDistr| is the engine of the |close| function.
It distributes a spine over a change, similar to |chgDistr|,
but here we care to maintain the explicit variable annotations correctly.

\begin{myhs}
\begin{code}
chgVarsDistr :: Holes kappa fam (WithVars (Chg kappa fam)) at -> WithVars (Chg kappa fam) at
chgVarsDistr rs =  let  us  = map (exElim uses)   (getHoles rs)
                        ds  = map (exElim decls)  (getHoles rs)
                   in WithVars  (unionsWith (+) ds) (unionsWith (+) us)
                                (chgDistr (repMap body rs))
\end{code}
\end{myhs}

  The |closeAux| function, \Cref{fig:pepatches:close},
receives a spine with leaves of type |WithVars dots|
and attempts to \emph{enlarge} them as necessary.
If it is not possible to close the current spine, we
return a |InL dots| equivalent to pushing all the
constructors of the spine down the deletion and insertion contexts.


\subsection{The |diff| Function}

  Equipped with the ability to produce changes and minimize them,
we move on to defining the |diff| function. As usual, it receives a source and
destination trees, |s| and |d|, and computes a patch that encodes the
information necessary to transform the source into the
destination. The extraction of the contexts yields a |Chg|, which is
finally translated to a \emph{locally-scoped} |Patch| by identifying
the largest possible spine, with |close|.

\begin{myhs}
\begin{code}
diff  :: (All Digestible kappa) => SFix kappa fam at -> SFix kappa fam at -> Patch kappa fam at
diff x y =  let  dx             = preprocess x
                 dy             = preprocess y
                 (i, sh)        = buildSharingMap opts dx dy
                 (del :*: ins)  = extract extMode canShare (dx :*: dy)
            in cpyPrimsOnSpine i (close (Chg del ins))
 where canShare t = 1 < treeHeight (getConst (getAnn t))
\end{code}
\end{myhs}

  The |cpyPrimsOnSpine| function will issue copies for the opaque
values that appear on the spine, as illustrated in
\Cref{fig:pepatches:cpyonspine}. There, the |42| does not get shared
for its height is smaller than 1 but since it occurs in the same
location in the deletion and insertion context it can be identified as a copy
-- which involves issuing a fresh metavariable, hence the parameter |i|
in the code above.

\begin{figure}
\centering
\subfloat[Globally-scoped change]{%
\begin{myforest}
[,change
 [|BinLbl| [|42|] [|Bin| [x, metavar] [y, metavar]] [z,metavar]]
 [|BinLbl| [|42|] [|Bin| [y, metavar] [x, metavar]] [z,metavar]]
]
\end{myforest}}\qquad%
\subfloat[Locally-scoped change with copies in its spine]{%
\begin{myforest}
[|BinLbl|, s sep=4mm
  [,change [k,metavar] [k,metavar]]
  [,change [|Bin| [x, metavar] [y,metavar]]
           [|Bin| [y, metavar] [x,metavar]]]
  [,change [z, metavar] [z, metavar]]]
\end{myforest}}
\caption{A Globally-scoped change and the result of applying it to |cpyPrimsOnSpine . close|,
producing a patch with locally scoped changes and copies in its spine.}
\label{fig:pepatches:cpyonspine}
\end{figure}

\subsection{Aligning Changes}
\label{sec:pepatches:alignments}

\begin{figure}
\centering
\subfloat[Change that deletes |42| at the head of a list]{%
\begin{myforest}
[,change , s sep=1mm
  [|(:)| [|42|] [|(:)|,name=dca [x,metavar,name=dx]
                  [|(:)|,name=dcb [y,metavar,name=dy] [z,metavar,name=dz]]]]
  [|(:)|,name=ica [x,metavar,name=ix]
    [|(:)|,name=icb [y,metavar,name=iy] [z,metavar,name=iz]]]
]
\draw [<->,densely dotted,thick,black!20!white] (dca) -- (ica);
\draw [<->,densely dotted,thick,black!20!white] (dcb) -- (icb);
\draw [<->,densely dotted,thick,black!20!white] (dx)  -- (ix);
\draw [<->,densely dotted,thick,black!20!white] (dy)  -- (iy);
\draw [<->,densely dotted,thick,black!20!white] (dz)  -- (iz);
\end{myforest}
\label{fig:pepatches:alignment-01:A}}
\qquad\qquad
\subfloat[Alignment where the deletion of |(: 42)| is correctly identified.]{%
\begin{myforest}
[, delctx , alignmentSmall
  [|(:)| [|42|] [SQ]]
  [|(:)|,
      [|Cpy (metavar x)|]
      [|(:)| [|Cpy (metavar y)|] [|Cpy (metavar z)|]]
  ]
]
\end{myforest}
\label{fig:pepatches:alignment-01:B}}%
\caption{The change from \Cref{fig:pepatches:misalignment}, with
with an association of which nodes of the deletion and
insertion contexts represent the same information, and an
explicit representation of that information.}
\label{fig:pepatches:alignment-01}
\end{figure}

  As we have seen in the previous sections, locally-scoped changes can
avoid misaligning changes (\Cref{fig:pepatches:misalignment}), but
they still do not help us in identifying the insertions and
deletions. As it will turn out, identifying these insertions and
deletions is crucial for synchronization.  In this section we will
define a datatype and an algorithm for representing and computing
alignments, which make the backbone of synchronization. Untyped
synchronizers, such as \texttt{harmony}~\cite{Foster2007}, must employ
schemas to identify insertions and deletions avoiding misalignments
(\Cref{fig:pepatches:misalignment}). In our case, the type information
enable us to identify insertions and deletions naturally by ensuring that
they delete one layer of a \emph{recursive type} at a time, never altering
the type of the value under scrutiny.

  Take \Cref{fig:pepatches:alignment-01:A}, illustrating the change that
motivated locally-scoped patches (\Cref{fig:pepatches:misalignment})
in the first place. This time, however, arrows
connect constructors that represent \emph{the
same information} in each respective context.  This makes it clear
that |(: 42)| has no counterpart in the insertion context and,
consequently, corresponds to a deletion.  The |Chg| datatype
by itself is insufficient to represent all this information. Therefore
we need a new datatype for \emph{alignments}, |Al|, and a function
that translates a |Chg| into an |Al|.  Computing and representing an
alignment is, intuitively, the process of computing and representing
this association between subtrees of the deletion and insertion
contexts. The aligned version of \Cref{fig:pepatches:alignment-01:A}
is shown in \Cref{fig:pepatches:alignment-01:B}, where the |Al| border
marks scoping for metavariables. The constructors that are paired up
in the deletion and insertion are placed in a spine; those without a
correspondent are flagged as deletions or insertions depending on
which context they belong. Finally, |Cpy (metavar SQ)| is an
abbreviation for |Chg (metavar SQ) (metavar SQ)|.

  An aligned patch consists of a spine of copied constructors leading
to a \emph{well-scoped alignment}. This alignment, in turn, consists
of a sequence of insertions, deletions or spines, which finally lead
to a |Chg|. These |Chg| in the leaves of the alignment are
globally-scoped with respect to the alignment they belong.
We also add explicit information about copies and permutations to aid
the synchronization engine later. \Cref{fig:pepatches:alignment-02}
illustrates a value of type |Patch| and its corresponding alignment,
of type |PatchAl| defined below. Note how the the scope from each
change in \Cref{fig:pepatches:alignment-02:A} is preserved in
\Cref{fig:pepatches:alignment-02:B}, but the |Bin| on the left of the
root can now be safely identified as a copy without losing information
about the scope of |metavar x|.

\begin{myhs}
\begin{code}
type PatchAl kappa fam = Holes kappa fam (Al kappa fam (Chg kappa fam))
\end{code}
\end{myhs}

\begin{figure}
\centering
\subfloat[Locally-scoped patch |p|]{%
\begin{myforest}
[|Bin|, s sep=3mm
  [,change , s sep=1mm
    [|Bin| [x,metavar] [y,metavar]]
    [|Bin| [y,metavar] [x,metavar]]]
  [,change , s sep=1mm
    [z,metavar]
    [|Bin| [|Leaf| [|42|]] [z,metavar]]]]
\end{myforest}\label{fig:pepatches:alignment-02:A}}%
\quad
\subfloat[Result of |align p|, still locally scoped.]{%
\begin{myforest}
[|Bin|
 [|Bin| , alignmentSmall
   [|Prm (metavar x) (metavar y)|]
   [|Prm (metavar y) (metavar x)|]]
 [,insctx , alignmentSmall
   [|Bin| [|Leaf| [|42|]] [SQ]]
   [|Cpy (metavar z)|]]]
\end{myforest}\label{fig:pepatches:alignment-02:B}}
\caption{A patch |p| and its corresponding aligned version.
The |Al| barrier marks the beginning of an algnment and delimits
scopes; copies and permutations are marked explicitly and insertions
and deletions indicate their continuation with |SQ|.}
\label{fig:pepatches:alignment-02}
\end{figure}

Computing the \emph{alignment} for a change |c| consists in
identifying what information in the deletion context correspond
to \emph{the same information} in the insertion context.
The bits and pieces in the deletion context that
have no correspondent in the insertion context should be identified
as deletions and vice-versa for the insertion context.
In \Cref{fig:pepatches:alignment-01:A}, for example, the second |(:)|
in the deletion context represents the same information as the
root |(:)| in the insertion context.

  We can recognize the deletion of |(: 42)| in
\Cref{fig:pepatches:alignment-01:B} structurally.  All of its fields,
except one recursive field, contains no metavariables. The
one subtree which \emph{does contain} metavariables is denoted the
\emph{focus} of the deletion (resp. insertion). We denote
trees with no metavariables as \emph{rigid} trees.  A \emph{rigid}
tree has the guarantee that none of its subtrees is being copied,
moved or modified. Consequently, \emph{rigid} trees are being entirely
deleted from the source or inserted at the destination of the
change. If a constructor in the deletion (resp. insertion) context has
all but one of its subtrees being \emph{rigid}, it is only natural to
consider this constructor to be part of the \emph{deletion}
(resp. \emph{insertion}).

  Since our patches are locally scoped, computing an aligned patch is
simply done by mapping over the spine and aligning the individual
changes.  Aligning changes, in turn, is done by identifying whether
the constructor at the head of the deletion (resp. insertion) context
can be deleted (resp. inserted) then recursing on the focus of the
deletion (resp. insertion). When the root of the deletion context and
the root of the insertion context qualify for deletion and insertion,
we check whether we can add them to a spine instead.

\subsubsection{Generic Alignments}

  We will be representing a deletion or
insertion of a recursive \emph{layer} by identifying the \emph{position}
where this modification must take place. Moreover, said position
must be a recursive field of the constructor -- that is,
the deletion or insertion must not alter the type that our patch
operates over. This is easy to identify since we
followed typed approach, where we always have access to type-level
information.

  In the remainder of this section we discuss the datatypes necessary
to represent an aligned change, as illustrated in
\Cref{fig:pepatches:alignment-01:B}, and how to compute said
alignments from a |Chg kappa fam at|. The |alignChg| function,
declared below, will receive a well-scoped change and compute an
alignment.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
\end{code}
\end{myhs}

  The alignments here, encoded in the |Al| datatype, is similar to its
predecessor |Almu| from \texttt{stdiff}
(\Cref{sec:stdiff:diff:fixpoint}), it records insertions, deletions
and spines over a fixpoint. Insertions and deletions will be
represented with |Zipper|s~\cite{Huet1997}. A zipper over a datatype
|t| is the type of \emph{one-hole-contexts} over |t|, where the hole
indicates a focused position. We will use the zippers provided
directly by the \genericssimpl{} library
(\Cref{sec:gp:simplistic-zipper}).  These zippers encode a
\emph{single} layer of a fixpoint at a time, for example, a zipper
over the |Bin| constructor is either |Bin SQ u| or |Bin u SQ|,
indicating the focus is in either the left or the right subtree. It
\emph{does not} enable us specify a nested focus point, like in |Bin
(Bin SQ t) u|.

  A value of type |Zipper c g h at| is then equivalent to a constructor
of type |at| with one of its recursive positions replaced by a value
of type |h at| and the other positions |at'| (recursive or not) carrying
values of type |g at'|. The |c| above is a constraint that enables us
to inform GHC some properties of type |at| and is mostly a technicality.

  An alignment |Al kappa fam f at| represents a sequence of insertions
and deletions interleaved with spines, copies and permutations which
ultimately lead to \emph{unclassified modifications}, which are typed
according to the |f| parameter. Next, we will go through the six
constructors of |Al| one by one. First we have deletions and
insertions, which explicitly mention a zipper and one recursive field
to continue the alignment.

\begin{myhs}
\begin{code}
data Al kappa fam f at where
  Del  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f) at -> Al kappa fam f at
  Ins  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f) at -> Al kappa fam f at
\end{code}
\end{myhs}

  The |CompountCnstr| constraint above must be carried around to indicate we
are aligning a type that belongs to the mutually recursive family and
therefore has a generic representation -- again, just a Haskell technicality.

  Naturally, if no insertion or deletion can be performed but both
insertion and deletion contexts have the same constructor at their
root, we want to recognize this constructor as part of the spine of
the alignment, and continue to align its fields pairwise.

\begin{myhs}
\begin{code}
  Spn  :: (CompoundCnstr kappa fam x) => SRep (Al kappa fam f) (Rep at) -> Al kappa fam f at
\end{code}
\end{myhs}

  The |Spn| inside an alignment does not need to preserve metavariable scoping,
consequently, it can be pushed closer to the leaves uncovering as many
copies as possible.

  When no |Ins|, |Del| or |Spn| can be used,
we must be fallback to recording a unclassified modification,
of type |f at|. Most of the times |f| will be simply |Chg kappa fam|,
but we will be needing to add some extra information in the leaves
of an alignment later. Moreover, keeping the |f| a parameter
turns |Al| into a functor which enables us to map over it easily.

\begin{myhs}
\begin{code}
  Mod  :: f at -> Al kappa fam f at
\end{code}
\end{myhs}

  Imagine an alignment |a = Mod (Chg (metavar x) (metavar x))|. Does |a|
represent a copy or is |x| contracted or duplicated? Because metavariables
are scoped globally within an alignment, we can only distinguish between
copies and duplications by traversing the entire alignment and recording
the arity of |x|. Yet, it is an important distinction to make. A copy
synchronizes with anything whereas a contraction needs to satisfy
additional constraints. Therefore, we will identify copies and permutations
directly in the alignment to aid the merge function, later.

  Let |c = Chg (metavar x) (metavar y)| with both |x| and |y| occur twice
in their global scope: once in the deletion context and once in the
insertion context. We say |c| is a copy when |x == y| and a permutation
when |x /= y|. These are the last two constructors of |Al|.

\begin{myhs}
\begin{code}
  Cpy  :: Metavar kappa fam at                          -> Al kappa fam f at
  Prm  :: Metavar kappa fam at -> Metavar kappa fam at  -> Al kappa fam f at
\end{code}
\end{myhs}

  Equipped with a definition for alignments, we move on to defining
|alignChg|.  Given a change |c|, the first step of |alignChg c| is
checking whether the root of |chgDel c| (resp. |chgIns c|) can be
deleted (resp. inserted). A deletion (resp. insertion) of an occurrence
of a constructor |X| can be performed when all the of fields of |X| at
this occurrence are \emph{rigid} trees with the exception of a single
recursive field -- recall \emph{rigid} trees contains no
metavariables. If we can delete the root, we flag it as a deletion and
continue through the recursive \emph{non-rigid} field. If we cannot
perform a deletion at the root of |chgDel c| nor an insertion at the
root of |chgIns c| but they are constructed with the same constructor,
we identify the constructor as being part of the alignments' spine.
If |chgDel c| and |chgIns c| do not even
have the same constructor at the root, nor are copies or permutations,
we finally fallback and flag an unclassified modification.

  To check whether constructors can be deleted or inserted efficiently,
we must annotate rigidity information throughout our trees.
The |IsRigid| datatype captures whether a tree contains
any metavariables or not and is placed in every node
of a tree with the |annotRigidity| function.

\begin{myhs}
\begin{code}
type IsRigid = Const Bool
annotRigidity :: Holes kappa fam h x -> HolesAnn  kappa fam IsRigid  h x
\end{code}
\end{myhs}

% The relevant
% code is shown in \Cref{fig:pepatches:rigidity}.
%
% \begin{figure}
% \begin{myhs}
% \begin{code}
% type IsRigid = Const Bool
% 
% isRigid :: HolesAnn kappa fam IsRigid h x -> Bool
% isRigid = getConst . getAnn
% 
% annotRigidity  :: Holes     kappa fam          h x
%                -> HolesAnn  kappa fam IsRigid  h x
% annotRigidity = synthesize  aggr                    -- aggregate recursive values
%                             (\ _ _ -> Const True)   -- primitives are rigid
%                             (\ _ _ -> Const False)  -- holes are not!
%   where
%     aggr :: U1 b -> SRep IsRigid (Rep b) -> Const Bool b
%     aggr _ = Const . repLeaves getConst (&&) True
% \end{code}
% \end{myhs}
% \caption{Annotating a tree augmented with holes with information
% about whether or not it actually contains a hole.}
% \label{fig:pepatches:rigidity}
% \end{figure}

  After annotatins the trees with rigidity information, we
extract the zippers that witness potential insertions
or deletions. This is done by the |hasRigidZipper| function, which is
implemented by extracting \emph{all} possible zippers from the root
and checking whether there is one such that all of its fields are
rigid except for the focus of the zipper. If we find such a zipper, we
return it wrapped in a |Just|. When a rigid zipper exists it is
unique by definition, hence there is no choice involved in detecting
insertions and deletions, which keeps our algorithms efficient
and deterministic.

\Cref{fig:pepatches:hasrigidzipper} exemplifies two possible arguments
to |hasRigidZipper|. The tree in \Cref{fig:pepatches:hasrigidzipper:A}
has three possible zippers: focusin on either of its recursive positions.
Neither of them, however, would have all its subtrees rigid except the focus
point. \Cref{fig:pepatches:hasrigidzipper:B} on the other hand has one
of its zippers (the one with focus on |Bin (metavar k) (metavar l)|,
\Cref{fig:pepatches:hasrigidzipper:C})
rigid, that is, none of the trees within the zipper has any
metavariables.  We omit the full implementation of |hasRigidZipper|
but invite the interested reader should check |Data.HDiff.Diff.Align|
in the source code (\Cref{chap:where-is-the-code}).

% \begin{myhs}
% \begin{code}
% hasRigidZipper  :: HolesAnn kappa fam IsRigid (Metavar kappa fam) t
%                 -> Maybe (Zipper  (CompoundCnstr kappa fam t) (SFix kappa fam)
%                                   (HolesAnn kappa fam IsRigid (Metavar kappa fam)) t)
% \end{code}
% \end{myhs}

\begin{figure}
\centering
\subfloat[No rigid zipper exists]{%
\quad
\begin{myforest}
[|Tri| [|Leaf| [|42|]] [a,metavar] [b,metavar]]
\end{myforest}\label{fig:pepatches:hasrigidzipper:A}\quad}\qquad
\subfloat[Has a rigid zipper]{%
\begin{myforest}
  [|Tri| [|Leaf| [|42|]] [|Leaf| [|21|]] [|Bin| [k,metavar] [l,metavar]]]
\end{myforest}\label{fig:pepatches:hasrigidzipper:B}}\qquad
\subfloat[Rigid zipper of \ref{fig:pepatches:hasrigidzipper:B}]{%
\begin{myforest}
[,zipper
  [|Tri| [|Leaf| [|42|]] [|Leaf| [|21|]] [SQ]]
  [|Bin| [k,metavar] [l,metavar]]]
\end{myforest}\label{fig:pepatches:hasrigidzipper:C}}
\caption{Example calls to |hasRigidZipper| and their respective return values
where applicable.}
\label{fig:pepatches:hasrigidzipper}
\end{figure}

  Checking for deletions, then, can be easily done by first checking
whether the root can has a rigid zipper, if so, we can flag the
deletion. In the excerpt of |alD| below, if |d| was the tree in
\Cref{fig:pepatches:hasrigidzipper:B}, |focus| would be |Bin (metavar
k) (metavar l)|, which is the single \emph{non-rigid} recursive
subtree of |d|.

\begin{myhs}
\begin{code}
alD d i = case hasRigidZipper d of
    Just (Zipper zd focus) -> Del zd (continueAligning focus i)
\end{code}
\end{myhs}

  The complete |alD| is more involved. For one, we must check whether
|i| also has a rigid zipper and when both |d| and |i| have rigid zippers,
we must check whether they are the same constructor and, if so, mark
it as part of the spine instead. The |al| function encapsulates the |alD|
above and is shown in \Cref{fig:pepatches:align-fulldef}. A call to |al|
will attempt to extract deletions, then insertions, then finally falling
back to copies, permutations, modifications or recursively calling itself
inside spines.

  To compute an alignment, then, we start computing the multiset of
variables used throughout a patch, annotate the deletion and insertion
context with |IsRigid| and pass everything to the |al| function.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
alignChg c@(Chg d i) = al (chgVargs c) (annotRigidity d) (annotRigidity i)
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
type Aligner kappa fam  =    HolesAnn kappa fam IsStiff (Metavar kappa fam) t
                        ->   HolesAnn kappa fam IsStiff (Metavar kappa fam) t
                        ->   Al kappa fam (Chg kappa fam t)


al :: Map Int Arity -> Aligner kappa fam
al vars d i = alD (alS vars (al vars)) d i
 where
   -- Try deleting many; try inserting one; decide whether to delete,
   -- insert or spn in case both Del and Ins are possible. Fallback to
   -- inserting many.
   alD :: Aligner kappa fam -> Aligner kappa fam
   alD f d i = case hasRigidZipper d of -- Is the root a potential deletion?
       Nothing              -> alI f d i
       -- If so, we must check whether we also have a potential insertion.
       Just (Zipper zd rd)  -> case hasRigitZipper i of
           Nothing              -> Del (Zipper zd (alD f rd i))
           Just (Zipper zi ri)  -> case zipSZip zd zi of -- are zd and zi the same?
                Just res -> Spn $$ plug (zipperMap Mod res) (alD f rd ri)
                Nothing  -> Del (Zipper zd (Ins (Zipper zi (alD f rd ri))))

   -- Try inserting many; fallback to parametrized action.
   alI :: Aligner kappa fam -> Aligner kappa fam
   alI f d i = case hasRigidZipper i of
       Nothing              -> f d i
       Just (Zipper zi ri)  -> Ins (Zipper zi (alI f d ri))

   -- Try extracting spine and executing desired action
   -- on the leaves; fallback to deleting; inserting then modifying
   -- if no spine is possible.
   alS :: Map Int Arity -> Aligner kappa fam -> Aligned kappa fam
   alS vars f d@(Roll' _ sd) i@(Roll' _ si) =
     case zipSRep sd si of
       Nothing  -> alMod vars d i
       Just r   -> Spn (repMap (uncurry' f) r)
   syncSpine vars _ d i = alMod vars d i

   -- Records a modification, copy or permutation.
   alMod :: Map Int Arity -> Aligned kappa fam
   alMod vars (Hole' _ vd) (Hole' _ vi) =
     -- are both vd and vi with arity 2?
     | all (== Just 2 . flip lookup vars) [metavarGet vd , metavarGet vi]
        = if vd == vi then Cpy vd else Prm vd vi
     | otherwise
        = Mod (Chg (Hole vd) (Hole vi))
   alMod _ d i = Mod (Chg d i)
\end{code}
\end{myhs}
\caption{Complete definition of |al|.}
\label{fig:pepatches:align-fulldef}
\end{figure}

  Forgetting information computed |alignChg| is trivial but enables
us to convert back into a |Chg|. The |disalign| function, sketched
below, plugs deletion and insertion zippers casting a zipper over |SFix| into a
zipper over |Holes| where necessary; distributes the constructors in
the spine into both deletion and insertion contexts and translates
|Cpy| and |Prm| as expected.

\begin{myhs}
\begin{code}
disalign :: Al kappa fam (Chg kappa fam) at -> Chg kappa fam at
disalign (Del (Zipper del rest)) =
  let Chg d i = disalign rest
   in Chg (Roll (plug (cast del) d) i)
disalign dots
\end{code}
\end{myhs}

  Distributing an outer spine through an alignment is trivial.
All we must do is place all the constructors of the outer spine
as |Spn|:

\begin{myhs}
\begin{code}
alDistr :: PatchAl kappa fam at -> Al kappa fam (Chg kappa fam) at
alDistr (Hole al)  = al
alDistr (Prim k)   = Spn (Prim k)
alDistr (Roll r)   = Spn (Roll (repMap alDistr r))
\end{code}
\end{myhs}

  Finally, computing aligned patches from locally-scoped patches
is done by mapping over the outer spine and aligning the changes
individually, then we make a pass over the result and issue copies for
opaque values that appear on the alignment's inner spine.

\begin{myhs}
\begin{code}
align :: Patch kappa fam at -> PatchAl kappa fam at
align = fst . align'
\end{code}
\end{myhs}

  The auxiliary function |align'| returns the successor of the last
issued name to ensure we can easily produce fresh names later on, if
need be. Once again, a technicality of handling names explicitly.
Note that |align| introduces information, namely, new metavariables
that represent copies over opaque values that appear on the
alignment's spine. This means that mapping |disalign| to the result of
|align| will \emph{not} produce the same result. Alignments and
changes are \emph{not} isomorphic.

\begin{myhs}
\begin{code}
align' :: Patch kappa fam at -> (PatchAl kappa fam at , Int)
align' p = flip runState maxv $$ holesMapM (alRefineM cpyPrims . alignChg vars) p
 where  vars = patchVars p
        maxv = maybe 0 id (lookupMax vars)
\end{code}
\end{myhs}

  The |cpyPrims| above issues a |Cpy i|, for a fresh name |i| whenever
it sees a modification with the form |Chg (Prim x) (Prim y)| with |x == y|.
The |alRefineM f| applies a function in the leaves of the |Al| and
has type.

\begin{myhs}
\begin{code}
alRefineM  :: (Monad m) => (forall x dot f x -> m (Al kappa fam g x))
           -> Al kappa fam f ty -> m (Al kappa fam g ty)
\end{code}
\end{myhs}

  This process of computing alignments showcases
an important aspect of our well-typed approach: the ability
to access type-level information in order to compute
zippers and understand deletions and insertions of a single
layer in a homogeneous fashion -- the type that results from
the insertion or deletion is the same type that is expected
by the insertion or deletion.

\subsection{Summary}

  In \Cref{sec:pepatches:patches} we have seen how |Chg| represents
an unrestricted tree-matching, which can later be translated into
isolated, well-scoped, fragments connected through an outer spine
and making up a |Patch|. Finally, we have seen how to
extract valuable information from well-scoped about which constructors
have been deleted, inserted or still belong to an inner spine, giving
rise to alignments. This representation is a mix of local and
global alignments. The outer spine is important to isolate a
large change into smaller chunks, independent of one another.

  The |diff| function produces a |Patch| instead of a |PatchAl|
to keep it consistent with our previously published work~\cite{Miraldo2019},
but also because its easier to manage calls to |align| where they are
directly necessary, since |align| produces fresh variables and
this can require special attention to keep names from being shadowed.

  In fact, the |diff| function could be any path in the diagram
portrayed in \Cref{fig:pepatches:possible-diffs}. There is no \emph{right}
choice as this depends on the specific application in question. For our
particular case of pursuing a synchronization function, we require all
the information up to |PatchAl|.

\begin{figure}
\centering
%{
%format Delta = "\HTNI{\Delta}"
\begin{displaymath}
\xymatrix@@C+1pc{
  |Delta (SFix kappa fam) at| \ar[r]^(.47){|Delta decorate|} \ar[ddr]_{|diff|}
     & |Delta (PrepFix kappa fam) at| \ar[d]^{|extract extMode|} & \\
     & |Chg kappa fam at| \ar[d]^{|close|} & \\
   & |Patch kappa fam at| \ar[r]_(.45){|align|} & |PatchAl al kappa fam at|
}
\end{displaymath}
\caption{Conceptual pipeline of the design space for the |diff|
function. |Delta f x| denotes |(f x , f x)|}
%}
\label{fig:pepatches:possible-diffs}
\end{figure}

\section{Merging Aligned Patches}
\label{sec:pepatches:merging}

  In this section we will be exploring a synchronization
algorithm for aligned patches, witnessed by the |merge|
function, declared below, which receives two \emph{aligned} patches
|p| and |q| that make a span -- that is, have at least one common
element in their domain. The result of |merge p q| is a patch that
can might contain conflicts, denoted by |PatchC|, whenever
both |p| and |q| modify the same subtree in two distinct ways.
If |p| and |q| do \emph{not} make a span |merge p q| returns |Nothing|.
\Cref{fig:pepatches:mergesquare} illustrates a span of patches |p|
and |q| and their merge which is supposed to be applied to their
common ancestor producing a tree which combines the
modifications performed by |p| and |q|, when possible.

\begin{myhs}
\begin{code}
merge  :: PatchAl kappa fam at -> PatchAl kappa fam al -> Maybe (PatchC kappa fam at)
\end{code}
\end{myhs}


\begin{figure}
\footnotesize
\centering
\[
\xymatrix{ & O \ar[dl]_{|p|} \ar[dr]^{|q|} \ar[dd]^(0.7){|merge p q|} & \\
          A & & B \\
            & M &}
\]
\caption{Span of patches, |p| (transforms $O$ into $A$)
and |q| (transforms $O$ into $B$). Both patches have
a common element $O$ in their domain. The patch |merge p q| applies to
this common ancestor $O$ and can be thought of as the \emph{union} of the
changes of |p| and |q|.}
\label{fig:pepatches:mergesquare}
\end{figure}

  Recall our patches consist of a spine which leads to
locally-scoped alignments, which in turn
have an inner spine that ultimately leads to changes. The distinction
between the \emph{outer} spine and the spine inside the
alignments is the scope. Consequently, we can map a pure
function over the outer spine without having to carry information
about local scopes to the next call.
When manipulating the \emph{inner} spine, however, we must
keep track of which variables have or have not been declared
or used. Take the example in
\Cref{fig:pepatches:merge-00}, that merges patches |p|
(\Cref{fig:pepatches:merge-00:A}) and |q| (\Cref{fig:pepatches:merge-00:B})
to produce a new patch (\Cref{fig:pepatches:merge-00:C}).
While synchronizing the left child of each root, we discover that the tree
located at (or, identified by) |metavar x| was |Leaf 42|.
We must remember this information since we will encounter
|metavar x| again and must ensure that it matches with
its previously discovered value in order to perform the contraction.
When we finish synchronizing the left child of the root, though,
we can forget about |metavar x| since well-scopedness of
alignments guarantees |metavar x| will not appear elsewhere.

\begin{figure}
\centering
\subfloat[Patch |p|]{%
\begin{myforest}
[|Bin|
  [,change
    [|Bin| [x,metavar] [x,metavar]]
    [x,metavar]]
  [|Bin| , alignmentSmall
    [|Prm (metavar y) (metavar z)|]
    [|Prm (metavar z) (metavar y)|]]
]
\end{myforest}\label{fig:pepatches:merge-00:A}}\qquad%
\subfloat[Patch |q|]{%
\begin{myforest}
[|Bin| , s sep=7mm
  [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]]
  [,insctx , alignmentSmall
    [|Bin| [|Leaf| [|84|]] [SQ]]
    [|Cpy (metavar k)|]]]
\end{myforest}\label{fig:pepatches:merge-00:B}}

\subfloat[Result of |merge p q|]{%
\begin{myforest}
[|Bin| , s sep=10mm
  [,change
    [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]]
    [|Leaf| [|42|]]]
  [,insctx , alignmentSmall
    [|Bin| [|Leaf| [|84|]] [SQ]]
    [|Bin|
      [|Prm (metavar y) (metavar z)|]
      [|Prm (metavar z) (metavar y)|]]]
]
\end{myforest}\label{fig:pepatches:merge-00:C}}
\caption{Example of a simple synchronization}
\label{fig:pepatches:merge-00}
\end{figure}

  It helps to think about metavariables in a change as a unique
identifier for a subtree in the source. For example, if one change
modifies a subtree |x| into a different subtree |x'|, but some other
change moves |x|, identified by |metavar x|, to a different location
in the tree, the result of synchronizing these should be the transport
of |x'| into the new location -- which is exactly where |metavar x|
appears in the insertion context.  The example in
\Cref{fig:pepatches:merge-01} illustrates this very situation: the
source tree identified by |metavar x| in the deletion context of
\Cref{fig:pepatches:merge-01:B} was changed, by
\Cref{fig:pepatches:merge-01:A}, from |Leaf 42| into |Leaf 84|. Since
|p| altered the content of a subtree, but |q| altered its location,
they are \emph{disjoint} -- they alter different aspects of the common
ancestor. Hence, the synchronization is possible and results in
\Cref{fig:pepatches:merge-01:C}.

\begin{figure}
\centering
\subfloat[Patch |p|]{%
\begin{myforest}
[|Bin| , s sep=4mm
  [|Leaf| [,change [|42|] [|84|]]]
  [|Cpy (metavar k)| , alignment={1}{4mm}]]
\end{myforest}
\label{fig:pepatches:merge-01:A}}%
\qquad%
\subfloat[Change |q|]{%
\begin{myforest}
[|Bin| , alignmentSmall
  [|Prm (metavar x) (metavar y)|]
  [|Prm (metavar y) (metavar x)|]
]
\end{myforest}
\label{fig:pepatches:merge-01:B}}%
\qquad%
\subfloat[Synchronization of |p| and |q|]{%
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [y,metavar]]
  [|Bin| [y,metavar] [|Leaf| [|84|]]]
]
\end{myforest}
\label{fig:pepatches:merge-01:C}}
\caption{Example of a simple synchronization.}
\label{fig:pepatches:merge-01}
\end{figure}

  Given then two aligned patches, the |merge p q| function below
will map over the common prefix of the spines
of |p| and |q|, captured by their least-general-generalization and
produce a patch with might contain conflicts inside.
\digress{In the actual implementation we receive two patches
and align them inside |merge|, this helps ensuring they will
have a disjoint set of names.}

\begin{myhs}
\begin{code}
merge  :: PatchAl kappa fam at -> PatchAl kappa fam at -> Maybe (PatchC kappa fam at)
merge oa ob = holesMapM (uncurry' go) (lgg oa ab)
  where  go  :: Holes kappa fam (Al kappa fam) at -> Holes kappa fam (Al kappa fam) at
             -> Maybe (Sum (Conflict kappa fam) (Chg kappa fam) at)
         go ca cb = mergeAl (alDistr ca) (alDistr cb)
\end{code}
\end{myhs}

  A conflict, defined below, contains a label identifying which branch
of the merge algorithm issued it and the two alignments that could not
be synchronized. Conflicts are issued whenever we were not able to
reconcile the alignments in question. This happens either when we
cannot detect that two edits to the same location are non-interfering
or when two edits to the same location in fact interfere with one another.
Putting it differently, conflicts might contain false positives where
edits could have been automatically reconciled.
The |PatchC| datatype encodes patches which might contain conflicts
inside.

\begin{myhs}
\begin{code}
data Conflict kappa fam at  = Conflict String (Al kappa fam at) (Al kappa fam at)

type PatchC kappa fam at    = Holes kappa fam (Sum (Conflict kappa fam) (Chg kappa fam)) at
\end{code}
\end{myhs}

  Merging has a large design space. In what follows we will discuss
our initial exploration and prototype algorithm, which was driven
practical experiments (\Cref{chap:experiments}).
\digress{Unfortunately, I never had time to come back and refine the
merging algorithm from its prototype phase into a more polished
version. The merging algorithm was the last aspect of the project I worked on.}

  The |mergeAl| function is responsible for synchronizing alignments and
is where most of the work is happens. In broad strokes, it is similar to
synchronizing |PatchST|'s, \Cref{sec:stdiff:merging}: insertions
are preserved as long as they do not happen simultaneously.
Deletions must be \emph{applied} before continuing and
copies are the identity of synchronization. In the current setting,
however, we also have permutations and arbitrary changes to look at.
The general conducting line of our synchronization algorithm is to
first record how each subtree was modified and then instantiate these
modifications in a later phase. Tarversing the patches simultaneously
whilst constructing substitutions would not suffice since the order
which metavariables appear in each context can be drastically different.
This would require us to start over every time we discovered new
information on the current traversal, yielding a very slow merging algorithm.

  Let us look at an example, illustrated in
\Cref{fig:pepatches:merge-02}. We start identifying we are in a
situation where both |diff o a| and |diff o b| are spines, that is,
they copy the same constructor at their root. Recursing pairwise
through their children, we see a permutation versus a copy, since a
copy is the identity element, we return the permutation.  On the right
we see another spine versus an insertion, but since the insertion
represents new information, it must be preserved.  Finally, inside the
insertion we see another copy, which means that the spine should be
preserved as is.  The resulting patch can be seen in
\Cref{fig:pepatches:merge-02:res}.

\begin{figure}
\centering
\subfloat[|align (diff o a)|]{%
\begin{myforest}
[|(:)| , alignmentSmall
  [|Prm (metavar x) (metavar y)|]
    [|(:)| [|Prm (metavar y) (metavar x)|]
      [|[]|]
    ]
]
\end{myforest}}
\qquad%
\subfloat[|align (diff o b)|]{%
\begin{myforest}
[|(:)| , s sep=10mm
  [|Cpy (metavar a)|, alignment={0}{3mm}]
  [,insctx, alignmentSmall
    [|(:)| [|42|] [SQ]]
    [|Cpy (metavar b)|]]]
\end{myforest}}
\quad%
\subfloat[Result of merge |merge oa ob|]{%
\begin{myforest}
[,change
  [|(:)| [a,metavar] [|(:)| [b,metavar] [|[]|]]]
  [|(:)| [b,metavar] [|(:)| [|42|] [|(:)| [a,metavar] [|[]|]]]]
]
\end{myforest}
\label{fig:pepatches:merge-02:res}}
\caption{Example merge of two simple patches.}
\label{fig:pepatches:merge-02}
\end{figure}

  We keep track of the equivalences we discover
in a state monad. The instantiation of metavariables
will be stored under |inst| and the list of tree equivalences
will be stored under |eqs|.

\begin{myhs}
\begin{code}
data MergeState kappa fam = MergeState
  { inst  :: Map (Exists (Metavar kappa fam)) (Exists (Chg      kappa fam))
  , eqs   :: Map (Exists (Metavar kappa fam)) (Exists (HolesMV  kappa fam))
  }
\end{code}
\end{myhs}

  It is important to keep track of equivalences in |eqs|. Say, for
example, we are to merge two changes that were left as
\emph{unclassified} by our alignment algorithm. Naturally, their
deletion contexts must be unifiable, yielding a series of equivalences
between their metavariables but since we do not possess information
about exactly how each of those metavariables were transformed, we
cannot register how they changed in
|inst|. \Cref{fig:pepatches:eqs-not-inst} provides a simple such
example. When unifying the deletion contexts of
\Cref{fig:pepatches:eqs-not-inst:A} and
\Cref{fig:pepatches:eqs-not-inst:B}, we learn that |{metavar x == Leaf
42, metavar a == metavar x; metavar b == metavar y}|, which enable us
to conclude both changes are compatible and perform the same action
modulo a contraction and can be merged, yielding \Cref{fig:pepatches:eqs-not-inst:C}

\begin{figure}
\centering
\subfloat[Change |p|]{%
\begin{myforest}
[,change, s sep=0mm,
  [|Tri| [x,metavar] [|Leaf| [|42|]] [y,metavar]]
  [|Bin| [x,metavar] [y,metavar]]]
\end{myforest}\label{fig:pepatches:eqs-not-inst:A}}\quad
\subfloat[Change |q|]{%
\begin{myforest}
[,change, s sep=0mm
  [|Tri| [a,metavar] [a,metavar] [b,metavar]]
  [|Bin| [a,metavar] [b,metavar]]]
\end{myforest}\label{fig:pepatches:eqs-not-inst:B}}\quad
\subfloat[|merge p q|]{%
\begin{myforest}
[,change,s sep=0mm
  [|Tri| [|Leaf| [|42|]] [|Leaf| [|42|]]  [b,metavar]]
  [|Bin| [|Leaf| [|42|]] [b,metavar]]]
\end{myforest}\label{fig:pepatches:eqs-not-inst:C}}
\caption{Merging arbitrary changes requires knowledge of equivalences between
metavariables and trees.}
\label{fig:pepatches:eqs-not-inst}
\end{figure}


%% 
%%   The equivalences in |eqs| are different from instantiations in
%% |inst| and arise from a lack of expressivity from our alignments.
%% The entries |(metavar v , c)| in |inst|
%% represent a decision made by the merging algorithm: the subtree
%% located at |metavar v| must be modified according to a change |c| --
%% which means that the result of the merging process will contain no
%% occurrences of |metavar v| left.  The equivalences, on the other hand,
%% represent observations made by the merging algorithm, that is, an
%% entry |(metavar v , t)| represents an observation that the subtree at
%% |metavar v| is equal to |t|. This distinction is intricate and deserves
%% a more detailed example.
%% 
%%   Take \Cref{fig:pepatches:inst-not-eqs},
%% which shows two aligned patches |p| and |q|, operating over rose trees.
%% The result of |merge p q| is expectectly |q| itself, since it performs
%% exactly the modifications done by |p| but additionally inserts some
%% information (|Rose "nest"|). Since the focus of the insertion performed
%% by |q| does not appear as a recursive argument, it is not detected
%% as such by our alignments. Moreover, since |Rose "keep" []| was
%% also contracted, we cannot flag it as a simple copy. When merging
%% |Chg (metavar y) (metavar y)| with |
%% 
%% 
%% performs an additional insertion. The difficulty arises from the
%% the focus of the insertion of |q| appearing in a nested position. our
%% simple one-layer zippers cannot detect it. Consequently,
%% when the merging algorithm is looking at both changes to the
%% left of |(:)|, it has to deal with them as if they were arbitrary changes.
%% Hence, it unifies the deletion contexts, discovering that |metavar y|
%% identifies the same tree as |metavar b|. When lookint at the
%% insertion contexts, we see that on the one hand
%% this subtree was left untouched (by |p|) but on the other it became
%% |Rose "nest" [metavar b]|. If we are not careful and simply ask the
%% unification engine to produce an idempodent substitution to let us
%% produce the final merge, it would return an \emph{occurs-check} failure.
%% This issue stems from a combination of factors. For one, |metavar y| does not
%% get identified as a copy because it is contracted, and secondly, our alignments
%% to not recognize |Rose "nest" [metavar b]| as an insertion because it has
%% depth two. \digress{I believe there should be a more elegant way of
%% working around this issue, but unfortunately I had to leave it as future work.}
%% 
%% \begin{figure}
%% \centering
%% \subfloat[|p = align (diff o a)|]{%
%% \begin{myforest}
%% [|Rose|, s sep=6mm
%%   [|Cpy (metavar x)|, alignmentSmall]
%%   [|(:)|,alignmentSmall, s sep=4mm
%%     [,change [y,metavar] [y,metavar]]
%%     [,change, s sep=0mm
%%       [|(:)| [y,metavar]
%%        [|(:)| [|Rose "rm" []|] [|[]|] ]]
%%       [|[]|]]]]
%% \end{myforest}}\quad%
%% \subfloat[|q = align (diff o b)|]{%
%% \begin{myforest}
%% [|Rose|, s sep=12mm
%%   [|Cpy (metavar a)|, alignmentSmall]
%%   [|(:)|, alignmentSmall, s sep=4mm
%%     [,change,s sep=0mm, [b,metavar] [|Rose| [|"nest"|] [|(:)| [b,metavar] [|[]|]]]]
%%     [,change,s sep=0mm, [|(:)| [b,metavar] [|(:)| [|Rose "rm" []|] [|[]|]]] [|[]|]]
%%   ]]
%% \end{myforest}}
%% \vspace*{6.4em}
%% \begin{myhsFig}
%% \begin{code}
%% data Rose = Rose String [Rose]
%% 
%% a = Rose "x" [Rose "keep" []]
%% o = Rose "x" [Rose "keep" [] , Rose "keep" [] , Rose "rm" []]
%% b = Rose "x" [Rose "nest" [Rose "keep" []]]
%% \end{code}
%% \end{myhsFig}
%% 
%% \caption{Intricate example where we ignoring the difference
%% between |inst| and |eqs| in |MergeState| would yeild a conflict.}
%% \label{fig:pepatches:inst-not-eqs}
%% \end{figure}

  Conflicts and errors stemming from the arguments to |mergeAl|
\emph{not} forming a span will be distinguished by the |MergeErr| datatype,
below. We also define auxiliary functions to raise each specific
error in a computation inside the |Except| monad.

\begin{myhs}
\begin{code}
data MergeErr = NotASpan | Conf String

throwConf lbl  = throwError (Conf lbl)
throwNotASpan  = throwError NotASpan
\end{code}
\end{myhs}

  The |mergeAl| function is defined as a wrapper around |mergeAlM|,
which is defined in terms of the |MergeM| monad to help carry around
the necessary state and raises errors through the |Except| monad.

\begin{myhs}
\begin{code}
type MergeM kappa fam = StateT (MergeState kappa fam) (Except MergeErr)

mergeAl  :: Aligned kappa fam x -> Aligned kappa fam x
         -> Maybe (Sum (Conflict kappa fam) (Chg kappa fam) x)
mergeAl x y = case runExcept (evalStateT (mergeAlM p q) mrgStEmpty) of
                Left NotASpan    -> Nothing
                Left (Conf err)  -> Just (InL (Conflict err p q))
                Right r          -> Just (InR (disalign r))
\end{code}
\end{myhs}

  Finally, the |mergeAlM| function maps over both alignments that
we wish to merge and collects all the constraints and observations.
It then attempts to splits these constraints and observations into
two maps: (A) a deletion map that contains information
about what a subtree identified by a metavariable \emph{was}; and
(B) an insertion map that identifies what said metavariable \emph{became}.
If it is possible to produce these two idempotent substitutions,
it then makes a second pass computing the final result.

\begin{myhs}
\begin{code}
mergeAlM  :: Al kappa fam at -> Al kappa fam at -> MergeM kappa fam (Al kappa fam at)
mergeAlM p q = do  phase1  <- mergePhase1 p q
                   info    <- get
                   case splitDelInsMap info of
                     Left   _   -> throwConf "failed-contr"
                     Right  di  -> alignedMapM (mergePhase2 di) phase1
\end{code}
\end{myhs}

\paragraph{First Phase}
The first pass is computed by the |mergePhase1| function, which will
populate the state with instantiations and equivalences and place
values of type |Phase2| in-place in the alignment. These values instruct
the second phase on how to proceed on that particular location.
Before proceeding, though, we must process the information
we gathered into a deletion and an insertion map, with
|splitDelInsMap| function. First we look into how the first pass
instantiates metavariables and registers equivalences.

  The |mergePhase1| function receives two alignments and
produces a third alignment with instructions for the \emph{second phase}.
These instructions can be instantiating a change, with
|P2Instantiate|, which might include a context to ensure
for some consistency predicates. Or checking that two changes are
$\alpha$-equivalent after they have been instantiated.

\begin{myhs}
\begin{code}
data Phase2 kappa fam at where
  P2Instantiate   :: Chg kappa fam at -> Maybe (HolesMV kappa fam at) -> Phase2 kappa fam at
  P2TestEq        :: Chg kappa fam at -> Chg kappa fam at -> Phase2 kappa fam at
\end{code}
\end{myhs}

  Deciding which instruction should be performed depends on the
structure of the alignments under synchronization.
The |mergePhase1| function is shown in its entirety
in \Cref{fig:pepathes:mergePhaseOne} but we will discussed the
individual cases one by one, next.

\begin{myhs}
\begin{code}
mergePhase1  :: Al kappa fam x -> Al kappa fam x -> MergeM kappa fam (Al' kappa fam (Phase2 kappa fam) x)
mergePhase1 p q = case (p , q) of
   (Cpy _ , _)  -> return (Mod (P2Instantiate (disalign q)))
   (_ , Cpy _)  -> return (Mod (P2Instantiate (disalign p)))
\end{code}
\end{myhs}

  The first cases we have to handle are copies, shown above, which
should be the identity of synchronization. That is, if |p| is a copy,
all we need to do is modify the tree according to |q| at the current
location. We might need to refine |q| according to other constraints
we discovered in other parts of the alignment in question, so the
final instruction is to \emph{instantiate} the |Chg| that comes from
forgetting the alignment |q|. Recall |disalign| maps alignments
back into changes.

  Next we look at permutations, which are almost copies
in the sense that they do not modify the \emph{content}
of the tree, but they modify the \emph{location}.
We distinguish the case where both patches permute the same
tree versus the case where one patch permutes the tree but
the other changes its contents.

\begin{myhs}
\begin{code}
   (Prm x y, Prm w z)  -> Mod <$$> mrgPrmPrm x y w z
   (Prm x y, _)        -> Mod <$$> mrgPrm x y (disalign q)
   (_, Prm x y)        -> Mod <$$> mrgPrm x y (disalign p)
\end{code} %$
\end{myhs}

  If we are to merge two permutations, |Prm (metavar x) (metavar y)|
against |Prm (metavar w) (metavar z)|, for example, we know that
|metavar x| and |metavar w| must refer to the same subtree, hence we
register their equivalence. But since the two changes permuted the
same tree, we can only synchronize them if they were permuted to the
\emph{same place}, in other words, if both permutations turn out to be
equal at the end of the synchronization process. Consequently,
we issue a |P2TestEq|.

\begin{myhs}
\begin{code}
mrgPrmPrm  :: Metavar kappa fam x -> Metavar kappa fam x
           -> Metavar kappa fam x -> Metavar kappa fam x
           -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrmPrm x y w z  =   onEqvs (\eqs -> substInsert eqs x (Hole w))
                   >>  return (P2TestEq (Chg (Hole x) (Hole y)) (Chg (Hole w) (Hole z)))
\end{code}
\end{myhs}

  If we are merging one permutation with something other
than a permutation, however, we know one change modified the location
of a tree, whereas another potentially modified its contents.
All we must do is record that the tree identified
by |metavar x| was modified according to |c|. After we have made one
entire pass over the alignments being merged, we must instantiate
the permutation with the information we discovered -- the |metavar x|
occurrence in the deletion context of the permutation will be |chgDel c|,
potentially simplified or refined. The |metavar y| appearing in
the insertion context of the permutation will be instantiated
with whatever we come to discover about it later. We know there \emph{must}
be a single occurrence of |metavar y| in a deletion context because
the alignment flagged it as a permutation.

\begin{myhs}
\begin{code}
mrgPrm  :: Metavar kappa fam x -> Metavar kappa fam x -> Chg kappa fam x
        -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrm x y c  =   addToInst "prm-chg" x c
              >>  return (P2Instantiate (Chg (Hole x) (Hole y)) Nothing)
\end{code}
\end{myhs}

  The |addToInst| function inserts the |(x, c)| entry in |inst| if |x|
is not yet a member. It raises a conflict with the supplied label
if |x| is already in |inst| with a value that is different than |c|.
\digress{I believe that we could develop a better algorithm if instead
of forbidding values different than |c| we check to see whether the
two different values can also be merged. I ran into many difficulties
tracking how subtrees were moved and opted for the easy and pragmatic
option of not doing anything difficult here.}

  The call to |addToInst| in |mrgPrm| never raises a
|"prm-chg"| conflict. This is because |metavar x| and |metavar y| are
classified as a permutation -- each variable occurs exactly once
in the deletion and once in the insertion contexts.  Therefore, it is
impossible that |x| was already a member of |inst|.  \digress{In
fact, throughout our experiments, in \Cref{chap:experiments}, we
observed that |"prm-chg"| never showed up as a conflict in our whole
dataset, as expected.}

  With permutations and copies out of the way, we start looking at the
more intricate branches of the merge function. Insertions are still fairly
simple and must preserved as long as they do not attempt to
insert different information in the same location -- we would not
be able to decide which insertion come first in this situation.

\begin{myhs}
\begin{code}
   (Ins (Zipper z p'), Ins (Zipper z' q'))
     | z == z'             -> Ins . Zipper z <$$> mergePhase1 p' q'
     | otherwise           -> throwConf "ins-ins"
   (Ins (Zipper z p'), _)  -> Ins . Zipper z <$$> mrgPhase1 p' q
   (_ ,Ins (Zipper z q'))  -> Ins . Zipper z <$$> mrgPhase1 p q'
\end{code} %
\end{myhs}

  Deletions must be preserved and \emph{executed}. That is, if one patch
deletes a constructor but the other modifies the fields the
constructor, we must first ensure that none of the deleted fields
have been modified but the deletion should be preserved in the merge.
The |tryDel| function attempts to execute the deletion of a zipper
over an alignment, and, if successful, returns the pair of
alignments we should continue to merge. It essentially overlaps
the deletion zipper with |a| and observe whether |a| performs no
modifications anywhere except on the focus of the zipper.
When its not possible to execute the deletion
we can continue. \Cref{fig:pepatches:trydel-examples} illustrate some
example calls to |tryDel|, whose complete generic definition is shown
in \Cref{fig:pepatches:trydel}.

\begin{myhs}
\begin{code}
   (Del zp@(Zipper z _), _)  -> Del . Zipper z <$$> (tryDel zp q >>= uncurry mrgPhase1)
   (_, Del zq@(Zipper z _))  -> Del . Zipper z <$$> (tryDel zq p >>= uncurry mrgPhase1)
\end{code} %
\end{myhs}

  Note that since |merge| is symmetric, we an freely swap the order
of arguments. \digress{Let me rephrase that. The |merge| \emph{should}
be symmetric, and \texttt{QuickCheck} tests were positive of this, but
I have not come to the point of proving this yet.}

\begin{figure}
\subfloat[Call to |tryDel| succeeds; The |Bin| at the root can be deleted
as it only overlaps with copies. |tryDel| returns the focus of the deletion
and the part of the alignment |a| that overlaps with it.]{
\begin{myforest}
[,phantom,s sep=12mm, l=0mm,for children={no edge}
  [,phantom,l=0mm,for children={no edge}
    [,delctx,name=ZD [|Bin| [|Leaf| [|42|]] [SQ]] [|Cpy (metavar a)|]]
    [|Bin|,alignmentSmall,name=A
      [|Cpy (metavar x)|]
      [|Bin| [|Prm (metavar w) (metavar z)|]
             [|Prm (metavar z) (metavar w)|]]]]
  [,phantom
    [|tryDel zd a == (Cpy (metavar a) , Bin (Prm dots) (Prm dots))|, no edge,name=RES]]]
\node (DEST) at ($ (RES.parent first) + (2em,0) $) {};
\node (NZD)  at ($ (ZD.parent anchor) + (0,20pt) $) {|zd|};
\node (NA)   at ($ (A.parent anchor)  + (0,20pt) $) {|a|};
\draw[->,black!30!white] (NZD.east) to[out=20,in=90] (DEST);
\draw[->,black!30!white] (NA.east)   to[out=10,in=90] (DEST);
\end{myforest}}

\subfloat[Call to |tryDel| fails; Although the |Bin| at the root could
be deleted, the alignment |a| is changing the |42| present in the
leaf. This is a conflict.]{
\begin{myforest}
[,phantom,s sep=12mm, l=0mm,for children={no edge}
  [,phantom,l=4mm,for children={no edge}
    [,delctx,name=ZD [|Bin| [|Leaf| [|42|]] [SQ]] [|Cpy (metavar a)|]]
    [|Bin|,alignmentSmall,name=A
      [|Leaf| [,change [|42|] [|84|]]]
      [|Cpy (metavar x)|]]]
  [,phantom
    [|tryDel zd a == throwConf "del-spn"|, no edge,name=RES]]]
\node (DEST) at ($ (RES.parent first) + (2em,0) $) {};
\node (NZD)  at ($ (ZD.parent anchor) + (0,20pt) $) {|zd|};
\node (NA)   at ($ (A.parent anchor)  + (0,20pt) $) {|a|};
\draw[->,black!30!white] (NZD.east) to[out=20,in=90] (DEST);
\draw[->,black!30!white] (NA.east)   to[out=10,in=90] (DEST);
\end{myforest}}
\caption{Two example calls to |tryDel|.}
\label{fig:pepatches:trydel-examples}
\end{figure}

\begin{figure}
\begin{myhs}
\begin{code}
tryDel  :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Al kappa fam (Chg kappa fam)) x
        -> Al kappa fam (Chg kappa fam) x
        -> MergeM kappa fam (Al kappa fam (Chg kappa fam) x , Al kappa fam (Chg kappa fam) x)
tryDel (Zipper z h) (Del (Zipper z' h'))
  | z == z'    = return (h , h')
  | otherwise  = throwConf "del-del"
tryDel (Zipper z h) (Spn rep) = case zipperRepZip z rep of
    Nothing  -> throwNotASpan
    Just r   -> case partition (exElim isInR1) (repLeavesList r) of
                      ([Exists (InL Refl :*: x)] , xs)
                        | all isCpyL1 xs  -> return (h , x)
                        | otherwise       -> throwConf "del-spn"
                      _                   -> error "unreachable; zipRepZip invariant"
tryDel (Zipper _ _) _ = throwConf "del-mod"
\end{code}
\end{myhs}
\caption{Complete generic definition of the |tryDel| function.}
\label{fig:pepatches:trydel}
\end{figure}

  Next we have spines versus modifications. Intuitively, we want to match the
deletion context of the change against the spine and, when successful,
return the result of instantiating the insertion context of the
change.

\begin{myhs}
\begin{code}
   (Mod p', Spn q')  -> Mod <$$> mrgChgSpn p' q'
   (Spn p', Mod q')  -> Mod <$$> mrgChgSpn q' p'
\end{code}
\end{myhs}

  The |mrgChgSpn| function, below, matches the deletion context of the
|Chg| against the spine and and returns a |P2Instantiate| instruction.
The instantiation function |instM|, exemplified in
\Cref{fig:pepatches:instm-examples} and defined in
\Cref{fig:pepatches:instm}, receives a deletion context and an
alignment and attempts to assign the variables in the deletion context
to changes inside the alignment. This is only possible, though, when the
modifications in the spine occur \emph{further} from the root than the
variables in the deletion context. Otherwise, we have a conflict where
some constructors flagged for deletion are also marked
as modifications.

\begin{figure}
\subfloat[Call to |instM| succeeds and registers that the
subtree identified by |metavar x| has had its left child delted,
according to the alignment.]{%
\begin{myforest}
[,phantom,s sep=10mm, l=0mm,for children={no edge}
  [,phantom,l=0mm,for children={no edge},s sep=2mm
    [|Bin|,name=DD [|Leaf| [|42|]] [x,metavar]]
    [|Bin|,alignmentSmall,name=AL,s sep=12mm
      [|Cpy (metavar a)|]
      [,delctx [|Bin| [|Leaf| [|21|]] [SQ]] [|Cpy (metavar k)|]]]]
  [,phantom
    [|instM d al == addToInst (metavar x) (Chg (Bin (Leaf 42) (metavar k)) (metavar k)))|, no edge,name=RES]]]
\node (DEST) at ($ (RES.parent first) + (2em,0) $) {};
\node (NDD)  at ($ (DD.parent anchor) + (0,20pt) $) {|d|};
\node (NAL)  at ($ (AL.parent anchor) + (0,20pt) $) {|al|};
\draw[->,black!30!white] (NDD.east) to[out=20,in=90] (DEST);
\draw[->,black!30!white] (NAL.east) to[out=10,in=90] (DEST);
\end{myforest}}

\subfloat[Call to |instM| returns a conflict; The deletion context, |d|,
wants to match against the value |42| but the alignment modifies it.]{%
\begin{myforest}
[,phantom,s sep=10mm, l=0mm,for children={no edge}
  [,phantom,l=0mm,for children={no edge},s sep=10mm
    [|Bin|,name=DD [|Leaf| [|42|]] [x,metavar]]
    [|Bin|,alignmentSmall,name=AL
      [|Leaf| [,change [|42|] [|21|]]]
      [|Cpy (metavar l)|]]]
  [,phantom
    [|instM d al == throwConf "inst-mod"|, no edge,name=RES]]]
\node (DEST) at ($ (RES.parent first) + (2em,0) $) {};
\node (NDD)  at ($ (DD.parent anchor) + (0,20pt) $) {|d|};
\node (NAL)  at ($ (AL.parent anchor) + (0,20pt) $) {|al|};
\node (HACK) at ($ (DEST) + (6cm,0) $) {};
\draw[->,black!30!white] (NDD.east) to[out=20,in=90] (DEST);
\draw[->,black!30!white] (NAL.east) to[out=10,in=90] (DEST);
\end{myforest}}
\caption{Two example calls to |instM|.}
\label{fig:pepatches:instm-examples}
\end{figure}

\begin{figure}
\begin{myhs}
\begin{code}
instM :: (All Eq kappa) => HolesMV kappa fam at -> Al kappa fam at -> MergeM kappa fam ()

instM _           (Cpy _)    = return ()
instM (Hole v)    a          = addToInst "inst-contr" v (disalign a)
instM _           (Mod _)    = throwConf "inst-mod"
instM _           (Prm _ _)  = throwConf "inst-perm"
-- Del ctx and spine must form a span; cannot reference different constructors or primitives.
instM x@(Prim _)  d        = when (x /= chgDel (disalign d)) throwNotASpan
instM (Roll r)    (Spn s)  = case zipSRep r s of
    Nothing   -> throwNotASpan
    Just res  -> void (repMapM (\x -> uncurry' instM x >> return x) res)
instM (Roll _)    (Ins _)  = throwConf "inst-ins"
instM (Roll _)    (Del _)  = throwConf "inst-del"
\end{code}
\end{myhs}
\caption{Implementation of |instM|, which receives a deletion context and
an alignment and attempts to instantiate the variables in the deletion
context with changes in the alignment.}
\label{fig:pepatches:instm}
\end{figure}

\begin{figure}
\begin{minipage}{.65\textwidth}
\centering
\subfloat[Aligned Patch |p|]{%
\begin{myforest}
[|(,)| , s sep=4mm , alignment
  [|(:)| [|Cpy (metavar m)|] [,change [|(:)| [a,metavar] [b,metavar]] [b,metavar]]]
  [,change [c,metavar] [|(:)| [a,metavar] [c,metavar]]]]
\end{myforest}\label{fig:pepatches:merge-03:A}}\qquad
\subfloat[Aligned Patch |q|]{%
\begin{myforest}
[|(,)| , s sep=4mm , alignment
  [|(:)| [|Cpy (metavar n)|] [,change [|(:)| [x,metavar] [y,metavar]] [y,metavar]]]
  [|(:)| [|Cpy (metavar o)|] [,change [z,metavar] [|(:)| [x,metavar] [z,metavar]]]]]
\end{myforest}\label{fig:pepatches:merge-03:B}}
\end{minipage}%
\begin{minipage}{.3\textwidth}
\begin{displaymath}
\xymatrix{ |([1,dots] , [2 , 3 , dots])| \\
           |([1,2,dots] , [3 , dots])| \ar[u]^{|p|} \ar[d]_{|q|} \\
           |([1,dots] , [3 , 2 , dots])|
}
\end{displaymath}
\end{minipage}
\caption{Example of two conflicting patches that move
the same subtree into two different locations. The patches
here are operating over pairs of lists.}
\label{fig:pepatches:merge-03}
\end{figure}

\begin{myhs}
\begin{code}
   mrgChgSpn  :: (CompoundCnstr kappa fam x) => Chg kappa fam x -> SRep (Al kappa fam) (Rep x)
              -> MergeM kappa fam (Phase2 kappa fam x)
   mrgChgSpn p@(Chg dp _) spn = do
     instM dp (Spn spn)
     return (P2Instantiate p (Just (chgIns (disalign (Spn spn)))))
\end{code}
\end{myhs}

  The |Just| in the return value above indicate we must check that we
will not introduce extra duplications.  In
\Cref{fig:pepatches:merge-03} illustrates a case where failing to
perform this check would result in an erroneous duplication of the
value |2|. Matching the deletion context of |chg = Chg (metavar c)
(metavar a : metavar c)| against the spine |spn = Spn (Cpy (metavar o)
: Chg (metavar z) (metavar x : (metavar z)))| yields |metavar c| equal
to |spn|, which correctly identifies that the subtree at |metavar c|
was modified according to |spn|.  The observation, however, is that
the insertion context of |chg| mentions |metavar a|, which is a
subtree that comes from outside the deletion context of |chg|. If we
do not perform any further check and proceed naively, we would end up
substituting |metavar c| for |ctxDel (disalign spn)| and for |ctxIns
(disalign spn)| in |ctxDel chg| and |ctxIns chg|, respectively, which
would result in:

\begin{minipage}{.8\textwidth}
\centering
\begin{myforest}
[,change
  [|(:)| [o,metavar] [z,metavar]]
  [|(:)| [a,metavar]
    [|(:)| [o,metavar] [|(:)| [x,metavar] [z,metavar]]]]]
\end{myforest}
\end{minipage}

  Since we know |metavar x == metavar a|, which was registered when
merging the left hand side of |(,)|, in
\Cref{fig:pepatches:merge-03:A,fig:pepatches:merge-03:B}, it becomes
clear that |metavar a| was erroneously duplicated. Our implementation
will reject this by checking that the set of
subtrees that appear in the result of instantiating |chg| is disjoint
from the set of subtrees moved by |spn|. \digress{I
dislike this aspect of this synchronization algorithm quite a lot, it
feels unnecessarily complex and with no really good justification
besides the example in \Cref{fig:pepatches:merge-03}, which was
distilled from real conflicts. I believe that further work would
uncover a more disciplined way of disallowing duplications to be
introduced.}


  Merging two spines is simple. We know they must
reference the same constructor since the arguments
to |merge| form a span. All that we have to do
is recurse on the paired fields of the spines, point-wise:

\begin{myhs}
\begin{code}
   (Spn p', Spn q') -> case zipSRep p' q' of
       Nothing -> throwNotASpan
       Just r  -> Spn <$$> repMapM (uncurry' mrgPhase1) r
\end{code}
\end{myhs} %

  Lastly, when the alignments in question are arbitrary modifications,
we must try our best to reconcile these. We handle duplications differently
than arbitrary modifications, they are easier to handle.

\begin{myhs}
\begin{code}
   (Mod p', Mod q') -> Mod <$$> mrgChgChg p' q'
\end{code}
\end{myhs}

  Merging duplications is straightforward, if |p'| or |q'|
above are a duplication, that is, of the form |Chg (metavar x) (metavar y)|
we attempt to instantiate them with according to the
how this subtree was changed and move on.

\begin{myhs}
\begin{code}
mrgChgDup  :: Chg kappa fam x -> Chg kappa fam x -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgDup dup@(Chg (Hole v) _) q' = do
  addToInst "chg-dup" v q'
  return (P2Instantiate dup Nothing)
\end{code}
\end{myhs}

  Finally, if |p| and |q| are not duplications, nor any of the cases
previously discussed, then the best we can do is register equivalence
of their domains -- recall both patches being merged must form a span
-- and synchronize successfully when both changes are equal.

\begin{myhs}
\begin{code}
mrgChgChg :: Chg kappa fam x -> Chg kappa fam x -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgChg p' q'  | isDup p'   = mrgChgDup p' q'
                 | isDup q'   = mrgChgDup q' p'
                 | otherwise  = case unify (chgDel p') (chgDel q') of
                      Left  _   -> throwNotASpan
                      Right r   -> onEqvs (M.union r) >> return (P2TestEq p' q')
\end{code}
\end{myhs}

%   \Cref{fig:pepatches:mergePhaseOne} collects all the cases discussed
% above and illustrates the full definition of |mergePhase1|.
Once the first pass is done and we have collected information
about how each subtree has been changed and potential subtree
equivalences we might have discovered. The next step is to synthesize
this information into two maps: a deletion map that informs us
what a subtree \emph{was} and a insertion map that informs us
what a subtree \emph{became}, so we can perform the |P2Instante|
and |P2TestEq| instructions.

% \begin{figure}
% \begin{myhs}[.99\textwidth]
% \begin{code}
% mrgPhase1 p q = case (p , q) of
%    (Cpy _ , _)  -> return (Mod (P2Instantiate (disalign q)))
%    (_ , Cpy _)  -> return (Mod (P2Instantiate (disalign p)))
% 
%    (Prm x y, Prm x' y')  -> Mod <$$> mrgPrmPrm x y x' y'
%    (Prm x y, _)          -> Mod <$$> mrgPrm x y (disalign q)
%    (_, Prm x y)          -> Mod <$$> mrgPrm x y (disalign p)
% 
%    -- Insertions are preserved as long as they are not simultaneous.
%    (Ins (Zipper z p'), Ins (Zipper z' q'))
%      | z == z'   -> Ins . Zipper z <$$> mergePhase1 p' q'
%      | otherwise -> throwConf "ins-ins"
%    (Ins (Zipper z p'), _) -> Ins . Zipper z <$$> mrgPhase1 p' q
%    (_ ,Ins (Zipper z q')) -> Ins . Zipper z <$$> mrgPhase1 p q'
% 
%    -- Deletions need to be checked for compatibility: we try
%    -- and "apply" the deletion to the other alignment
%    (Del zp@(Zipper z _), _) -> Del . Zipper z <$$> (tryDel zp q >>= uncurry mrgPhase1)
%    (_, Del zq@(Zipper z _)) -> Del . Zipper z <$$> (tryDel zq p >>= uncurry mrgPhase1 . swap)
% 
%    -- Spines mean that on one hand a constructor was copied; but the mod
%    -- indicates this constructor changed.
%    (Mod p', Spn q') -> Mod <$$> mrgChgSpn p' q'
%    (Spn p', Mod q') -> Mod <$$> mrgChgSpn q' p'
% 
%    -- Two spines it is easy, just pointwise merge their recursive positions
%    (Spn p', Spn q') -> case zipSRep p' q' of
%        Nothing -> throwNotASpan
%        Just r  -> Spn <$$> repMapM (uncurry' mrgPhase1) r
% 
%    -- Finally, modifications sould be instantiated, if possible.
%    (Mod p', Mod q') -> Mod <$$> mrgChgChg p' q'
% \end{code}
% \end{myhs}
% \caption{Full implementation of |mergePhase1|.}
% \label{fig:pepatches:mergePhaseOne}
% \end{figure}

\paragraph{Second Phase}
The second phase starts with splitting |inst| and |eqvs|, which
requires some attention. For example,
imagine there exists an entry in |inst| that assigns |metavar x|
to |Chg (Hole (metavar y)) (: 42 (Hole (metavar y)))|, this tells us that
the tree identified by |metavar x| is the same as the tree identified
by |metavar y|, and it became |(: 42 (metavar y))|. Now suppose that
|metavar x| was duplicated somewhere else, and we come across
an equivalence that says |metavar y == metavar x|. We cannot simply insert
this equivalence into |inst| because the merge algorithm made the decision to
remove all occurrences of |metavar x|, not of |metavar y|, even
though they identify the same subtree. This is important to ensure
we produce patches that can be applied. \digress{This is yet
another aspect I am unsatisfied with and would like to see a more
disciplined approach. Will have to be future work, nevertheless.}

  The |splitDelInsMaps| function is responsible for synthesizing the
information gathered in the first pass of the synchronization
algorithm. First we split |inst| into the deletion and insertion
components of each of its points. Next, we partition the equivalences into rigid
equivalences, of the form |(metavar v , t)| where |t| has no holes, and
non-rigid equivalences. The rigid equivalences are added to both
deletion and insertion maps, but the non-rigid ones, |(metavar v ,
t)|, are are only added when there is no information about the
|metavar v| in the map and, if |t == metavar u|, we also check
that there is no information about |metavar u| in the map.
Lastly, after these have been added to the map, we call |minimize|
to produce an idempotent substitution we can use for phase two.
If an occurs-check error is raised, this is forwarded as a conflict.

\begin{myhs}
\begin{code}
splitDelInsMaps  :: MergeState kappa fam
                 -> Either [Exists (Metavar kappa fam)]
                           (  Subst kappa fam (Metavar kappa fam) ,  Subst kappa fam (Metavar kappa fam))
splitDelInsMaps (MergeState iot eqvs) = do
    let e' = splitEqvs eqvs
    d <-  addEqvsAndSimpl (map (exMap chgDel) inst) e'
    i <-  addEqvsAndSimpl (map (exMap chgIns) inst) e'
    return (d , i)
\end{code}
\end{myhs}

  After computing the insertion and deletion maps, which
inform us how each identified subtree was modified, we start
a second pass over the result of the first pass and execute
the necessary instructions.

\begin{myhs}
\begin{code}
phase2  :: (Subst kappa fam , Subst kappa fam) -> Phase2 kappa fam at
        -> MergeM kappa fam (Chg kappa fam at)
phase2 di (P2TestEq ca cb)              = isEqChg di ca cb
phase2 di (P2Instantiate chg Nothing)   = return (refineChg di chg)
phase2 di (P2Instantiate chg (Just i))  = do
   es <- gets eqs
   case getCommonVars (substApply es (chgIns chg)) (substApply es i) of
           []  -> return (refineChg di chg)
           xs  -> throwConf ("mov-mov " ++ show xs)
\end{code}
\end{myhs}

  The |getCommonVars| computes the intersection of the variables in
two |Holes|, which is used to forbid subtrees to be moved in
two different ways.

  Refining changes according to the inferred information is
straightforward, all we must do is apply the deletion map to the
deletion context and the insertion map to the insertion context.

\begin{myhs}
\begin{code}
refineChg :: Subst2 kappa fam -> Chg kappa fam at -> Chg kappa fam at
refineChg (d , i) (Chg del ins) = Chg (substApply d del) (substApply i ins)
\end{code}
\end{myhs}

  When deciding whether two changes are equal, its also important
to refine them first, since they might be $\alpha$-equivalent.

\begin{myhs}
\begin{code}
isEqChg  :: Subst2 kappa fam -> Chg kappa fam at -> Chg kappa fam at
         -> Maybe (Chg kappa fam at)
isEqChg di ca cb =  let  ca' = refineChg di ca
                         cb' = refineChg di cb
                    in if ca' == cb' then Just ca' else Nothing
\end{code}
\end{myhs}


%% \begin{figure}
%% \centering
%% \subfloat[Aligned patch, |p|.]{%
%% \begin{myforest}
%% [|Bin|   , s sep=15mm
%%    [Cpy]
%% %  [,change [x,metavar] [x,metavar]]
%%    [,delctx , s sep=8mm
%%     [|Bin| [|Leaf| [|42|]] [,sq]]
%%     [Cpy]
%% %    [,rootchange
%% %       [y,metavar]
%% %       [y,metavar]]
%% ]]
%% \end{myforest}
%% \label{fig:pepatches:merge-02:A}}
%% \subfloat[Aligned patch, |q|.]{%
%% \begin{myforest}
%% [|Bin|   % , s sep=4mm
%%   [|Bin| % , s sep=2mm
%%     [,change [a,metavar] [b,metavar]]
%%     [,change [b,metavar] [a,metavar]]]
%%   [,insctx % , s sep=8mm
%%     [|Bin| [,sq] [|Leaf| [|84|]]]
%%     [Cpy]
%%     % [,rootchange [c,metavar] [c,metavar]]
%%   ]
%% ]
%% \end{myforest}
%% \label{fig:pepatches:merge-02:B}}%
%% \caption{Properly aligned version of \Cref{fig:pepatches:misalignment}.}
%% \label{fig:pepatches:merge-02}
%% \end{figure}

  The merging algorithm presented in this section is involved. It
must deal with a number of corner cases and use advanced techniques
to do so generically. Most of the difficulties come from having to
deal with arbitrary duplications and contractions. If we instead chose
to use only linear patches, that is, patches where each metavariable must
be declared and used exactly once, the merge algorithm could be simplified.

\section{Discussion and Further Work}
\label{sec:pepatches:discussion}

  With \texttt{hdiff} we have seen that a complete detachment from
edit-scripts enables us to define a computationally efficient
differencing algorithm and how the notion of \emph{change} coupled
with a simple notion of composition gives a sensible algebraic
structure.  The patch datatype in \texttt{hdiff} is more expressive
than edit-script based approaches, it enables us to write
transformations involving arbitrary permutations and duplications. As
a consequence, we have a more involved merge algorithm. For one, we
cannot easily generalize our three-way merge to $n$-way merge. More
importantly, though, there are subtleties in the algorithm that arose
purely from practical necessities. Our posterior empirical evaluation
(\Cref{chap:experiments}) does indicate that the best success ratio
comes from merging linear patches -- where metavariables occur exactly
twice, obtained with the |Patience| extraction mode. This does suggest
that the soft-spot in the design space might well be allowing
arbitrary permutations, enabling a fast differencing algorithm,
but forbiding arbitrary duplications and contractions, which could
enable a simpler merging algorithm. Besides the merging
algorithm, we will discuss a number of other important aspects
that were left as future work and would need to
be addressed to bring \texttt{hdiff} from a prototype to
a production tool.

\subsubsection*{Refining Matching and Sharing Control}
  The matching engine underlying \texttt{hdiff} uses hashes
indiscriminately, all information under a subtree is used to compute
its hash, which can be undesirable. Imagine a parser that annotates
its resulting AST with source-location tokens. This means that we
would not be able to recognize permutations of statements, for
example, since both occurrences would have different source-location
tokens and, consequently, different hashes.

  This issue goes hand in hand with deciding which parts of the tree can
be shared and up until which point. For example, we probably never
want to share local statements outside their scope.  Recall we avoided
this issue by restricting whether a subtree could be shared
or not based on its height. This was a pragmatic design choice
that enabled us to make progress but it is a work-around at its best.

  Salting the hash function of |preprocess| is not an option for
working around the issue of sharing control.
If the information driving the salt function changes, none of the
subtrees under there can be shared again. To illustrate this,
suppose we push scope names into a stack with a
function |intrScope :: SFix kappa fam at -> Maybe String|, which would be
supplied by the user. It returns a |Just| whenever the datatype in question
introduces a scope. The |const Nothing| function works as a default
value, meaning that the mutually recursive family in question has no
scope-dependent naming. A more interesting |intrScope|, for
some imaginary mutually recursive family, is given below.

\begin{myhs}
\begin{code}
intrScope m@(Module dots)        = Just (moduleName m)
intrScope f@(FunctionDecl dots)  = Just (functionName f)
intrScope _                      = Nothing
\end{code}
\end{myhs}

  With |intrScope| as above, we could instruct the |preprocess| to
push module names and function names every time it traverses through
one such element of the family. For example, preprocessing the
pseudo-code below would mean that the hash for \verb!a! inside
\verb!fib! would be computed with |["m" , "fib"]| as a salt; but
\verb!a! inside \verb!fat!  would be computed with |["m" , "fat"]| as
a salt, yielding a different hash.

\begin{verbatim}
module m
  fib n = let a = 0; b = 1; ...
  fat n = let a = 0; ...
\end{verbatim}

  This will work out well for many cases, but as soon as a change
altered any information that was being used as a salt, nothing could
be shared anymore. For example, if we rename \verb!module m! to
\verb!module x!, the source and destination would contain no common
hashes, since we would have used |["m"]| to salt the hashes for the
source tree, but |["x"]| for the destination, yielding different
hashes.

  This problem is twofold, however. Besides identifying the
algorithmic means to ensure \texttt{hdiff} could be scope-aware and
respect said scopes, we must also engineer an interface to enable the
user to easily define said scopes. I envisioned a design with a custom
version of the \genericssimpl{} library, with an added alias for the
identity functor that could receive special treatment, for example:

\begin{myhs}
\begin{code}
newtype Scoped f = Scoped { unScoped :: f }

data Decl  = ImportDecl dots
           | FunDecl String [ParmDecl] (Scoped Body)
           dots
\end{code}
\end{myhs}

  This would mean that when inspecting and pattern matching on |SRep|
throughout our algorithms, we could treat \emph{scoped} types differently.

  We reiterate that if there is a solution to this problem, it certainly
will not use a modification of the matching mechanism: if we use
scope names, renamings will case problems; if we use the order which
scopes have been seen (De Bruijn-like), permutations will cause problems.
Controlling on the height of the trees and minimizing this issue was
the best option to move forward in an early stage. Unfortunately,
I did not have time to explore how scope graphs~\cite{Neron2015} could
help us here, but it is certainly a good place to start looking.
It might be possible to use scope graphs to write a more intricate
|close| function, that will properly break sharing where necessary,
for example.

\subsubsection*{Extraction Methods, \emph{Best} Patch and Edit-Scripts}

We have presented three extraction methods, which we called
|NoNested|, |ProperShare| and |Patience|.  Computing the diff between
two trees using different extraction methods can produce different
patches. Certainly there can be more extraction methods. One such
example that I never had the time to implement was a refinement of
|ProperShare|, aimed at breaking the sharing introduced by it. The
idea was to list the the metavariables that appear in the deletion and
insertion context and compute the LCS between these lists. The
location of copies enable us to break sharing and introduce new
metavariables.  For example, take the change below.

\begin{center}
\begin{myforest}
[,change
  [|Bin| [|Bin| [x, metavar] [x, metavar]]
       [|Bin| [z, metavar] [x, metavar]]]
  [|Bin| [x, metavar]
       [|Bin| [z, metavar] [x, metavar]]]
]
\end{myforest}
\end{center}

  The list of metavariables in the deletion context is |[metavar x ,
metavar x , metavar z , metavar x]|, but in the insertion context we
have |[metavar x , metavar z , metavar x]|. Computing the longest
common subsequence between
these lists yields |[Del x , Cpy , Cpy , Cpy]|. The first |Del|
suggests a contraction is really necessary, but the last copy shows
that we could \emph{break} the sharing by renaming |(metavar x)| to
|(metavar k)|, for example. This would essentially transform the
change above into:

\begin{center}
\begin{myforest}
[,change
  [|Bin| [|Bin| [x, metavar] [x, metavar]]
       [|Bin| [z, metavar] [k, metavar]]]
  [|Bin| [x, metavar]
       [|Bin| [z, metavar] [k, metavar]]]
]
\end{myforest}
\end{center}

  The point is that the copying of |metavar z| can act as a synchronization point
to introduce more variables, forget some sharing constraints, and ultimately
enlarge the domain of our patches.

  Forgetting about sharing is just one example of a different context
extraction mechanism and, without a formal notion about when a patch
is \emph{better} than another, its impossible to make a decision about
which context extraction should be used. Our experimental results
suggest that |Patience| yields patches that merge successfully more
often, but this is far from providing a metric on patches, like the
usual notion of cost does for edit-scripts.

\paragraph{Relation to Edit-Scripts.} Another interesting aspect that
I would have liked to look at is the relation between our |Patch| datatype
and traditional edit-scripts. The idea of breaking sharing above can be used
to translate our patches to an edit-script. Some early experiments did show
that we could use this method to compute approximations of the least-cost
edit-script in linear time. Given that the minimum cost edit-script takes
nearly quadratic time~\cite{backurs2015}, it might be worth looking into
how good an approximation we might be able to compute in linear time.
\victor{fact-check the above reference more carefully}

\subsubsection*{Formalizations and Generalizations}
Formalizing and proving properties about our |diff| and |merge| functions
was also one of my priorities. As it turns out, the extensional nature
of |Patch| makes for a difficult Agda formalization, which is the reason
this was left as further work.

  The value of a formalization goes beyond enabling us to prove
important properties. It also provides a laboratory for generalizing
aspects of the algorithms. Two of those immediately jump to mind:
generalizing the merge function to merge $n$ patches and
generalizing alignments insertions and deletions zippers to be
of arbitrary depth, instead of a single layer.
Finally, a formalization also provides important value in better
understanding the merge algorithm.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
