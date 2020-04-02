
\victor{I'm inclined in borrowing a \texttt{\\digress} env
like in Mandelbrot's ``Fractal Geom. of Nature''; where I write
in the first person about my experience doing things; could
be a good way to add bits like the following:
\digress{This hdiff approach as born from ...}}

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
patch. Consequently, we do not need any of the classical restrictions
imposed on tree matchings.

  Suppose we want to describe a change that modifies the left element
of a binary tree. If we had the full Haskell programming language available
as the patch language, we could write something in the lines of
\Cref{fig:pepatches:example-01:A}. Observing the function |c|
in \Cref{fig:pepatches:example-01:A}, we see it has a clear domain -- a
set of |Tree|s that when applied to |c| yields a |Just| -- which is
specified by the pattern and guards. Then, for each tree in the domain
we compute a corresponding tree in the codomain.  The new tree is obtained
from the old tree by replacing the |10| by |42| in-place.  Closely
inspecting this definition definition, we can interpret the matching of
the pattern as a \emph{deletion} phase and the construction of the
resulting tree as a \emph{insertion} phase.  The \texttt{hdiff}
approach represents the change in |c| exactly as that: a pattern and a
expression. Essentially, we write |c| as |chg (Bin (Leaf 10) y) (Bin
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
than before. Take, for example, the chhange that swaps two subtrees, which cannot
even be written using an edit-script based approach, here it is
given by |chg (Bin x y) (Bin y x)|. Another helpful consequence of
our design is that we effectively bypass the \emph{choice} phase of the
algorithm. When computing the differences between |Bin Leaf Leaf|
and |Leaf|, for example, we do not have to chose one |Leaf| to copy
because we can copy both with the help of a contraction operation,
with a change such as: |patch (Bin x x) x|. This aspect is crucial
and enables us to write a linear |diff| algorithm.

  In this chapter we explore the representation and computation
aspects of \texttt{hdiff}.  The big shift in paradigm of
\texttt{hdiff} also requires a more careful look into the metatheory
and nuances of the algorithm, which were not present in our original
paper~\cite{Miraldo2019}. The material in this chapter is a
developed from our ICFP'19 publication~\cite{Miraldo2019}, shifting
to the \genericssimpl{} library.

\victor{Maybe we write another paper with Pierre about it?}

\section{Changes}

\victor{is it necessary to add some text here?}

\subsection{A Concrete Example}
\label{sec:pepatches:concrete-changes}

  Before exploring the generic implementation of our algorithm, let us
look at a simple, concrete instance first, which sets the stage for
the the generic implementation that will follow.  Throughout this
section we will explore the central ideas from our algorithm
instantiated for a type of 2-3-trees:

\begin{myhs}
\begin{code}
data Tree  =  Leaf  Int
           |  Bin   Tree  Tree
           |  Tri   Tree  Tree  Tree
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
|Tree| with holes of type |phi|. Therefore, |TreeC MetaVar|
represents the type of |Tree| with holes carrying metavariables.
These metavariables correspond to arbitrary trees that are
\emph{common subtrees} of both the source and destination of the
change.  These are exactly the bits that are being copied from the
source to the destination tree.  We refer to a value of |TreeC| as a
\emph{context}.  For now, the metavariables will be simple |Int|
values but later on we will need to carry additional information.

\begin{myhs}
\begin{code}
type MetaVar = Int

data TreeC phi  = Hole   phi
                | LeafC  Int
                | BinC   TreeC TreeC
                | TriC   TreeC TreeC TreeC
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
\subfloat{%
\begin{myforest}
[,change [|Bin| [0,metavar] [1,metavar]]
         [|Bin| [1,metavar] [0,metavar]]]
\end{myforest}
}\qquad
\subfloat{%
\begin{myforest}
[,change [|Bin| [0,metavar]       [1,metavar]]
         [|Tri| [0,metavar] [|a|] [1,metavar]]]
\end{myforest}
}
\caption{Illustration of |diff (Bin t u) (Bin u t)| to the left and
|diff (Bin t u) (Tri t a u)| on the right. Metavariables are denoted
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

  Applying a change is done by unifying the the
metavariables in the deletion context, and later
instantiating the the insertion context with the obtained
substitution.

\begin{myhs}
\begin{code}
chgApply :: Change MetaVar -> Tree -> Maybe Tree
chgApply (d , i) x = del d x >>= ins i
\end{code}
\end{myhs}

  Naturally, if the term |x| and the deletion context |d| are
\emph{incompatible}, this operation will fail. Contrary to regular
pattern-matching we allow variables to appear more than once on both
the deletion and insertion contexts. Their semantics are dual:
duplicate variables in the deletion context must match equal trees,
and are referred to as contractions, whereas duplicate variables in the
insertion context will duplicate trees.  We use an auxiliary function
within the definition of |del| to make this check easier to
perform. Given a deletion context |ctx| and source |tree|, the |del|
function tries to associate all the metavariables in the context with
a subtree of the input |tree|.

\begin{myhs}
\begin{code}
del :: TreeC MetaVar -> Tree -> Maybe (Map MetaVar Tree)
del ctx tree = go ctx tree empty
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
go :: TreeC -> Tree -> Map MetaVar Tree -> Maybe (Map MetaVar Tree)
go (LeafC n)     (Leaf n')    m = guard (n == n') >> return m
go (BinC x y)    (Bin a b)    m = go x a m >>= go y b
go (TriC x y z)  (Tri a b c)  m = go x a m >>= go y b >>= go z c
go (Hole i)      t            m = case lookup i m of
                                        Nothing  -> return (M.insert i t m)
                                        Just t'  -> guard (t == t') >> return m
go _             _            m = Nothing
\end{code}
\end{myhs}

  We will refer to the result of |del ctx t| as the \emph{substitution}
that instantiates the metavariables of |ctx| with subtrees of |t|.
Once we have obtained such a substitution, we instantiate the variables
in the insertion context with their respective values, to obtain the
final tree.  This phase fails only when the change contains unbound
variables. The |ins| function is defined below.

\begin{myhs}
\begin{code}
ins :: TreeC MetaVar -> Map MetaVar Tree -> Maybe Tree
ins (LeafC n)     m  = return (Leaf n)
ins (BinC x y)    m  = Bin <$$> ins x m <*> ins y m
ins (TriC x y z)  m  = Tri <$$> ins x m <*> ins y m <*> ins z m
ins (Hole i)      m  = lookup i m
\end{code}
\end{myhs}

\subsubsection{Computing Changes}

  Next, we explore how to produce a change from a source and a
destination, defining a |chgTree| function. Intuitively, this function will
try to exploit as many copy opportunities as possible. For now, we delegate
the decision of whether a subtree should be copied or not to an
oracle: assume we have access a function |wcs :: Tree -> Tree ->
Tree -> Maybe MetaVar|, short for \emph{``which common subtree''}.  The
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
implementation for |Tree|. For now, assuming the oracle exists allows for
a clear separation of concerns.  The |changeTree| function merely
has to compute the deletion and insertion contexts, using said
oracle -- the inner workings of the oracle are abstracted away cleanly.

\begin{myhs}
\begin{code}
chgTree :: Tree -> Tree -> Change MetaVar
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
extract :: (Tree -> Maybe MetaVar) -> Tree -> TreeC MetaVar
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
the metavariable |metavar y|, required by the insertion context.

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
\caption{Context extraction must care to produce
well-formed changes. The nested occurrence of |t| within |Bin t u|
here yields a change with an undefined variable on its insertion
context.}
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
\texttt{--patience} option, which only copies uniquely occurring
lines. In fact, to make this easy to experiment, we will parameterize
our final |extract| with which of the.  \emph{context extraction
methods} described above should be used to produce correct changes.

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

  We will be looking into the correct |extract| function when
we get to its generic implementation. For the time being, we move on
to computing the |wcs| function efficiently for the concrete
case of the |Tree| datatype.


\begin{figure}
\victor{Find a better example... not sure this really illustrates
the differences}

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

%% 
%% 
%% \subsection{Minimizing Changes: Computing Patches}
%% %todo I think I understand why you want to minimize these changes -- but
%% %it's a quite subtle point. What problems do you run into if you *don't* minimize
%% %changes?
%% %
%% %vcm: No real problem for now. Yet, the merging algorithm
%% %     can only be written in 5 lines because of that.
%% %     Another aspect is that it allows us to reuse changes
%% %     in a much smoother way. For example, lets say we are
%% %     trying to apply a patch to a tree, but the spine
%% %     does not match. If the patch has only one change, we
%% %     can pull a UNIX `patch` and apply that change regardless.
%% 
%%   The process of minimizing and isolating the changes starts by
%% identifying the redundant part of the contexts. That is, the
%% constructors that show up as a prefix in \emph{both} the deletion and
%% the insertion context. They are essentially being copied over and we
%% want to make this fact explicit by separating them into what we call
%% the \emph{spine} of the patch. This step will help us reason about
%% patches later on.  If a constructor is in the \emph{spine}, we know it has been
%% copied, if it shows up in a change, we know it was either deleted or
%% inserted.  The spine will then contain changes---pairs of
%% an insertion and deletion context---in its leaves:
%% 
%% \begin{myhs}
%% \begin{code}
%% type Patch23 = TreeC (Change23 MetaVar)
%% \end{code}
%% \end{myhs}
%% 
%% \begin{figure}
%% %\includegraphics[scale=0.3]{src/img/patch-example.pdf}
%% oops
%% \vspace{.4em}
%% \begin{myhs}
%% \begin{code}
%% TriC  (Hole   (Hole 0 , Hole 0))
%%         (Hole   (BinC (Hole 0) (Hole 1) , BinC (Hole 1) (Hole 0))
%%         (BinC  (Hole  (tree23toC w, tree23toC w'))
%%                  (Hole  (Hole 3, Hole 3)))
%% \end{code}
%% \end{myhs}
%% \caption{Graphical and textual representation of the patch that %
%% transforms the value |Tri t (Bin u v) (Bin w x)| into the %
%% value |Tri t (Bin v u) (Bin w' x)|. The |tree23toC| function %
%% converts a |Tree| into a |TreeC| in the canonical way.}
%%  \label{fig:patch-example}
%% \end{figure}
%% 
%%   A \emph{patch} consists in a spine with \emph{changes} inside of it. 
%% \Cref{fig:patch-example} illustrates a value of type |Patch23|, where the
%% \emph{changes} are visualized with a shaded background in the
%% leaves of the spine. Note that the changes contains only the necessary
%% constructors to make sure that all metavariables that are used in the insertion
%% context are defined in the deletion context.
%% This keeps changes small and isolated, making them easier to merge. 
%% 
%%   In this section we will discuss how to take the results of
%% |changeTree| and transform them into a |Patch23|. The first step to
%% compute a patch from a change is identifying its \emph{spine}. That
%% is, the constructors that are present in both the deletion and
%% insertion contexts.  We are essentially splitting a monolithic change into
%% the \emph{greatest common prefix} of the insertion and deletion
%% contexts, leaving smaller changes on the leaves of this prefix:
%% 
%% \begin{myhs}
%% \begin{code}
%% gcp :: TreeC var -> TreeC var -> TreeC (Change23 var)
%% gcp LeafC              LeafC              = LeafC
%% gcp (BinC a1 b1)     (BinC a2 b2)     = BinC (gcp a1 a2) (gcp b1 b2)
%% gcp (TriC a1 b1 c1)  (TriC a1 b2 c2)  = TriC (gcp a1 a2) (gcp b1 b2) (gcp c1 c2)
%% gcp a                  b                  = Hole (a , b)
%% \end{code}
%% \end{myhs}
%% 
%%   In the last case of the |gcp| function either |a| and |b|
%% are both holes or the constructors disagree,
%% hence they do \emph{not} belong in the common prefix.
%% 
%%   One might be tempted to take the results of |changeTreeC|, pipe
%% them into the |gcp| function directly.  Yet, the
%% \emph{greatest common prefix} consumes all the possible constructors
%% leading to disagreeing parts of the contexts where this might be too greedy.
%% We must be careful not to break bindings as shown below:
%% 
%% %\begin{figure}
%% \begin{minipage}[t]{.55\textwidth}
%% \begin{myhs}
%% \begin{code}
%% -- prob = changeTree (Bin t t) (Bin x t)
%% prob  :: Change23 MetaVar
%% prob  =  Change  (  BinC (Hole 0)  (Hole 0)
%%                  ,  BinC x         (Hole 0))
%% \end{code}
%% \end{myhs}
%% \end{minipage} %
%% \begin{minipage}[t]{.35\textwidth}
%% \[ |gcp prob ==| \hspace{6em} \]
%% %\includegraphics[scale=0.3]{src/img/patch-02.pdf}
%% oops
%% \end{minipage}
%% % \caption{How |gcp| breaks binding. The triangle represents a |TreeC| with no holes.}
%% % \label{fig:patch-scoping-problem}
%% % \end{figure}
%% 
%%   In this example, the second change contains a |Hole 0| that does not
%% occur in the deletion context, and is hence \emph{unbound}. To address
%% this problem, we go over the result from our call to |gcp|, pulling
%% changes up the tree until each change is closed, that is, the set of
%% variables in both contexts is identical. We call this process the
%% \emph{closure} of a patch and declare a function to compute this
%% below.
%% 
%%   We have illustrated the process of |closure| in
%% \Cref{fig:closure}. Note that in both the input and output for the
%% |closure| function the subtree |x| appears on the deletion
%% context. Moreover, the |closure| functions only bubbles up the minimal
%% number of constructors to ensure all changes are closed.  In
%% particular, the |Bin| constructor at the root is still part of the
%% spine after the call to |closure|. 
%% 
%% \begin{figure}
%% %\includegraphics[scale=0.3]{src/img/patch-03.pdf}
%% oops
%% \caption{Graphical representation of the |closure| function.}
%% \label{fig:closure}
%% \end{figure}
%% 
%% \begin{myhs}
%% \begin{code}
%% closure :: TreeC (Change23 MetaVar) -> Patch23
%% \end{code}
%% \end{myhs}
%% 
%%   Although the |closure| function apparently always returns a patch,
%% its implementation might fail if there exists no way of closing all
%% the changes. In our case, this will never happen as we know that
%% |changeTree| outputs a closed change. In the worst case, the
%% resulting spine will be empty---but the change will certainly be
%% closed.  That is due to |postprocess|, which could have been merged
%% with |closure|. We kept them separate for clarity.
%% \Cref{sec:representing-changes} comes back to the |closure| function
%% in more detail on its generic incarnation. For now, it is more
%% important to understand that it facilitates merging our patches, later on (\Cref{sec:merging}).
%% It is worth mentioning that the result of |closure p| should be a patch that
%% can be applied to \emph{at least as many elements as |p|}. In some corner
%% cases |closure| might enlarge the domain of a patch by breaking some contractions.
%% This is not an issue, however, as being able to apply a patch to more
%% elements is a good thing.
%% 
%%   As soon as every change within the spine has been closed, we have a
%% \emph{patch}.  The final |diff| function for |Tree| is then defined
%% as follows:
%% 
%% \begin{myhs}
%% \begin{code}
%% diffTree :: Tree -> Tree -> Patch23
%% diffTree s d = closure $$ gcp $$ changeTree s d
%% \end{code}
%% \end{myhs}
%%  
%%   We could now define the |applyPatch23| function that applies a
%% \emph{patch}, rather than the |applyChange23| we saw previously.  This
%% is done by traversing the object tree and the spine of the patch until
%% a change is found and applying that change to the \emph{local}
%% subtrees in question.  
%% 
%% %% For one, we are not trying to
%% %% minimize the changes after we |extract| a context from the source or
%% %% destination trees. This makes merging significantly harder.  Another
%% %% problem is that we are not addressing what happens when there
%% %% exists a subtree that appears in at least two different places with
%% %% one occurrence being under a larger subtree. This can break the apply
%% %% function and needs to be identified and handled. Moreover, this example algorithm
%% %% shares subtrees too eagerly. For instance, every occurrence of |Leaf|
%% %% will be shared under the same metavariable. This restriction does not
%% %% impact the correctness of the algorithm but is an important point on
%% %% the design space: how to \emph{drive} this algorithm, \Cref{sec:sharing}.
%% 

\subsubsection{Defining the Oracle for |Tree|}
\label{sec:pepatches:concreteoracle}

  In order to have a working version of our differencing algorithm for
|Tree| we must provide the |wcs| implementation. Recall that the |wcs|
function, \emph{which common subtree}, has type |Tree -> Tree -> Tree
-> Maybe MetaVar|. Given a fixed |s| and |d|, |wcs s d x| returns
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
wcs :: Tree -> Tree -> Tree -> Maybe MetaVar
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
similar computations frequently, and performance is just as
important. These systems often rely on a technique known as
\emph{hash-consing}~\cite{Goto1974,Filliatre2006}, which is part
of the canon of programming folklore. Hash consing arises as a means of
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
instance Eq Tree where t == u = merkleRoot t == merkleRoot u
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
merkleRoot (LeafH n)    = hash (encode "1" ++ encode n)
merkleRoot (Bin x y)    = hash (concat ["2" , merkleRoot x , merkleRoot y])
merkleRoot (Tri x y z)  = hash (concat ["3" , merkleRoot x , merkleRoot y , merkleRoot z])
\end{code}
\end{myhs}

  Note that although it is theoretically possible to have false
positives, when using a cryptographic hash function the chance of
collision is negligible and hence, in practice, they never
happen~\cite{Menezes1997}. Nonetheless, it would be easy to detect when a
collision has occured in our algorithm; consequently, we chose to
ignore this issue.

  Recall we are striving for a constant time |(==)| implementation,
but the |(==)| definition above is still linear, we must recompute the
|merkleRoot| on every comparison. We fix this by caching the hash
associated with every node of a |Tree|.  This is done by the
|decorate| function, illustrated \Cref{fig:pepatches:decorate-conc}.

\begin{myhs}
\begin{code}
type TreeH   = (TreeH' , Digest)
data TreeH'  = LeafH
             | BinH TreeH  TreeH
             | TriH TreeH  TreeH  TreeH
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
\Cref{WHERE}. The |TreeH| datype carries round the
|merkleRoot| of its first component, hence, enabling us
to define |(==)| in constant time.

  The second source of inefficiency, enumerating all possible
subtrees, can be addressed by choosing a better data structure.  In
order to check whether a tree |x| is a subtree of a fixed |s| and |d|,
it suffices to check whether the merkle root of |x| appears in a
``database'' of the common merkle roots of |s| and |d|. Given that a
|Digest| is just a |[Word]|, the optimal choice for such ``database''
is a Trie~\cite{Brass2008} mapping a |[Word]| to a |MetaVar|. Trie
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
wcs :: TreeH -> TreeH -> TreeH -> Maybe MetaVar
wcs s d = lookup (mkTrie s intersect mkTrie d) . merkleRoot
  where  (intersect)  :: Trie k v  -> Trie k u  -> Trie k v
         lookup       :: Trie k v  -> [k]       -> Maybe v
         mkTrie       :: TreeH     -> Trie Word MetaVar
\end{code}
\end{myhs}

  The use of cryptographic hashes is unsurprising. They are almost
folklore for speeding up a variety of computations. It is important to
notice that the efficiency of our algorithm comes from our novel
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

  In \Cref{sec:pepatches:concrete-changes} we have seen how |TreeC|
played a crucial role in defining changes for the |Tree| datatype.
In this section, we generalize the construction of \emph{contexts}
to any datatype supported by the \genericssimpl{} library.


  Recall a \emph{context} over a datatype |T| is just a value of |T|
augmented with an additional constructor used to represent
\emph{holes}. This can be done with the \emph{free monad} construction
provided by the \genericssimpl{} library: |HolesAnn kappa fam ann
phi| datatype (\Cref{sec:gp:simplistic:holes}) is a free monad in |phi|.
We recall its definition ignoring annotations below.

\begin{myhs}
\begin{code}
data Holes kappa fam h a where
  Hole  :: h a -> Holes kappa fam h a
  Prim  :: (PrimCnstr kappa fam a)      => a -> Holes kappa fam h a
  Roll  :: (CompoundCnstr kappa fam a)  => SRep (Holes kappa fam h) (Rep a) -> Holes kappa fam h a
\end{code}
\end{myhs}

  The |TreeC MetaVar| datatype, defined in
\Cref{sec:pepatches:concrete-changes} to represent a value of type
|Tree| augmented with metavariables that were simple |Int|s, is in
fact, isomorhic to |Holes (P [ Int ]) (P [ Tree ]) (Const Int)|.
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
data MetaVar kappa fam at where
  MV_Prim  :: (PrimCnstr kappa fam at)      => Int -> MetaVar kappa fam at
  MV_Comp  :: (CompoundCnstr kappa fam at)  => Int -> MetaVar kappa fam at
\end{code}
\end{myhs}

  With |MetaVar| above, we can always fetch the |Int| identifying
the metavar but we maintain all the type-level information we need
to inspect at run-time. We define the |HolesMV| synonym
for values augmented with metavariables for convenience.

\begin{myhs}
\begin{code}
type HolesMV kappa fam = Holes kappa fam (MetaVar kappa fam)
\end{code}
\end{myhs}

  A \emph{change} is our \emph{unit of transformation} and
as we have already seen, consists in a pair of a deletion context and an
insertion context for the same type.  These contexts are
values of the mutually recursive family in question augmented with
metavariables:

\begin{myhs}
\begin{code}
data Chg kappa fam at = Chg  {  chgDel  :: HolesMV kappa fam at
                             ,  chgIns  :: HolesMV kappa fam at }
\end{code}
\end{myhs}

  Applying a change |c| to an element |x| consists in unifying |x|
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
c| we would like to guarantee that every metavariable in |chgIns c|
gets substituted, yielding a term with no holes as a result.
Consequently we expect a value of type |Chg| to be well-scoped, that
is, all the variables that are present in the insertion context must
also occur on the deletion context, in Haskell:

\begin{myhs}
\begin{code}
vars        :: HolesMV kappa fam at -> Map Int Arity

wellscoped  :: Chg kappa fam at -> Bool
wellscoped (Chg d i) = keys (vars i) == keys (vars d)
\end{code}
\victor{decide... is |vars del == vars ins| or |vars ins < vars del|}?
\end{myhs}

  Attempting to apply a non-well-scoped change is a violation of
the contract of |applyChg|. We throw an error on that case
and distinguish it from a change |c| not being able to be applied to |x|
because |x| is not an element of the domain of |c|.

  A change, |Chg|, is very similar to a \emph{tree matching}
(\Cref{sec:background:tree-edit-distance}) with less restrictions. In
other words, it arbitrarily maps subtrees from the source to the
destination. From an algebraic point of view, this already gives us a
desirable structure, as we will explore next, in
\Cref{sec:pepatches:meta-theory}.

\subsection{Meta Theory}
\label{sec:pepatches:meta-theory}

%% POTENTIAL NOTATION:
%{

%format (app (p) x) = "\mathopen{\HT{\llbracket}}" p "\mathclose{\HT{\rrbracket}}\>" x
%format after q p   = q "\mathbin{\HT{\bullet}}" p
%format iff         = "\HS{\iff}"
%format alpha       = "\HVNI{\alpha}"
%format beta        = "\HVNI{\beta}"
%format gamma       = "\HVNI{\gamma}"
%format sigma       = "\HVNI{\sigma}"
%format zeta        = "\HVNI{\zeta}"

\victor{maybe move the notation to the topleve;
I quite like semantic brackets for application}

  The |Chg| datatype represents a complete detachment from
edit-scripts. We can represent arbitrary structural transformations
through the ability to duplicate, permute and contract arbitrary
subtrees.  Effectively, we argue that an arbitrary function between
the nodes of a source tree and the desired destination tree make for
an effective representation of a patch. By avoiding translating this
mapping to an edit-script, we also avoid all the restrictions imposed
by classic \emph{tree mappings} (\Cref{def:background:tree-mapping}),
which are very restrictive -- order preserving partial bijections
which preserve the ancestry order.

  On this section we will look into how |Chg| admits a simple
composition operation and forms a partial monoid or
a partial grupoid depending on whether we allow metavariables to
be left unused or not. We shall be ignoring the \emph{change-versus-patch}
distinction and working solely with \emph{changes} in this section.
We can always recompute a patch from a change if we wish to do so and,
for meta-theoretical concerns, the distinction is artificial nevertheless
 -- it was put in place as a means to better drive
the synchronization algorithm.

  Through the remainder of this section we will assume changes have
all been $\alpha$-converted to never capture names.

  Composing two changes |c0 = Chg d0 i0| with |c1 = Chg d1 i1| is
possible if and only if the image of |chgApply c0| has elements in common
with the domain of |chgApply c1|. This can be easily witnessed
by trying to unify |i0| with |d1|. If they are unifiable, the changes
are composable. In fact, let |sigma = unify i0 d1|, the
change that witnesses the composition is given by
|c = Chg (substApply sigma d0) (substApply sigma i1)|.

\begin{myhs}
\begin{code}
after :: Chg kappa fam at -> Chg kappa fam at -> Maybe (Chg kappa fam at)
after p q =
  case unify (chgDel p) (chgIns q) of
    Left   _      -> Nothing
    Right  sigma  -> Just (Chg  (substApply sigma (chgDel q))
                                (substApply sigma (chgIns p)))
\end{code}
\end{myhs}

  We say that |after p q| is defined if there exists a change
|k| such that |after p q == Just k|, or, equivalently, if
|chgDel p| is unifiable with |chgIns q|.

  Note that it is inherent that purely structural composition of two changes
|p| after |q| yields a change, |pq|, that potentially misses sharing
opportunities. Imagine that |p| inserts a subtree |t| that was
deleted by |q|. Our composition algorithm posses no information
that this |t| is to be treated as a copy. This also occurs in
the edit-script universe: composing patches yields worse patches
than recomputing differences. We can imagine that a more complicated
composition algorithm could work around and recognize the copies
in those situations.

  Regardless of whether the composition produces \emph{the best}
patches possible or not, it is vital that it is correct. That
is, the composition of two patches is indistinguishable from
the composition of their application function. For the remainder
of this section we will abuse notation and write |sigma x|
instead of |substApply sigma x|. Finally, is
is crucial to recall we will abide by the Barendregt convention~\cite{Barendregt1984}
in our proofs and metatheory -- that is, all changes that appear
in in some mathematical context have their bound variable names
independent of each other, or, no two changes share
a variable name.

\victor{Is this style of proof ok? Can you follow it?}

\begin{lemma}[Composition Correct] \label{lemma:pepatches:comp-correct}
For any changes |p| and |q| and trees |x| and |y| aptly typed;
|app (after p q) x == Just y| if and only if
there exists |z| such that |app q x == Just z| and |app p z == Just y|.
\end{lemma}
\begin{proof}
\begin{description}
\item[if.]
Assuming |app (after p q) x == Just y|, we want to prove there exists
|z| such that |app q x == Just z| and |app p z == Just y|. Let |sigma|
be the result of |unify (chgDel p) (chgIns q)|, witnessing |after p q|;
let |gamma| be the result of |unify (sigma (chgDel q)) x|, witnessing the
application.
\begin{enumerate}
\item First, we observe that |chgDel q| unifies with |x|
through |gamma . sigma|. Moreover, |(gamma . sigma) q == x|.
Hence, |app q x == Just z|, for |z = (gamma . sigma) (ctxIns q)|.

\item Now, we must prove that there exists a substitution
|zeta| such that |zeta (ctxDel p) == zeta z|
Taking |zeta = gamma . sigma| and observing that |(gamma . sigma) (ctxIns q)|
has no variables enables us to conclude that we can
apply |p| to |z|.

\item Finally, we must prove that the result of
applying |p| to |z| coincides with |y|, that is, |zeta (ctxIns p) == y|.
Which is trivial given |zeta == gamma . sigma| and our hypothesis.
\end{enumerate}
\item[only if.]
Assuming there exists |z| such that |app q x == Just z| and
|app p x == Just y|, we want to prove that |app (after p q) x == Just y|.
Let |alpha| be such that |alpha (ctxDel q) == x|, hence, |z == alpha (ctxIns q)|;
Let |beta| be such that |beta (ctxDel p) == z|, hence |y == beta (ctxIns p)|.
\begin{enumerate}
\item First we prove that |after p q| is defined, that is,
there exists |sigma'| such that |sigma' (ctxIns q) == sigma' (ctxDel p)|.
Take |sigma' = alpha ++ beta|, and recall |alpha| and |beta|
have disjoint supports.

\begin{myhs}
\begin{code}
     sigma'  (ctxIns q)  ==  sigma'  (ctxDel p)
iff  alpha   (ctxIns q)  ==  beta    (ctxDel p)   -- disjoint supports
iff  z                   ==  beta    (ctxDel p)   -- def z
iff  beta z              ==  beta    (ctxDel p)   -- z has no variables
\end{code}
\end{myhs}

\item Since |sigma'| unifies |ctxIns q| and |ctxDel p|, let
|sigma| be their \emph{most general unifier}, that is,
|sigma = unify (ctxIns q) (ctxDel p)|. This yields
that |sigma' = gamma . sigma| for some |gamma| and
that |p after q == Chg (sigma (ctxDel q)) (sigma (ctxIns p))|.

\item Next we prove |sigma (ctxDel q)| can be
applied to |x|. Well, we know |x == beta (ctxDel q)|
and |beta (ctxDel q) == sigma' (ctxDel q)|, hence,
|x == (gamma . sigma) (ctxDel q)|.
Because |x| has no variables, |gamma x == x|.
Hence, |gamma| witnesses the unification of |sigma (ctxDel q)|
and |x|. Hence, |app (after p q) x == gamma (sigma (ctxIns p))|
Finally, a straightforward calculation yields that
|gamma (sigma (ctxIns p)) == y|.
\end{enumerate}
\end{description}
\end{proof}

  Once we have established that composition is correct
with respect to application, we would like to ensure
composition is associative. But first, it is handy to
consider an extensional equality over changes. Two
changes are said to be equal if and only if they are
indistinguishable through their application semantics:

\[
|p ~ q iff forall x dot (app p x) == (app q x)|
\]

\begin{lemma}[Definability of Composition]
Let |p|, |q| and |r| be aptly typed changes;
|after (after p q) r| is defined if and only if |after p (after q r)|
is defined.
\end{lemma}
\begin{proof}
If the proof above is fine; I'll transcribe what I have.
\end{proof}

\begin{lemma}[Associativity of Composition] \label{lemma:pepatches:comp-assoc}
Let |p|, |q| and |r| be aptly typed changes such
that |after (after p q) r| is defined, then
|after (after p q) r ~ after p (after q r)|.
\end{lemma}
\begin{proof}
If the proof above is fine; I'll transcribe what I have.
\end{proof}

\begin{lemma}[Identity of Composition] \label{lemma:pepatches:comp-id}
Let |p| be a change, then |cpy = Chg (metavar x) (metavar x)| is
the identity of composition. That is, |after p cpy == p == after cpy p|.
\end{lemma}
\begin{proof}
Trivial; |cpy| unifies with anything.
\end{proof}

  \Cref{lemma:pepatches:comp-assoc,lemma:pepatches:comp-id} establish
a partial monoid structure for |Chg| and |after| under extensional
change equality, |~|. This further strengthens the applicability
of |Chg| as a sound replacement for edit-script.

\victor{discuss inverses?}

\victor{
The |PatchPE ki codes| forms either:
\begin{itemize}
\item Partial monoid, if we want |vars ins <= vars del|
\item Grupoid, if we take |vars ins == vars del|
\end{itemize}
}


%}
%%% END OF TEMPORARY NOTATION


\subsection{Computing Changes}
\label{sec:pepatches:diff}

  In this section we explore how to efficiently compute a |Chg| given
a source and a destination trees, that is, defining the |diff| function.
Very much like \Cref{sec:pepatches:concrete-changes}, where we
sketched the |diff| function for the contrete type |Tree|,
this process depends on being able to
tell whether or not a given subtree is supposed to be \emph{shared}.
Consequently, for a given source |s| and destination |d| we
start by computing the \emph{sharing map} of |s| and |d|. This
sharing map is an auxiliary structure which enables us
to efficiently decide if a given tree |x| is a subtree of |s| and |d|.
Later, a second pass uses this sharing map and
\emph{extracts} the deletion and insertion contexts.

  The \emph{sharing map} is central to the efficiency of the
differencing algorithm, but it makes no decision about what to share.
We have seen, in ,\Cref{dif:pepatches:extract-problem}, that we must
employ some method do ensure that the extracted contexts produce
well-scoped changes. The three \emph{context extraction} methods we
have seen decide what can be shared or not and have been compared in
\Cref{fig:pepatches:extract-sol}. Recall their definition below.

\begin{myhs}
\begin{code}
data ExtractionMode  =  NoNested |  ProperShare |  Patience
\end{code}
\end{myhs}

  The problem of deciding what can be shared has another facet
to it, which is particularly relevant in the domain of differencing for
programming languages: we must be careful not to \emph{overshare}
trees.  Imagine a local variable declaration \verb!int x = 0;! in an
arbitrary function; it should \emph{not} be shared with a syntactically
equal declaration in another function.  A careful analysis of what can
and cannot be shared would require domain-specific knowledge of the
programming language in question.  Nevertheless, we can impose
different restrictions that make it \emph{unlikely} that values will
be shared across scope boundaries.  A simple and effective such
measure is not sharing subtrees with height strictly less than one
(or a configurable parameter). This keeps constants and most variable
declarations from being shared, effectively avoiding the issue.
\digress{I would like to reiterate the \emph{avoiding-the-issue}
aspect of this decision. I did attempt to overcome this with a few
methods which will be discussed later
(\Cref{sec:pepatches:discussion}). None of my attempts at solving the
issue were successful, hence, the best option really became
avoiding the issue by making sure that we can easily exclude certain
trees from being shared.}

\subsubsection{Which Common Subtree, Generically and Efficiently}

  The efficiency of whe ``which common subtree'' function
comes exclusively from annotating and indexing the source
and destination trees properly, similarly to
\emph{hash-consing}~\cite{Goto1974,Filliatre2006}.

\victor{glue?}

  Similarly to the concrete example from \Cref{sec:pepatches:concrete-patches},
the first thing we must do is annotate our trees with hashes at
every point. Gladly, the |Holes| datatype from \genericssimpl{}
also supports annotations. Unlike the concrete example, however,
we will also keep the height of each tree around. The |PrepFix|
below serves the same function as the concrete |TreeH|.

\begin{myhs}
\begin{code}
data PrepData a = PrepData  {  getDigest  :: Digest
                            ,  getHeight  :: Int
                            }

type PrepFix kappa fam
  = SFixAnn kappa fam PrepData
\end{code}
\end{myhs}

  The |decorate| function can be easily written with the help of
synthesized attributes. The homonym |synthesize| function from
\genericssimpl{} does exactly that. \Cref{fig:pepatches:decorate}
illustrates the same example from \Cref{fig:pepatches:decorate-conc},
but with hashes and heights.

\begin{myhs}
\begin{code}
decorate  :: (All Digestible kappa) => SFix kappa fam at -> PrepFix kappa fam at
decorate  = synthesize dots
\end{code}
\end{myhs}

\begin{figure}
%{
%format WD c ha he = "\begin{array}{c} \HS{hash}\HS{=}" ha " \\ \HS{height}\HS{=}" he " \\"  c " \end{array}"
\centering
\begin{myforest}
[,phantom , s sep'+=60pt
[|Bin| , name=A [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]] [|Leaf| [|84|]]]
[|WD Bin "0f42ab" 3|, tikz+={
        \draw [hdiff-black,->] (A.east) [out=25, in=165]to node[midway,above]{|decorate|} (!c.west);
      }
  [|WD Bin "310dac" 2| , name=ex1
    [|WD Leaf "0021ab" 1| [|WD 42 "004200" 0|]]
    [|WD Leaf "0021ab" 1| [|WD 42 "004200" 0|]]
  ]
  [|WD Leaf "4a32bd" 1|
    [|WD 84 "008400" 0|]
  ]
]
]
\end{myforest}
%}
\caption{Example of decorating a tree with hashes, through the
|decorate| function.}
\label{fig:pepatches:decorate}
\end{figure}

  The hashes are computed from the a unique identifier per constructor
and a concatenation of the hashes of the subtrees. The hash of the
root in \Cref{fig:pepatches:decorate}, for example, is computed with
a call to |hash (concat ["Main.Tree.Bin", "310dac", "4a32bd"])|.  This
ensures that hashes uniquely identify a subtree modulo hash
collisions.

  After preprocessing the input trees we want to traverse them and insert
every hash we see in a hash map, associated with a a counter for how
many times we have seen a tree. We use a simple |Int64|-indexed trie~\cite{Brass2008}
as our datastructure. \digress{I would like to also
implemented this algorithm with a big-endian Patricia Tree~\cite{Okasaki1998}
and compare the results. I think the difference would be
small, but worth considering when producing a production implementation}.

\begin{myhs}
\begin{code}
type Arity = Int

buildArityMap    :: PrepFix a kappa fam ix -> T.Trie Int
\end{code}
\end{myhs}

  A call to |buildArityMap| with the tree shown in
\Cref{fig:pepatches:preprocess}, for example, would
yield the following map.

\begin{myhs}
\begin{code}
T.fromList  [ ("0f42ab",  1),  ("310dac",  1),  ("0021ab",  2)
            , ("004200",  2),  ("4a32bd",  1),  ("008400",  1)
            ]
\end{code}
\end{myhs}

  After processing the \emph{arity} maps for both
the source tree and destination tree, we construct the \emph{sharing}
map. Which consists in the intersection of the arity maps and a final
pass adding a unique identifier to every key. We also keep
track of how many metavariables were assigned, so we can always
allocate fresh names without having to go inspect the whole map again.

\begin{myhs}
\begin{code}
type MetavarAndArity = MAA {getMetavar :: Int , getArity :: Arity}

buildSharingMap  :: PrepFix a kappa fam ix -> PrepFix a kappa fam ix
                 -> (Int , T.Trie MetaVarAndArity)
buildSharingMap x y
  =   T.mapAccum (\i ar -> (i+1 , MAA i ar) ) 0
  $$  T.zipWith (+) (buildArityMap x) (buildArityMap y)
\end{code}
\end{myhs}

  With all these pieces available to us, defining an efficient |wcs s d|
is straightforward: preprocess the trees, compute their sharing map and
use it for lookups. Yet, the whole point of preprocessing the trees
was to avoid the unnecessary recomputation of their hashes. Consequently,
we are better off carrying these preprocessed trees everywhere through
the computation of changes. The final |wcs| function will have its type
slightly adjusted and is defined below.

\begin{myhs}
\begin{code}
wcs  :: (All Digestible kappa) => PrepFix kappa fam at -> PrepFix kappa fam at
     -> (PrepFix kappa fam at -> Maybe Int)
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
and ignore the remote possibility of hash collisions.
Yet, it would not be hard to detect these collisions whilst
computing the arity map. To do so, we should store the tree with its associated
hash instead of just the hash, then, on every insertion we could check
that the inserted tree matches with the tree already in the map.
This process would cost us precious time and hence, we chose
to ignore hash collisions. \digress{Cryptographic hashes have
negligible collision probability but can be much more expensive to compute,
could be interesting to implement this algorithm with a non-cryptographic hash
and employ this collision checking to better understand what is the best option.
I believe this collision checking will be much slower for it brings the complexity
of the algorithm up}

\subsection{Context Extraction and the |diff| function}
\label{sec:pepatches:extract}

  Computing the set of common subtrees is straight forward and does
not involve many design decisions. Deciding which of those subtrees
are eligible to be shared, though, is an entirely different beast. As
we mentioned before, we surely do not want to share all \texttt{int}
constants throughout a file, for example.  Or, we would not like to
share all variables with the same name as they might be different
variables. As a matter of fact, a good definition of what can be
shared might even be impossible without domain-specific knowledge.

  We chose to never share subtrees with height smaller than a given
parameter. Our choice is very pragmatic in the sense that we can
preprocess all the trees and annotate them with their height,
which does not involve any domain specific knowledge and is efficient.
\digress{In the code, I abstracted this
away by the means of a predicate |CanShare| below. I hoped
to come back here and implement more refined sharing strategies.
I never had time for that, unfortunately.}

\begin{myhs}
\begin{code}
type CanShare kappa fam = forall ix dot PrepFix kappa fam ix -> Bool
\end{code}
\end{myhs}

  The interface function receives an |ExtractionMode|, a sharing map
and a |CanShare| predicate and two preprocessed fixpoints to extract
contexts from. The reason we receive two trees and produce two
contexts is because modes like |NoNested| perform some
cleanup that depends no global information.

\begin{myhs}
\begin{code}
extract  :: DiffMode -> CanShare kappa fam -> IsSharedMap
         -> (PrepFix kappa fam :*: PrepFix kappa fam) at
         -> (HolesMV kappa fam :*: HolesMV kappa fam) at
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
examples next, but I sketch other possibilities later (
\Cref{sec:pepatches:discussion}).}

\paragraph{Extracting with |NoNested|}
Extracting contexts with the |NoNested| mode is very simple.
We first extract the contexts naively, then make a second pass
removing the variables that appear exclusively in the insertion
context by the trees they abstracted over. The trick in doing so
efficiently is to \emph{not} forget which common subtrees
have been substituted on the first pass:

\begin{myhs}
\begin{code}
noNested1  :: CanShare kappa fam -> T.Trie MetavarAndArity -> PrepFix a kappa fam at
           -> Holes kappa fam (Const Int :*: PrepFix a kappa fam) at
noNested1 h sm x@(PrimAnn _    xi) = Prim xi
noNested1 h sm x@(SFixAnn ann  xi)
  =  if h x  then  maybe recurse (mkHole x) $$ lookup (identOf ann) sm
             else  recurse
 where
    recurse     = Roll (repMap (noNexted1 h sm) xi)
    mkHole x v  = Hole (Const (getMetavar v) :*: x)
\end{code}
\end{myhs}

  The second pass will go over holes and decide whether to
transform the |Const Int| into a |MetaVar kappa fam| or
whether to forget this was a potential shared tree and
keep the tree in there instead.

\paragraph{Extracting with |Patience|}
The |Patience| extraction method is very similar to |NoNested|,
with the difference that instead of simply looking a hash up
in the sharing map, it will further check that the given hash
occurs with arity two -- indicating the tree in question
occurs once in the source tree and once in the destination.
This completely bypasses the issue with |NoNested| producing
insertion contexts with undefined variables and requires
no further processing. The reason for it is that the variables
produced will appear with the same arity as the trees they abstract,
and in this case, it will be two: once in the deletion context
and once in the insertion context.

\paragraph{Extracting with |ProperShares|}
It is arguable that we might want to prioritize sharing
over spines, which is exactly what |ProperShares| does.
We say that a tree |x| is a \emph{proper-share} between |s| and
|d| whenever no subtree of |x| occurs in |s| and |d| with arity greater
than that of |x|. In other words, |x| is a proper-share if
and only if all of its subtrees only occur as subtrees of
other occurrences of |x|.

  Extracting contexts with under the |ProperShare| mode
consists in annotating the source and destination trees with
a boolean indicating whether or not they are a proper share,
then proceeding just like |Patience|, but instead of checking
that the arity must be two, we check that the tree is classified
as a \emph{proper-share}.

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

\paragraph{The |diff| function.}  Finally, the |diff| function
receives a source and destination trees, |s| and |d|, and computes a
patch that encodes the information necessary to transform the source
into the destination. The extraction of the contexts yields a |Chg|,
which is finally translated to a \emph{locally-scoped} |Patch| by
identifying the largest possible spine, with |close|.

\begin{myhs}
\begin{code}
diff  :: (All Digestible kappa) => SFix kappa fam at -> SFix kappa fam at -> Patch kappa fam at
diff x y =  let  dx             = preprocess x
                 dy             = preprocess y
                 (i, sh)        = buildSharingMap opts dx dy
                 (del :*: ins)  = extract canShare (dx :*: dy)
            in cpyPrimsOnSpine i (close (Chg del ins))
 where
   canShare t = 1 < treeHeight (getConst (getAnn t))
\end{code}
\end{myhs}

  The |cpyPrimsOnSpine| function will issue copies for the opaque
values that appear on the spine, as illustrated in
\Cref{fig:pepatches:cpyonspine}, where the |42| does not get shared
for its height is smaller than 1 but since it occurs in the same
location in the deletion and insertion context, we flag it as a copy
-- which involves issuing a fresh metavariable, hence the parameter |i|
in the code above.




\victor{\Huge I'm here}


\begin{figure}
\centering
\subfloat{%
\begin{myforest}
[,change
  [|Bin| [x,metavar] [|Leaf| [|5|]]]
  [|Bin| [x,metavar] [|Leaf| [|6|]]]
]
\end{myforest}
\label{fig:pepatches:example-04:A}}%
\quad\quad\quad
\subfloat{%
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [z,metavar]]
  [|Bin| [|Leaf| [|84|]] [|Bin| [z,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-04:B}}%
\caption{Example of disjoint changes.}
\label{fig:pepatches:example-04}
\end{figure}





From a synchronization point of view, however, we do not yet
posses enough information to synchronize these \emph{changes}
effectively.

  Synchronizing changes requires us to understand which
constructors in the deletion context are, in fact, just being copied
over in the insertion context. Take \Cref{fig:pepatches:example-04},
where one change operates exclusively on the right child of a binary
tree whereas the other alters the left child and duplicates the right
child in-place.  These changes are \emph{disjoint} and should be possible to
be automatically synchronized.  To recognize them as \emph{disjoint}
will require more information than what is provided by |Chg|.
Nevertheless, the notion of \emph{change} is still the backbone of
the implementation.  In fact, our |diff| algorithm (\Cref{sec:pepatches:diff})
will produce a \emph{change}, which will then be translated to more expressive
representations.

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

\paragraph{Introducing Patches.}
Observing the definition of |Chg| reveals that the
deletion context might \emph{delete} many constructors that the insertion
context later insert, as in \Cref{fig:pepatches:example-04}.
This conceals the fact that the
|Bin| at the root of the tree was in fact being copied. Following
the \texttt{stdiff} nomenclature, the |Bin| at the root of both
changes in \Cref{fig:pepatches:example-04} should be places
in the \emph{spine} of the patch.  That is, it is copied over
from source to destination but it leads to changes further down the
tree.

\victor{I'm unsure with this justification of pushing
changes down; I mean... we could just have written a ``better''
merge algorithm}


  A \emph{patch} consists in a spine that contains changes
in its leaves and is defined by the type |Patch| below.
\Cref{fig:pepatches:example-02} illustrates the difference
between patches and changes graphically.
In \Cref{fig:pepatches:example-02:chg} we see |Bin (Leaf 42)|
being repeated in both contexts -- whereas in
\Cref{fig:pepatches:example-02:patch} it has been placed in the spine
and consequently, is clearly identified as a copy.

\begin{myhs}
\begin{code}
type Patch kappa fam = Holes kappa fam (Chg kappa fam)
\end{code}
\end{myhs}

  Patches are computed from changes by
extracting topmost common constructors from the
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

  The first option, of \emph{globally-scoped} patches, is
very easy to compute. All we have to do is to compute the
anti-unification of the insertion and deletion context.

\begin{myhs}
\begin{code}
globallyScopedPatch :: Chg ki codes at -> PatchPE ki codes at
globallyScopedPatch (Chg d i) = holesMap (uncurry' Chg) (lgg d i)
\end{code}
\end{myhs}

  Albeit easy to compute, however, \emph{globally-scoped} patches
contribute little information from a synchronization point of view.
In fact, it can make merging even harder as shown in
\Cref{fig:pepatches:misaligned}, where a
globally scoped patch is produced from a change.
It is harder to understand that the |(:) 42| is being deleted
by looking at the globally-scoped patch than by looking at the change.
This is because the first |(:)| constructor is considered to be in the spine
by the naive anti-unification, which proceeds top-down.
Note that a bottom-up approach would
would suffer similar issues for insertions anyway.
\victor{This is a problem Harmony also had!}
The real solution to this problem is the notion of \emph{alignment}
which will be discussed shortly (\Cref{sec:pepatches:alignment}), for
the time being we will maintain our focus on scoping.

  \emph{Locally-scoped} changes implies that
changes might still contain repeated constructors in the root
of their deletion and insertion contexts -- hence they will not be
structurally minimal. On the other hand, copies are easy to
identify and reconciliation will happen \emph{in place}. This later
reason being particularly important for a industrial synchronizer since
it enables the \emph{conflicts} to be put in place and refer
to small parts of the patch instead of the whole.

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
\caption{Misaligned metavariables due to deletions
in the head of linearly-structured data. This is hard to reconcile.}
\label{fig:pepatches:misalignment}
\end{figure}

  Independently of global or local scoping,
ignoring the information about the spine yields a forgetful
functor from patches back into changes. It is simple to define thanks
to the free monad structure of |Holes|, which gives us the
necessary monadic multiplication.

\begin{myhs}
\begin{code}
holesMap    :: (forall x dot phi x -> psi x)
            => Holes kappa fam phi at -> Holes kappa fam psi at

holesJoin   :: Holes kappa fam (Holes kappa fam) at -> Holes kappa fam at

chgDistr    :: PatchPE ki codes at -> Chg ki codes at
chgDistr p  = Chg  (holesJoin (holesMap chgDel  p))
                   (holesJoin (holesMap chgIns  p))
\end{code}
\end{myhs}

  It is worth noting that we must care that |chgDistr| wont
capture variables. It will only work properly if all metavariables
have already been properly $\alpha$-converted to avoid capturing. We
cannot enforce this invariant directly in the |chgDistr| function for
performance reasons.  Throughout the implementation, however, we
continuously ensure that even though we produce and work with
\emph{locally scoped} patches, all scopes contains disjoint sets of
names and therefore can be safely distributed.  In the context of
meta-theoretical definitions and proofs we will abide by Barendregts
Convention~\cite{Barendregt1984} where no two bound variables are
identified with the same name.  \digress{I wonder how an
implementation using De Bruijn indexes would look like. I'm not
immediately sure it would be easier to enforce correct indexes. Through
the bowels of the code we ensure two changes have disjoint sets of
names by adding the successor of the maximum variable of one over the
other.}

  The application semantics of |Patch| is easily defined in terms
of |chgApply|. As usual, assume all metavariable scopes are disjoint, the
application of a patch is defined as:

\begin{myhs}
\begin{code}
apply  :: (All Eq kappa) => Patch kappa fam at -> SFix kappa fam at -> SFix kappa fam at
apply  = chgApply . chgDistr
\end{code}
\end{myhs}

  From our empirical experience, discussed in \Cref{sec:pepatches:experiments},
it does seem like \emph{locally-scoped} patches outperform \emph{globally-scoped}
enabling us to solve more conflicts successfully. Besides this empirical
validation, opting for \emph{locally-scoped} patches also enable us to place
conflicts in-place, which is better than issuing a single conflict for
the whole patch. For these reasons, we will move on with \emph{locally-scoped}
patches. Next, \Cref{sec:pepatches:closures} introduces an algorithm for translating
a single |Chg| into a patch with locally-scoped changes and \Cref{sec:pepatches:alignment}
looks into further refining the changes into \emph{alignments}, providing
even more information to the synchronization engine.

\subsection{Computing Closures}
\label{sec:pepatches:closures}

\begin{figure}
\centering
\subfloat[Not minimal; |Bin| is repeated and not necessary
to maintain scope.]{%
\quad
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Bin| [|Leaf| [|84|]] [x,metavar]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:A}}%
\quad\quad
\subfloat[Minimal; root constructor modified.]{%
\quad
\begin{myforest}
[,change
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Tri| [|Leaf| [|42|]] [x,metavar] [|Leaf| [|84|]]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:B}}%

\subfloat[Minimal; |Bin| is necessary to maintain scope.]{%
\quad
\begin{myforest}
[,change
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:C}}%
\quad\quad
\subfloat[Patch with minimal changes computed with |close| applied to \ref{fig:pepatches:example-minimal:A}]{%
\quad
\begin{myforest}
[|Bin|, s sep=5mm
  [|Leaf| [,change [|42|] [|84|]]]
  [,change [x,metavar] [x,metavar]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:D}}%
\caption{Some non-minimal and one minimal change.}
\label{fig:pepatches:example-minimal}
\end{figure}

%{
%format dn = "\HSVar{d_n}"
%format in = "\HSVar{i_n}"
%format dj = "\HSVar{d_j}"
%format ij = "\HSVar{i_j}"

  We say a change |c :: Chg kappa fam at| is in \emph{minimal}
form if and only if it is closed with respect to some global scope and,
either: (A) |chgDel c| and |chgIns c| have different constructors at their
root or (B) they contain the same constructor and said constructor is
necessary to maintain well-scopedness. In other words, when |chgDel c| and
|chgIns c| contain the same constructor, take
|chgDel c = inj d0 dots dn| and |chgIns c = inj i0 dots in|.  If there
exists a variable |v| that occurs in |ij| but is not defined in |dj|
then we cannot put |inj| into a spine whilst maintaining all
changes well-scoped. \Cref{fig:pepatches:example-minimal} illustrates
some cases.
%}

  Defining whether a change is closed or not has its nuances. Firstly,
we can only know that a change is in fact closed if we know, at least,
how many times each variable is used globally.  Say a variable |x| is
used |n + m| times in total, and it has |n| and |m| occurrences in the
deletion and insertion contexts of |c|, then |x| is not used anywhere
else but in |c|, in other words, |x| is \emph{local} to |c|. If all
variables of |c| are \emph{local} to |c|, we say |c| is closed.  Given
a multiset of variables |g :: Map Int Arity| for the global scope, we
can define |isClosedChg| in Haskell as:

\begin{myhs}
\begin{code}
isClosed :: Map Int Arity -> Map Int Arity -> Map Int Arity -> Bool
isClosed global ds us = unionWith (+) ds us `isSubmapOf` global

isClosedChg :: Map Int Arity -> Chg kappa fam at -> Bool
isClosedChg global (Chg d i) = isClosed global (vars d) (vars i)
\end{code}
\end{myhs}

  Given a well-scoped change |c|, we would like
to compute a spine with minimal changes in its leaves.
We start by computing the least general generalization |s = lgg (chgDel c) (chdIns c)|
which might contain \emph{locally ill-scoped} changes, then we push
constructors that are in the spine into the changes until they are
all closed. Recall \Cref{fig:pepatches:example-03}, which
illustrates this process well. Computing the closure of
\Cref{fig:pepatches:example-03:A} is done by computing
\Cref{fig:pepatches:example-03:B}, then \emph{pushing} the the |Bin|
constructor down the changes, fixing their scope, resulting in
\Cref{fig:pepatches:example-03:C}.

  The |close| function, \Cref{fig:pepatches:close}, is responsible for pushing
constructors through the least general generalization until they
represent minimal changes. It calls an auxiliary version that receives
the global scope and keeps track of the variables it seen so far.
The worst case scenario happens when the we need \emph{all} constructors
of the spine to close the change, in which case, |close c = Hole c|;
yet, if we pass a well-scoped change change to |close|, we must be able
to produce a patch.

  Deciding whether a given change is closed or not requires us to keep
track of the variables we have seen being declared and used in a change.
Recomputing this multisets would be a waste of resources and would yield
a much slower algorithm. The |annWithVars| function below computes the
variables that occur in two contexts and annotates a change with them:

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
        Nothing   ->  let res = chgVarsDistr (Roll (repMap (either' Hole id) aux))
                      in if isClosed gl res then InR (Hole res) else InL res
  where
    fromInR   :: Sum f g x -> Maybe (g x)
\end{code}
\end{myhs}
\caption{The |close| and |closeAux| functions.}
\label{fig:pepatches:close}
\end{figure}

  The |closeAux| function, \Cref{fig:pepatches:close},
receives a spine with leaves of type |WithVars dots|
and attempts to \emph{enlarge} them as necessary.
If it is not possible to close the current spine, we
return a |InL dots| equivalent to pushing all the
constructors of the spine down the deletion and insertion contexts.
The main component behind |closeAux| is |chgVarsDistr|, which distributes
|WithVars| over a spine and computes the union of the
declared and used multisets.

\begin{myhs}
\begin{code}
chgVarsDistr :: Holes kappa fam (WithVars (Chg kappa fam)) at -> WithVars (Chg kappa fam) at
chgVarsDistr rs =  let  us  = map (exElim uses)   (getHoles rs)
                        ds  = map (exElim decls)  (getHoles rs)
                   in WithVars  (unionsWith (+) ds) (unionsWith (+) us)
                                (chgDistr (repMap body rs))
\end{code}
\end{myhs}

  It is worth noting that computing a \emph{locally scoped} patch
from a large monolithic change only helps in preventing situations
such the bad alignment presented in \Cref{fig:pepatches:misalignment:A}.
In fact, let |c| be as in \Cref{fig:pepatches:misalignment:A},
a call to |close c| would return |Hole c| -- meaning |c| is already
in minimal closed form and cannot have a larger spine whilst maintaining
well-scopedness. Another way of putting it is that we at least
do not make things worse, but we surely are not able to recognize
the deletion of |Bin 42| effectively either.

  Recognizing deletions and insertions is crucial for us: no
synchronization algorithm can achieve effective results if it cannot
separate old information from new information. Flagging |Bin 42| as a
deletion in \Cref{fig:pepatches:misalignment:A} means we still must
produce an \emph{alignment} of the minimal changes produced by |close|.

\subsection{Aligning Patches}
\label{sec:pepatches:alignments}

  An aligned patch consists in a spine of copied constructors
leading to a \emph{well-scoped alignment}. This alignment, in turn,
consists in a sequence of insertions, deletions or spines,
which finally lead to a |Chg|. This is not so different from
\texttt{stdiff}s' |Almu|, presented in \Cref{sec:stdiff:diff:fixpoint}.
In addition to simple insertions, deletions and spines we also
add explicit information about copies and permutations to aid
the synchronization engine later on. \Cref{fig:pepatches:alignment-02}
illustrates a value of type |Patch| and its corresponding
alignment, of type |PatchAl| defined below.

\begin{myhs}
\begin{code}
type PatchAl kappa fam = Holes kappa fam (Al kappa fam)
\end{code}
\end{myhs}

\begin{figure}
\centering
\victor{DRAW SCOPES!}

\subfloat[Non aligned patch |p|]{%
\begin{myforest}
[|Bin|, s sep=3mm
  [,change , s sep=1mm
    [|Bin| [x,metavar] [y,metavar]]
    [|Bin| [y,metavar] [x,metavar]]]
  [,change , s sep=1mm
    [z,metavar]
    [|Bin| [|Leaf| [|42|]] [z,metavar]]]]
\end{myforest}}%
\quad
\subfloat[Result of |align p|]{%
\begin{myforest}
[|Bin|
 [|Bin| , alignmentSmall
   [|Prm (metavar x) (metavar y)|]
   [|Prm (metavar y) (metavar x)|]]
 [,insctx , alignmentSmall
   [|Bin| [|Leaf| [|42|]] [SQ]]
   [|Cpy (metavar z)|]]]
\end{myforest}}
\caption{A patch |p| and its corresponding aligned version. Note
how the aligned version provides more information about
which constructors are actually copied inside the
changes performed by |p|.}
\label{fig:pepatches:alignment-02}
\end{figure}

\begin{figure}
\centering
\subfloat[Change that deletes |42| at the head of a list.]{%
\begin{myforest}
[,change , s sep=1mm
  [|(:)| [|42|] [|(:)| [x,metavar] [|(:)| [y,metavar] [z,metavar]]]]
  [|(:)| [x,metavar] [|(:)| [y,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:alignment-01:A}}
\quad\quad
\subfloat[Deletion of |(: 42)| correctly identified.]{%
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
\caption{Properly aligned version of \Cref{fig:pepatches:misaligment}.}
\label{fig:pepatches:alignment-01}
\end{figure}

  Since our patches are locally scoped, computing an aligned patch
is simply done by mapping over the spine and aligning the individual changes.
Computing the \emph{alignment} for a change |c| consists in
identifying which parts of the deletion context correspond
to which pars of the insertion context, that is, which constructors
or metavariables represent \emph{the same information} in the
source object of the change.

  The change shown in \Cref{fig:pepatches:alignment-01:A} -- repeated
from \Cref{fig:pepatches:misalignment:A} -- illustrates
the need for alignments. It is only after recognizing the
root |(:)| in the deletion context as an actual \emph{deletion} that we can
uncover the copies in its children it. If we somehow identify that
the root constructor in the deletion context, |(:)|, represents
the same data as the root constructor in the insertion context,
we would end up having to work with a patch that is unnecessarily
more complicated than it should (\Cref{fig:pepatches:misalignment:B}).
We argue that the correct solution is to identify the \emph{second}
|(:)| constructor in the deletion context with the root of the \emph{first}
insertion context: these really do represent the same information
and, hence, enable us to uncover the simple copies that the patch
performs.

  The deletion of |(: 42)| in \Cref{fig:pepatches:alignment-01:B}
has all fields, except one recursive field, containing no metavariables.
These trees with no metavariables are denoted as \emph{rigid} trees.
A \emph{rigid} tree has the guarantee that none of its
subtrees is being copied, moved or modified. In fact,
\emph{rigid} trees have been entirely deleted from the source or inserted
at the destination of the change. Consequently, if a constructor
in the deletion (resp. insertion) context has all but one of
its subtrees being \emph{rigid}, it is only natural to consider
this constructor to be part of the \emph{deletion} (resp. \emph{insertion}).

  We will be representing a deletion or
insertion of a recursive \emph{layer} by identifying the \emph{position}
where this modification must take place. Moreover, said position
must be a recursive field of the constructor -- that is,
the deletion or insertion must not alter the type that our patch
operates over. This is easy to identify since we
followed typed approach, where we always have access to type-level
information.

  In the remainder of this section we discuss how to represent
an aligned change, such as \Cref{fig:pepatches:alignment-01:B}, and
how to compute them from a |Chg kappa fam at|. Our starting
point is in defining the |alignChg| function, declared below.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
\end{code}
\end{myhs}

  In general, we represent insertions and deletions with a
|Zipper|~\cite{Huet1991}. A zipper over a datatype |t| is
the type of \emph{one-hole-contexts} over |t|, where the hole
indicates a selected position. We will only
be using zippers over a \emph{single} layer of a fixpoint at a time.
In our case, then, a zipper over the |Bin| constructor
is either |Bin SQ u| or |Bin u SQ|, indicating a selected position is
in the left or the right subtree -- we briefly discuss zippers
generically in \ref{sec:gp:simplistic-zipper}.

  A value of type |Zipper| then will be equivalent to one layer of
a fixpoint with one of its recursive positions identified.
It shall carry trees (encoded by |SFix kappa fam|) in all
its positions except one, which represents where the alignment
\emph{continues}. An alignment |Al kappa fam f at| represents a
sequence of insertions and deletions interleaved with spines which
ultimately lead to \emph{modifications}, which are typed according to
the |f| parameter.

\begin{myhs}
\begin{code}
data Al kappa fam f at where
  Del  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f) at -> Al kappa fam f at
  Ins  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f) at -> Al kappa fam f at
\end{code}
\end{myhs}

  The |CompountCnstr| constraint must be carried around to indicate we
are aligning a type that belongs to the mutually recursive family and
therefore has a generic representation -- this is just a Haskell technicality.

  Naturally, if no insertion or deletion can be made but both
insertion and deletion contexts have the same constructor at their
root, we want to recognize this constructor as part of a spine and
continue aligning its fields pairwise.

\begin{myhs}
\begin{code}
  Spn  :: (CompoundCnstr kappa fam x) => SRep (Al kappa fam f) (Rep at) -> Al kappa fam f at
\end{code}
\end{myhs}

  When no |Ins|, |Del| or |Spn| can be used,
we must be fallback to recording a modification,
of type |f at|. Most of the times, |f| will be |Chg kappa fam|,
but we might need to add some extra information in the leaves
of an alignment.

\begin{myhs}
\begin{code}
  Mod  :: f at -> Al kappa fam f at
\end{code}
\end{myhs}

  Finally, it is useful to flag copies and permutations early for they
are simpler to synchronize than arbitrary changes.  A copy is
witnessed by a change |c = Chg (metavar x) (metavar x)| such that
|metavar x| only occurs twice globally. This means all occurrences of
|metavar x| have been accounted for in |c| and the tree at |metavar x|
in the source of the change is not being duplicated anywhere else.

  A permutation, on the other hand, is witnessed by |c = Chg (metavar
x) (metavar y)|, where both |metavar x| and |metavar y| are different
but also occur only twice globally.  It is a bit more restrictive than
a copy, since this represents that the tree at |metavar x| is being
moved -- that is, its \emph{location} is being modified but its \emph{content}
remains the same.

\begin{myhs}
\begin{code}
  Cpy  :: MetaVar kappa fam at                          -> Al kappa fam f at
  Prm  :: MetaVar kappa fam at -> MetaVar kappa fam at  -> Al kappa fam f at
\end{code}
\end{myhs}

  Equipped with a definition for alignments, we move on to defining
|alignChg|.  Given a change |c|, the first step of |alignChg c| is
checking whether the root of |chgDel c| (resp. |chgIns c|) can be deleted
(resp. inserted) -- that is, all of the of the constructor
at the root of |chgDel c| (resp. |chgIns c|) are \emph{rigid} trees
with the exception of a single recursive field. If we can delete the
root, we flag it as a deletion and continue through the recursive
\emph{non-rigid} field. If we cannot perform a deletion at the root of
|chgDel c| nor an insertion at the root of |chgIns c| but they are
constructed with the same constructor, we identify the
constructor as being part of the alignments' spine
and recursing on the children. If |chgDel c| and |chgIns c| do not even
have the same constructor at the root, nor are copies
or permutations, we finally fallback and flag an arbitrary modification.

  To check whether a constructor can be inserted in an efficient manner
we must have this information annotated over the tree. Annotating a tree
augmented with holes with information about whether or not any |Hole|
constructor occurs is done with |annotRigidity|, shown in
\Cref{fig:pepatches:rigidity}.

\begin{figure}
\begin{myhs}
\begin{code}
type IsRigid = Const Bool

isRigid :: HolesAnn kappa fam IsRigid h x -> Bool
isRigid = getConst . getAnn

annotRigidity  :: Holes     kappa fam          h x
               -> HolesAnn  kappa fam IsRigid  h x
annotRigidity = synthesize  aggr                    -- aggregate recursive values
                            (\ _ _ -> Const True)   -- primitives are rigid
                            (\ _ _ -> Const False)  -- holes are not!
  where
    aggr :: U1 b -> SRep IsRigid (Rep b) -> Const Bool b
    aggr _ = Const . repLeaves getConst (&&) True
\end{code}
\end{myhs}
\caption{Annotating a tree augmented with holes with information
about whether or not it actually contains a hole.}
\label{fig:pepatches:rigidity}
\end{figure}

  Once our trees have been annotated with rigidity information,
we proceed to the extraction of a zippers to witness
potential insertions or deletions. This
is done by the |hasRigidZipper| function, which first extracts
\emph{all} possible zippers from the root and checks whether there
is a single on that satisfy the criteria. If there is, we return it
wrapped in a |Just|.

\begin{myhs}
\begin{code}
hasRigidZipper  :: HolesAnn kappa fam IsRigid (MetaVar kappa fam) t
                -> Maybe (Zipper  (CompoundCnstr kappa fam t)
                                  (SFix kappa fam)
                                  (HolesAnn kappa fam IsRigid (MetaVar kappa fam)) t)
\end{code}
\end{myhs}

\victor{I feel I need more info on the paras below}
  The return type is close to almost what the |Del| and |Ins|
constructors expect: a value of type |t| where all but one
recursive positions are populated by the |SFix kappa fam| datatype, \ie{},
trees with \emph{no holes}; \emph{rigid}. The one position,
of type |HolesAnn kappa fam IsRigid dots| identifies the subtree which
we should continue to align against.
We omit the full implementation of |hasRigidZipper| here but invite
the interested reader to check the source code.\victor{where?}

  Finally, we are ready to define |alignChg| in its entirety.  We
start computing the multiset of variables used throughout a patch,
annotate the deletion and insertion context with |IsRigid| and proceed
to actually align them with the |al| function, whose full definition
can be found in \Cref{fig:pepatches:align-fulldef}, and, albeit long,
is rather simple. In general lines, |al| attempts to delete as many
constructors as possible, followed by inserting as many constructors
as possible; whenever it finds that it deleted and inserted the same
constructor, it uses a |Spn| instead and calls itself recursively
on the leaves of the |Spn|. Ultimately, when none of |Del|, |Ins|
or |Spn| can be used it falls back to |Cpy|, |Prm| or |Mod|.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
alignChg c@(Chg d i) = al (chgVargs c) (annotRigidity d) (annotRigidity i)
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
type Aligner kappa fam  = HolesAnn kappa fam IsStiff (MetaVar kappa fam) t
                        -> HolesAnn kappa fam IsStiff (MetaVar kappa fam) t
                        -> Al kappa fam t


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
       Nothing -> alMod vars d i
       Just r  -> Spn (repMap (uncurry' f) r)
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

  The |alignChg| and |disalign|, sketched below, form an isomorphism
between alignments and changes. The |disalign| function is plugs
deletion and insertion zippers, casting a zipper over |SFix| into a
zipper over |Holes| where necessary; distributes the constructors in
the spine into both deletion and insertion contexts and translates
|Cpy| and |Prm| as expected.

\begin{myhs}
\begin{code}
disalign :: Al kappa fam at -> Chg kappa fam at
disalign (Del (Zipper del rest)) =
  let Chg d i = disalign rest
   in Chg (Roll (plug (cast del) d) i)
disalign dots
\end{code}
\end{myhs}

  A spine with alignments in its leaves is denoted
as an aligned patch, and, just like changes,
alignments also easily distribute over spines:

\begin{myhs}
\begin{code}
alDistr :: PatchAl kappa fam at -> Al kappa fam at
alDistr (Hole al)  = al
alDistr (Prim k)   = Spn (Prim k)
alDistr (Roll r)   = Spn (Roll (repMap alDistr r))
\end{code}
\end{myhs}

  Finally, computing aligned patches from locally-scoped patches
is done by mapping over the spine and align the changes
individually, then we make a pass over the result and issue copies for
opaque values that appear on the alignment's spine. The auxiliary
function |align'| returns the successor of the last issued name to
ensure we can easily produce fresh names later on, if need be.
Note that |align| introduces information, namely, new metavariables
that represent copies over opaque values that appear on the alignment's
spine. This means that mapping |disalign| to the result of |align|
will \emph{not} produce the same result. We have \emph{no} isomorphism here.

\begin{myhs}
\begin{code}
align :: Patch kappa fam at -> PatchAl kappa fam at
align = fst . align'

align' :: Patch kappa fam at -> (PatchAl kappa fam at , Int)
align' p = flip runState maxv
         $$ holesMapM (alRefineM cpyPrims . alignChg vars) p
  where
    vars = patchVars p
    maxv = maybe 0 id (lookupMax vars)
\end{code}
\end{myhs}

  The |cpyPrims| above issues a |Cpy i|, for a fresh name |i| whenever
it sees a modification with the form |Chg (Prim x) (Prim y)| and |x == y|.
The |alRefineM f| applies a function in the leaves of the |Al| and
has type.

\begin{myhs}
\begin{code}
alRefineM  :: (Monad m) => (forall x dot f x -> m (Al' kappa fam g x))
           -> Al' kappa fam f ty -> m (Al' kappa fam g ty)
\end{code}
\end{myhs}

  This process of computing alignments showcases
an important aspect of our well-typed approach: the ability
to access type-level information in order to compute
zippers and understand deletions and insertions of a single
layer in a homogeneous fashion -- the type that results from
the insertion or deletion is the same type that is expected
by the insertion or deletion. \digress{At least in my experience,
defining a synchronization algorithm without alignments
proved a significantly more difficult, if not impossible.}

\victor{
Still mention:
\begin{itemize}
  \item Conjecture: arbitrarily deep zippers will give edit-script like complexity!
that's where the log n is hidden.
\end{itemize}
}


\section{Merging Aligned Patches}
\label{sec:pepatches:merging}

  In the previous sections we have seen how |Chg|
can be used as the \emph{representation} of a transformation
between two trees. We have also seen how we can
extract a \emph{spine}, which indicates a prefix of constructors
copied from the source to the destination and leads
to changes, which in turn are \emph{aligned} to reveal
entire insertions and deletions, copies and permutations.
In this section we will be defining our synchronization
algorithm, which uses this extra information to better
merge our patches. At the end, we want to have defined
a function |merge| with the following type:

\begin{myhs}
\begin{code}
merge  :: PatchAl kappa fam at -> PatchAl kappa fam al -> Maybe (PatchC kappa fam at)
\end{code}
\end{myhs}

  The |merge| function, here, receives two \emph{aligned} patches
|p| and |q| that make a span -- have at least one common
element in their domain -- and produces a patch that
can be annotated with conflicts, denoted by |PatchC|, when
both |p| and |q| modify the same subtree in two distinct ways.
If |p| and |q| do \emph{not} make a span it returns |Nothing|.
\Cref{fig:pepatches:mergesquare} illustrates a span of patches |p|
and |q| and their merge which is applied to their common ancestor
and produces a tree which combines the modifications performed
by |p| and |q|, when possible.

\begin{figure}
\centering
\[
\xymatrix{ & O \ar[dl]_{|p|} \ar[dr]^{|q|} \ar[dd]^(0.8){|merge p q|} & \\
          A & & B \\
            & M &}
\]
\caption{Illustration of |merge|.}
\label{fig:pepatches:mergesquare}
\end{figure}

  Recall our patches consist in a spine, which leads to
locally-scoped alignments. These alignments in turn also
have a spine which ultimately leads to modifications. The distinction
between the \emph{outer} spine and the spine inside the
alignments is the scope. Consequently, we can map over
the outer spine without needing to remember information
across calls but we \emph{must} remember information
inside the scope of an alignment. Take the example in
\Cref{fig:pepatches:merge-00}, while synchronizing
the left child of the root, we discover that the tree
located at (or, identified by) |metavar x| was |Leaf 42|.
We must remember this information since we will encounter
|metavar x| again and must see that it matches with
its previous value in order to perform the contraction.
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
\end{myforest}}\qquad%
\subfloat[Patch |q|]{%
\begin{myforest}
[|Bin| , s sep=7mm
  [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]]
  [,insctx , alignmentSmall
    [|Bin| [|Leaf| [|84|]] [SQ]]
    [|Cpy (metavar k)|]]]
\end{myforest}}

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
\end{myforest}}
\caption{Example of a synchronization}
\label{fig:pepatches:merge-00}
\end{figure}

  It helps to think about the metavariables in a change as
a unique identifier for a subtree in the source. For example, if one
change modifies a subtree |metavar x| into a different
subtree |k|, but some other change moves |metavar x| to a different
location in the tree, the result of synchronizing these should be
the transport of |k| into the new location -- which is
exactly where |metavar x| appears in the insertion context.
The example in \Cref{fig:pepatches:merge-01} illustrates this very
situation: the source tree identified by |metavar x| in
the deletion context of \Cref{fig:pepatches:merge-01:B} was
changed, by \Cref{fig:pepatches:merge-01:A}, from |Leaf 42| into
|Leaf 84|. Since |p| altered the content of a subtree, but |q|
altered its location, they are \emph{disjoint} -- they
alter different aspects of the common ancestor. Hence, the
synchronization is possible and results in \Cref{fig:pepatches:merge-01:C}.

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

  A conflict is issued whenever we were not able to reconcile
the alignments in question. This happens either when
we cannot detect that two edits to the same location are non-interfering
or when two edits to the same location interfere with one another.
The |PatchC| datatype encodes patches which might contain conflicts
inside.

\begin{myhs}
\begin{code}
data Conflict kappa fam at  = Conflict String (Al kappa fam at) (Al kappa fam at)

type PatchC kappa fam at    = Holes kappa fam (Sum (Conflict kappa fam) (Chg kappa fam)) at
\end{code}
\end{myhs}

  \digress{Before going into the bowels of synchronization, a little
prelude is due. In this section we will discuss the sketch
of a merge algorithm, but this is by no means final. We believe
a more elegant algorithm could be certainly possible.
Yet, unfortunately, at one point one has to stop and write a thesis.
The sketch we is the last piece I have worked on.}

  We follow with the |mergeAl| function, responsible for
synchronizing alignments. In broad strokes, it is similar to
synchronizing |PatchST|'s, \Cref{sec:stdiff:merging}: insertions
are preserved as long as they do not happen simultaneously.
Deletions must be \emph{applied} before continuing and
copies are the identity of synchronization. In the current setting,
however, we also have permutations and arbitrary changes to look at.
The general conducting line of our synchronization algorithm is to
first record how each subtree was modified and then instantiate these
modifications in a later phase.

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


  We will be keeping track of the equivalences we discover
in a state monad. The instantiation of metavariables
will be stored under |iota| and the list of tree equivalences
will be stored under |eqs|.

\begin{myhs}
\begin{code}
type Subst kappa fam phi = Map (Exists phi)

data MergeState kappa fam = MergeState
  { iota :: Map (Exists (MetaVar kappa fam)) (Exists (Chg      kappa fam))
  , eqs  :: Map (Exists (MetaVar kappa fam)) (Exists (HolesMV  kappa fam))
  }
\end{code}
\end{myhs}

  The equivalences in |eqs| are different from instantiations
in |iota| in an important way. The entries |(metavar v , p)| in |iota|
represent a decision made by the merging algorithm: the subtree
located at |metavar v| must be modified according to patch |p| -- which
means that at the end of the process, there will be no occurrences of |metavar v| left.
The equivalences, on the other hand, represent observations made
by the merging algorithm, that is, an entry |(metavar v , t)| represents
an observation that the subtree at |metavar v| is, in fact, equal to |t|.
These facts may or may not be used later on. For example, say that
there is an entry |(metavar u, metavar v)| in |eqs|, but we
already made a decision about how to instantiate |metavar v|,
that is, there is also an entry |(metavar v , t)| in |iota|.
If we substitute occurrences of |metavar u| for |v| we risk reintroducing
occurrences of |v|, which can yield in patches that cannot be applied.
\digress{I believe that there is a more elegant way to address
this. One option could have been using a single map and register equivalences
some other way. Say that |metavar v| is discovered to be
equivalent to |t|, it could be registered as |(metavar v , Chg t t)|,
that is: |metavar v| was |t| and became |t|. Once again, recall that
the merging algorithm in this section was very much a work-in-progress
while my PhD finished.}

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

  The |mergeAl| function, then, is just a wrapper around |mergeAlM|,
which is defined in terms of the |MergeM| monad, which carries around
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
mergeAlM p q = do
  phase1  <- mergePhase1 p q
  info    <- get
  case splitDelInsMap info of
    Left   _   -> throwConf "failed-contr"
    Right  di  -> alignedMapM (phase2 di) phase1
\end{code}
\end{myhs}

  The first pass is computed by the |mrgPhase1| function, which will
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
|P2Instantiate|, which might include a context we need to check
that the result of the instantiation has disjoint variables
from that provided context. Or checking that two changes are
$\alpha$-equivalent after they have been instantiated.

\begin{myhs}
\begin{code}
data Phase2 kappa fam at where
  P2Instantiate   :: Chg kappa fam at -> Maybe (HolesMV kappa fam at) -> Phase2 kappa fam at
  P2TestEq        :: Chg kappa fam at -> Chg kappa fam at -> Phase2 kappa fam at
\end{code}
\end{myhs}

  Deciding which instruction should be performed depends on the
structure of the alignments under synchronization.  Copies are the
identity element. The |mergePhase1| function is shown in its entirety
in \Cref{fig:pepathes:mergePhase1} but discussed in detail below.
It follows similar reasoning from the merge algorithm for \texttt{stdiff}
(\Cref{sec:stdiff:merge}). In fact, the |Al| datatype resembles the
|Almu| -- both have insertions, deletions and spines but the former
The |mergePhase1| function proceeds by induction on its arguments.

\begin{myhs}
\begin{code}
mergePhase1  :: Al kappa fam x -> Al kappa fam x -> MergeM kappa fam (Al' kappa fam (Phase2 kappa fam) x)
mergePhase1 p q = case (p , q) of dots
\end{code}
\end{myhs}

  The first cases we have to handle are copies, which should be
the identity of synchronization. That is, if |p| is a copy,
all we need to do is modify the tree according to |q| at the
current location. We might need to refine |q| according to
other constraints we discovered in other parts of the alignment
in question, so the final instruction is to \emph{instantiate}
the |Chg| that comes from forgetting the alignment |q|.

\begin{myhs}
\begin{code}
   (Cpy _ , _)  -> return (Mod (P2Instantiate (disalign q)))
   (_ , Cpy _)  -> return (Mod (P2Instantiate (disalign p)))
\end{code}
\end{myhs}

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
equal at the end of the process.

\begin{myhs}
\begin{code}
mrgPrmPrm  :: MetaVar kappa fam x -> MetaVar kappa fam x
           -> MetaVar kappa fam x -> MetaVar kappa fam x
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
mrgPrm  :: MetaVar kappa fam x -> MetaVar kappa fam x -> Chg kappa fam x
        -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrm x y c  =   addToIota "prm-chg" x c
              >>  return (P2Instantiate (Chg (Hole x) (Hole y)) Nothing)
\end{code}
\end{myhs}

  The |addToIota| function inserts the |(x, c)| entry in |iota| if |x|
is not yet a member. It raises a conflict with the supplied label
if |x| is already in |iota| with a value that is different than |c|.
\digress{I believe that we could develop a better algorithm if instead
of forbidding values different than |c| we check to see whether the
two different values can also be merged. I ran into many difficulties
tracking how subtrees were moved and opted for the easy and pragmatic
option of not doing anything difficult here.}

  Worth noting that the call to |addToIota| in |mrgPrm|, above,
will never raise a |"prm-chg"| conflict. This is because |metavar x|
and |metavar y| are classified as a permutation hence, each variable occurs
exactly once in the deletion and once in the insertion contexts.
Therefore, it is impossible that |x| above was already a member of |iota|.
\digress{In fact, when we come to discussing the experiments,
in \Cref{chap:experiments}, we see that |"prm-chg"| never showed up
as a conflict in our whole dataset.}

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

  Deletions must be \emph{executed}. If one patch
deletes a constructor but the other modifies the fields the
constructor, we must ensure that none of the deleted fields
have been modified by the other patch. This is done by the |tryDel|
function, which attempts to delete a zipper from an alignment, and,
if successful, returns the pair of alignments we should continue
to merge.

\begin{myhs}
\begin{code}
   (Del zp@(Zipper z _), _)  -> Del . Zipper z <$$> (tryDel zp q >>= uncurry mrgPhase1)
   (_, Del zq@(Zipper z _))  -> Del . Zipper z <$$> (tryDel zq p >>= uncurry mrgPhase1)
\end{code} %
\end{myhs}

  Note that since |merge| is symmetric, we an freely swap the order
of arguments. \digress{Let me rephrase that. The |merge| \emph{should}
be symmetric, and \texttt{QuickCheck} tests were positive of this, but I have no
proof.}

  The |tryDel| function matches on the possible cases for |q| (resp. |p|)
and checks whether there are any modifications to the locations the
zipper wants to delete. If there are, we throw a conflict, otherwise
we can continue.

\begin{myhs}
\begin{code}
tryDel  :: Zipper (CompoundCnstr kappa fam x) (SFix kappa fam) (Al kappa fam) x
        -> Al kappa fam x
        -> MergeM kappa fam (Al kappa fam x , Al kappa fam x)
tryDel (Zipper z h) (Del (Zipper z' h'))
  | z == z'    = return (h , h')
  | otherwise  = throwConf "del-del"
tryDel (Zipper z h) (Spn rep) = case zipperRepZip z rep of
    Nothing  -> throwNotASpan
    Just r   -> let hs = repLeavesList r
                 in case partition (exElim isInR1) hs of
                      ([Exists (InL Refl :*: x)] , xs)
                        | all isCpyL1 xs  -> return (h , x)
                        | otherwise       -> throwConf "del-spn"
                      _                   -> error "unreachable; zipRepZip invariant"
tryDel (Zipper _ _) _ = throwConf "del-mod"
\end{code}
\end{myhs}

  Spines and modifications are one of the trickiest cases we
have to manage. Intuitively, we want to match the deletion
context of the change against the spine and, when successful,
return the result of instantiating the insertion context of
the change. Yet, we must later check that we did \emph{not}
introduce duplications by doing so, as illustrated
in \Cref{fig:pepatches:merge-03}.

\begin{myhs}
\begin{code}
   (Mod p', Spn q')  -> Mod <$$> mrgChgSpn p' q'
   (Spn p', Mod q')  -> Mod <$$> mrgChgSpn q' p'
\end{code}
\end{myhs}

  The |mrgChgSpn| function, below, matches the deletion
context of the |Chg| against the spine and and returns
a |P2Instantiate| instruction for change. The instantiation
function here, |instM|, receives a deletion context and an alignment
and attempts to assign the variables in the deletion context
to changes inside the spine. This is possible whenever
the modifications in the spine occur further from the root
than the variables in the spine. \Cref{fig:pepatches:instm}
illustrates the implementation of |instM|.

\begin{figure}
\begin{myhs}
\begin{code}
instM :: (All Eq kappa) => HolesMV kappa fam at -> Al kappa fam at -> MergeM kappa fam ()
instM _           (Cpy _)  = return ()
instM (Hole v)    a        = addToIota "inst-contr" v (disalign a)
-- Del ctx and spine must form a span; cannot reference different constructors or primitives.
instM x@(Prim _)  d        = when (x /= chgDel (disalign d)) throwNotASpan
instM (Roll r)    (Spn s)  = case zipSRep r s of
    Nothing   -> throwNotASpan
    Just res  -> void (repMapM (\x -> uncurry' instM x >> return x) res)
-- Spine wants to change a portion of the tree that is deleted by the deletion context.
instM _         (Mod _)    = throwConf "inst-mod"
instM _         (Prm _ _)  = throwConf "inst-perm"
instM (Roll _)  (Ins _)    = throwConf "inst-ins"
instM (Roll _)  (Del _)    = throwConf "inst-del"
\end{code}
\end{myhs}
\caption{Implementation of |instM|.}
\label{fig:pepatches:instm}
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

  In |mrgChgSpn| we must check that the variables that would show up
in the result, after the second phase is done, do not mention any
variable that occurs in the insertion contexts of the
spine. \Cref{fig:pepatches:merge-03} illustrates a case where failing
to perform this check would result in an erroneous duplication of the
value |2|. Matching the deletion context of |chg = Chg (metavar c) (metavar
a : metavar c)| against the spine |spn = Spn (Cpy : Chg (metavar z)
(metavar x : (metavar z)))| yields |c| equal to |spn|, which
correctly identifies that the subtree at |metavar c| was modified according to |spn|.
The observation, however, is that the insertion
context of |chg| mentions |metavar a|, which is a subtree that comes
from outside the deletion context of |chg|. If we do not perform
any further check and proceed naively, we would end up
substituting |metavar c| for |ctxDel (disalign spn)|
and for |ctxIns (disalign spn)| in |ctxDel chg| and |ctxIns chg|, respectively,
which would result in:

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
will reject this by performing a check that ensures the set of
subtrees that appear in the result of instantiating |chg| is disjoint
from the set of subtrees that were moved around by |spn|. \digress{I
dislike this aspect of this synchronization algorithm quite a lot, it
feels unnecessarily complex and with no really good justification
besides the example in \Cref{fig:pepatches:merge-03}, which was distilled
from real conflicts. There must be a more disciplined way of disallowing duplications to be
introduced without this but I could not figure it out.}

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
\caption{Example of two conflicting patches for moving
the same subtree into two different locations. The patches
here are operating over pairs of lists.}
\label{fig:pepatches:merge-03}
\end{figure}

  Merging two spines is simple. We know they must
reference the same constructor since the arguments
to |merge| form a span. All that we have to do
is recurse on the paired fields of the spines, pointwise:

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
where |metavar x| or |metavar y| appears three or more times globally,
we attempt to instantiate them with according to the
how this subtree was changed and move on.

\begin{myhs}
\begin{code}
mrgChgDup  :: Chg kappa fam x -> Chg kappa fam x -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgDup dup@(Chg (Hole v) _) q' = do
  addToIota "chg-dup" v q'
  return (P2Instantiate dup Nothing)
\end{code}
\end{myhs}

  If they are not duplications, nor none of the cases previously
handled by |mergePhase1|, then the best we can do is register
equivalence of their domains -- recall both patches being merged must
form a span -- and synchronize successfully when both changes are
equal.

\begin{myhs}
\begin{code}
mrgChgChg :: Chg kappa fam x -> Chg kappa fam x -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgChg p' q'  | isDup p'   = mrgChgDup p' q'
                 | isDup q'   = mrgChgDup q' p'
                 | otherwise  = case unify (chgDel p') (chgDel q') of
                      Left  _   -> throwNotASpan
                      Right r   -> onEqvs (M.union r)
                                >> return (P2TestEq p' q')
\end{code}
\end{myhs}

  \Cref{fig:pepatches:mergePhase1} collects all the cases discussed
above and illustrates the full definition of |mergePhase1|.
Once the first pass is done, however, we have collected information
about how each subtree has been changed and potential subtree
equivalences we might have discovered. The next step is to synthesize
this information into two maps: a deletion map that informs us
what a subtree \emph{was} and a insertion map that informs us
what a subtree \emph{became}, so we can perform the |P2Instante|
instructions.

\begin{figure}
\begin{myhs}[.99\textwidth]
\begin{code}
mrgPhase1 p q = case (p , q) of
   (Cpy _ , _)  -> return (Mod (P2Instantiate (disalign q)))
   (_ , Cpy _)  -> return (Mod (P2Instantiate (disalign p)))

   (Prm x y, Prm x' y')  -> Mod <$$> mrgPrmPrm x y x' y'
   (Prm x y, _)          -> Mod <$$> mrgPrm x y (disalign q)
   (_, Prm x y)          -> Mod <$$> mrgPrm x y (disalign p)

   -- Insertions are preserved as long as they are not simultaneous.
   (Ins (Zipper z p'), Ins (Zipper z' q'))
     | z == z'   -> Ins . Zipper z <$$> mergePhase1 p' q'
     | otherwise -> throwConf "ins-ins"
   (Ins (Zipper z p'), _) -> Ins . Zipper z <$$> mrgPhase1 p' q
   (_ ,Ins (Zipper z q')) -> Ins . Zipper z <$$> mrgPhase1 p q'

   -- Deletions need to be checked for compatibility: we try
   -- and "apply" the deletion to the other alignment
   (Del zp@(Zipper z _), _) -> Del . Zipper z <$$> (tryDel zp q >>= uncurry mrgPhase1)
   (_, Del zq@(Zipper z _)) -> Del . Zipper z <$$> (tryDel zq p >>= uncurry mrgPhase1 . swap)

   -- Spines mean that on one hand a constructor was copied; but the mod
   -- indicates this constructor changed.
   (Mod p', Spn q') -> Mod <$$> mrgChgSpn p' q'
   (Spn p', Mod q') -> Mod <$$> mrgChgSpn q' p'

   -- Two spines it is easy, just pointwise merge their recursive positions
   (Spn p', Spn q') -> case zipSRep p' q' of
       Nothing -> throwNotASpan
       Just r  -> Spn <$$> repMapM (uncurry' mrgPhase1) r

   -- Finally, modifications sould be instantiated, if possible.
   (Mod p', Mod q') -> Mod <$$> mrgChgChg p' q'
\end{code}
\end{myhs}
\caption{Full implementation of |mergePhase1|.}
\label{fig:pepatches:mergePhase1}
\end{figure}

  Splitting |iota| and |eqvs| require some attention. For example,
imagine there exists an entry in |iota| that assigns |metavar 0|
to |Chg (Hole (metavar 1)) (: 42 (Hole (metavar 1)))|, this tells us that
the tree identified by |metavar 0| is the same as the tree identified
by |metavar 1|, and it became |(: 42 (metavar 1))|. Now suppose that
|metavar 0| was duplicated somewhere else, and we come across
an equivalence that says |metavar 1 == metavar 0|. We cannot simply insert
this into |iota| because the merge algorithm made the decision to
remove all occurrences of |metavar 0|, not of |metavar 1|, even
though they identify the same subtree. This is important to ensure
we produce patches that can be applied.

  The |splitDelInsMaps| function is responsible for synthesizing the
information gathered in the first pass of the synchronization
algorithm. Splitting |iota| is easy, we just use the deletion and
insertion context of the changes that overlapped a given
metavariable. Next, we partitioning the equivalences into rigid
equivalences, of the form |(metavar v , t)| where |t| has no holes, or
non-rigid equivalences. The rigid equivalences are added to both
deletion and insertion maps, but the non-rigid ones, |(metavar v ,
t)|, are are only added when there is no information about the
|metavar v| in the map and, if |t == metavar u|, we also check
that there is no information about |metavar u| in the map.
Finally, after these have been added to the map, we all |minimize|
to produce an idempotent substitution we can use for phase two.
If an occurs-check error is raised, this is forwarded as a conflict.

\begin{myhs}
\begin{code}
splitDelInsMaps  :: MergeState kappa fam
                 -> Either [Exists (MetaVar kappa fam)]
                           (  Subst kappa fam (MetaVar kappa fam) ,  Subst kappa fam (MetaVar kappa fam))
splitDelInsMaps (MergeState iot eqvs) = do
    let e' = splitEqvs eqvs
    d <- addEqvsAndSimpl (map (exMap chgDel) iot) e'
    i <- addEqvsAndSimpl (map (exMap chgIns) iot) e'
    return (d , i)
\end{code}
\end{myhs}

  Finally, after computing the insertion and deletion maps that
inform us how each identified subtree was modified, we make
a second pass over the partial result executing the necessary instructions.
The instructions include checking two changes for equality, returning
their refinement upon success, simply refining a change or
refining and ensuring it has no common variables with some
term.

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

  The |getCommonVars| simply computes the intersection of the variables
in two |Holes kappa fam at|.

  \victor{I would love to give better reasons for this to be the
way it is. But the truth is it is like this because this is
what worked... Can I just write something like that?}

  Refining changes according to the inferred information about what each tree
was and became is straightforward, all we must do is apply the deletion map to
the deletion context and the insertion map to the insertion context.

\begin{myhs}
\begin{code}
refineChg :: Subst2 kappa fam -> Chg kappa fam at -> Chg kappa fam at
refineChg (d , i) (Chg del ins) = Chg (substApply d del) (substApply i ins)
\end{code}
\end{myhs}

  When deciding whether two changes are equal, its also important
to refine them first, since they might be $\alpha$-equal.

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

\victor{Check \cite{Saito2002}; place our algos in their taxonomy}

\victor{Harmoy has a similar problem as we found with lists;
check page 13 for \cite{Foster2007}; we do it differently overall.
Our merge proposes a mix of local and global alignments to solve this
in a satisfactory manner}

\victor{Actually; \texttt{hdiff} with alignment really improves on that
by essentially enabling permutations and duplications over \texttt{stdiff}}
\victor{Another aspect is that \texttt{hdiff} actually uses type information
when doing synchronization; this is pretty neat and apparently the (only) use for
types in structural diffing}

\victor{What else do we want to discuss here?}
\victor{Mention results and forward to experiments for further details?}

\victor{Best mereg rate so far is:
\texttt{hdiff merge -d nonest -k spine *.java}
with 900 successes (and 500 merge diffs); check commit \texttt{11aebdf9cf0b57b97734ede0285c7df8d4dfe28a}
on hdiff to reproduce}

\section{Discussion and Further Work}
\label{sec:pepatches:discussion}

\victor{
\begin{itemize}
  \item Better control over the tree matching process (ability
to ignore source-location tokens for instance; ability to
specify scope-aware sharing)

  \item Look into more extraction methods; understand whether there
is a sensible notion of ``best'' patch.

  \item Agda formalization of \texttt{hdiff}, in particular, the merge algorithm.

  \item Generalization to merging $n$ files

  \item Generalization to arbitraryily-deep zippers
\end{itemize}
}


\victor{Frst person or third person?}

  With \texttt{hdiff} we have seen that a complete detachment from edit-scripts
enables us to define a computationally efficient differencing algorithm.
Moreover, we have seen how our patches can still be merged
and posses a sensible algebraic structure. Although we will
discuss empirical results shortly, in \Cref{chap:experiments}, we advance
that \texttt{hdiff} has shown a strong potential for practical use.
The current state of \texttt{hdiff}, however, is still that of a \emph{proof-of-concept}
as opposed to a practical implementation of a tool. In this section
we will discuss a number aspects that were left as future work.

\subsubsection{Refining Matching and Sharing Control}
  In its current state, the matching engine uses hashes indiscriminately. 
All information under a subtree is used to compute its hash. This
might not be desirable though, imagine a parser that annotates
its resulting AST with source-location tokens. This would mean that
if a statement was permuted, we would not be able to recognize it as such,
since both occurrences would have different source-location tokens and,
consequently, different hashes.

  This issue goes hand in hand with deciding which parts of the tree can
be shared and up until which point. For example, we probably never
want to share local statements outside their scope.  Recall we avoided
this issue by restricting whether a subtree could be shared
or not based on its \emph{height}. This was a pragmatic design choice
that enabled us to make progress but it is a work-around at its best.

  Salting the hash function of |preprocess| is also not an option.
If the information driving the salt function changes, none of the
subtrees under there can be shared again. To illustrate this,
suppose we push scope names into a stack with a
function |intrScope :: SFix kappa fam at -> Maybe String|, which would be
supplied by the user and returns a |Just| whenever the datatype in question
introduces a scope. The definition of |intrScope| would naturally depend
on the universe in question. The |const Nothing| function works as a default
value, meaning that the mutually recursive family in question has no
scope-dependent naming. A more interesting |intrScope| is given below.

\begin{myhs}
\begin{code}
intrScope m@(Module dots)        = Just (moduleName m)
intrScope f@(FunctionDecl dots)  = Just (functionName f)
intrScope _                      = Nothing
\end{code}
\end{myhs}

  With |intrScope| as above, we could instruct the |preprocess| to push module names
and function names every time it traverses through one such element
of the family. For example, preprocessing the pseudo-code below would
mean that the hash for \verb!a! inside \verb!fib! would be
computed with |["m" , "fib"]| as a salt; but \verb!a! inside \verb!fat!
would be computed with |["m" , "fat"]| as a salt, yielding a different hash.

\begin{verbatim}
module m
  fib n = let a = 0; b = 1; ...
  fat n = let a = 0; ...
\end{verbatim}

  This will work out well for many cases, but as soon as a change altered any information
that was being used as a salt, nothing could be shared anymore. For example,
if we rename \verb!module m! to \verb!module x!, the source and destination
would contain no common hashes, since we would have used |["m"]| to salt the hashes
for the source tree, but |["x"]| for the destination, yielding different hashes.

  This problem is twofold, however. Besides identifying the algorithmic
means to ensure \texttt{hdiff} could be scope-aware and respect said scopes,
we must also engineer an interface to enable the user to easily define
said scopes. We envisioned a design with a custom version of the \genericssimpl{}
library, with an added alias for the identity functor that could receive special treatment,
for example:

\begin{myhs}
\begin{code}
newtype Scoped f = Scoped { unScoped :: f }

data Decl = ImportDecl dots
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
the best option to move forward in an early stage.

\subsubsection{Extraction Methods, \emph{Best} Patch and Edit-Scripts}
We have presented three extraction methods, which we called |NoNested|, |ProperShare| and |Patience|.
Computing the diff between two trees using different extraction methods can produce
different patches. Certainly there can be more extraction methods. One such
example that we never had the time to implement was a refinement of |ProperShare|,
aimed at breaking the sharing introduced by it. The idea was to list the the metavariables
that appear in the deletion and insertion context and compute the LCS between
these lists. The location of copies enable us to break sharing and introduce new metavariables.
For example, take the change below.

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

  The list of metavariables in the deletion context is |[metavar x , metavar x , metavar z , metavar x]|,
but in the insertion context we have |[metavar x , metavar z , metavar x]|. Computing the
LCS between these lists yields |[Del x , Cpy , Cpy , Cpy]|. The first |Del| suggests a contraction
is really necessary, but the last copy shows that we could \emph{break} the sharing by renaming
|(metavar x)| to |(metavar k)|, for example. This would essentially transform the change
above into:

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

  Forgetting about sharing is just one example of a different context extraction mechanism and,
without a formal notion about when a patch is \emph{better} than another,
its impossible to make a decision about which context extraction should be
used. Our experimental results suggest that |Patience| yields patches that
merge successfully more often, but this is far from providing a metric
on patches, like the usual notion of cost does for edit-scripts.

\victor{more text?}

\paragraph{Relation to Edit-Scripts.} Another interesting aspect that
we would have liked to look at is the relation between our |Patch| datatype
and traditional edit-scripts. The idea of breaking sharing above can be used
to translate our patches to an edit-script. Some early experiments did show
that we could use this method to compute approximations of the least-cost
edit-script in linear time, but more research is needed to validate this.

\victor{We know, for a fact, that computing the least cost edit-script
take $\mathcal{O}(n \log{n})$. Our algo computes a patch
in $\mathcal{O}(n)$. Whats the relaton? where's the $\log{n}$?}

\subsubsection{Formalizations and Generalizations}
Formalizing and proving properties about our |diff| and |merge| functions
was also on my list of things to do. As it turns out, the extensional nature
of |Patch| makes for a difficult Agda formalization, which is the reason
we this was left as further work.

  The value of a formalization goes beyond enabling us to prove
important properties. It also provides a laboratory for generalizing
aspects of the algorithms. Two of those immediately jump to mind:
generalizing the merge function to merge $n$ patches and
generalizing alignments insertions and deletions zippers to be
of arbitrary depth, instead of a single layer.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
