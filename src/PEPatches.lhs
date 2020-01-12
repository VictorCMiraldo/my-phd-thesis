  The \texttt{stdiff} approach, which provided a first representation
of tree-sructured patches for tree-structured data was stil very
much coupled with edit-scripts: we still suffered the ambuiguity problem,
which was reflected on the coputationally expensive algorithm. We were also
subject to being unable to represent permutations and moves efficiently.
Overcoming these drawbacks required a significant shift in perspective and
represents a complete decoupling from edit-script based differencing algorithms.

  In general, differening algorithms are divided in a matching phase, which
identifies which subtrees should be copied, and later extrapolates one edit-script
from said tree matching. The main idea of \texttt{hdiff} is to forget about the
second part altogether and use the tree matching \emph{as the patch}.
This gave rise to the |PatchPE x| type, our second attempt at detaching from 
edit scripts, which will be explored in this chapter.

  Suppose we want to write a patch that modifies the left element
of a binary tree. If we had the full Haskell programming language available
as the patch language, we would probably write somethgin in the lines of:

\begin{myhs}
\begin{code}
p :: Tree -> Maybe Tree
p (Bin (Leaf x) y) 
  | x == 10    = Just (Bin (Leaf 42) y)
  | otherwise  = Nothing
p _            = Nothing
\end{code}
\end{myhs}

  Looking at the |p| function above, we see it has a clear domain --
a set of |Tree|s that when applied to |p| yields a |Just| -- which is specified
by the pattern and guards, and we see it has a clear transformation
for each tree in the domain: it replaces the |10| by |42| inplace.
Taking a magnifying glass at that definition, we can interpret
the matching of the pattern as a \emph{deletion} phase and the construction
of the resulting tree as a \emph{insertion} phase. The overall idea of
the \texttt{hdiff} approach is to represent the patch |p| exactly as
that: a pattern and a expression. Essentially, we could write |p|
as |patch (Bin (Leaf 10) y) (Bin (Leaf 42) y)|, or, graphically
as in \Cref{fig:pepatches:example-01}.
\victor{Find a graphical repr for metavars that does not rely on color;
explain it here}

\begin{figure}
\centering
\begin{forest}
[,rootchange
  [|Bin| [|Leaf| [10]] [y,metavar]]
  [|Bin| [|Leaf| [42]] [y,metavar]]
]
\end{forest}
\caption{Graphical represntation of a patch that modifies the left
children of a binary node}
\label{fig:pepatches:example-01}
\end{figure}

  With this added expressivity we can represent more transformations
than before. Take the patch that swaps two subtrees, which cannot
even be written using an edit-script based approach, here it is
given by |patch (Bin x y) (Bin y x)|. Another helpful consequence of
our design is that we bypass the \emph{choice} phase of the
algorithm. When computing the differences between |Bin Leaf Leaf|
and |Leaf|, for example, we do not have to chose one |Leaf| to copy
because we can copy both with the help of a contraction operation. The patch
that witnesses this would be |patch (Bin x x) x|. This optimization
enables us to write linear |diff| algorithms even in the presence
of permutations and duplications. 

  This chapter arises as a refinement from our ICFP'19 publication~\cite{Miraldo2019},
where we explore the representation and computation aspects of \texttt{hdiff}.
The big shift in paradigm of \texttt{hdiff} also requires a more careful look into 
the metatheory and nuances of the algorithm, which were not present in said contribution.
Moreover, we first wrote our algorithm~\cite{Miraldo2019} using the \texttt{generics-mrsop}
library even though \texttt{hdiff} does not require an explicit sums of products. This means
we can port it to \texttt{generics-simplistic-deep} and gather real world data fort
his approach. We present our code in this section on the \texttt{generics-simplistic-deep} framework.
\victor{Maybe we write a paper with pierre about it?}

\victor{
  Unfortunately with the added complexity reasoning about patches
becomes more complicated. Moreover, an altogether new approach requires 
us to think of some metatheory.
}

\victor{
\begin{itemize}
  \item Deatch from edit-scripts;
  \item talk about hash-consing and how to use different extraction
        algorithms (no-nested; proper-share and patience)
  \item overall complexity of patches is a big deal; see composition and merging (if we eventually make one)
\end{itemize}
}

\section{The Type of Patches}

  Just like \texttt{stdiff}, discussed in \Cref{chap:structural-patches}, we will rely on
\texttt{generics-mrsop} to encode our operations and algorithms generically. 
The first step in representing our patches is to augment the generic representation of our trees
with metavariables. This was, in fact, the reason for us to add the |Holes| datatype 
to \texttt{generics-mrsop} (\Cref{sec:gp:holes}). Recall its definition:

\begin{myhs}
\begin{code}
 data Holes :: (kon -> Star) -> [[[Atom kon]]] -> (Atom kon -> Star) -> Atom kon -> Star
    where
  Hole   :: phi at  -> Holes kappa codes phi at
  HOpq   :: kappa k -> Holes kappa codes phi ((P K) k)
  HPeel  :: (IsNat n , IsNat i)
         => Constr (Lkup i codes) n
         -> NP (Holes kappa codes phi) (Lkup n (Lkup i codes))
         -> Holes kappa codes phi ((P I) i) 
\end{code}
\end{myhs}

  If we put values of type |Const Int| in the holes,
as in |Holes ki codes (Const Int)|, we would get a functor mapping an
index of the family into its representation, augmented with integers,
representing metavariables. This is almost enough, yet, we would run into 
problems whenever we tried to inder the type of a metavariable over
an opaque value. For this reason, we must keep the opaque values
around in order to be able to compare their type-level indicies.

\begin{myhs}
\begin{code}
data Annotate (x :: Star) (f :: k -> Star) :: k -> Star where
  Annotate :: x -> f i -> Annotate x f i

type MetaVar ki = NA (Annotate Int ki) (Const Int)
\end{code}
\end{myhs}

  With |MetaVar| as defined above, we can always fetch the |Int| identifying
the metavar but we posses much more type-level information that is inspectable
at run-time. 

  Next we define \emph{changes} to be a pair of a deletion context
and an insertion context for the same type. As expected, these contexts
are values of the mutually recursive family in question augmented
with metavariables.

\begin{myhs}
\begin{code}
data Chg ki codes at = Chg
  { chgDel  :: Holes ki codes (MetaVar ki) at
  , chgIns  :: Holes ki codes (MetaVar ki) at
  }
\end{code}
\end{myhs}

  It is worth noting that there might be a lot of redundant information
in a value of type |Chg ki codes at|. Take for example the
change that swaps two elements of a binary tree. Both the deletion context
and the insertion context contains a |Bin| constructor -- as
illustrated in \Cref{fig:pepatches:change-versus-patch:chg}.
This indicates, in fact, that the |Bin| constructor is being
copied from the source to the destination. To make this evident
we define a |Patch| to be the anti-unification of a change's
deletion and insertion contexts -- in this case, illustrated
in \Cref{fig:pepatches:change-versus-patch:patch} and defined below.
We call the prefix of constructors that are copied from source
to the destination the \emph{spine} of the patch.

\begin{figure}
\centering
\subfloat[swap as a \emph{change}]{%
\begin{forest}
[,rootchange 
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]
]
\end{forest}
\label{fig:pepatches:change-versus-patch:chg}}%
\quad\quad\quad
\subfloat[swap as a \emph{patch}]{%
\begin{forest}
[|Bin|,s sep = 5mm%make it wider
  [,change [x,metavar] [y,metavar]]
  [,change [y,metavar] [x,metavar]]
]
\end{forest}
\label{fig:pepatches:change-versus-patch:patch}}%
\caption{Two isomorphic representations -- with and without
an explicit spine -- for the patch that swaps the children
of a binary node}
\label{fig:pepatches:change-versus-patch}
\end{figure}

\begin{myhs}
\begin{code}
type PatchPE ki codes = Holes ki codes (Chg ki codes)
\end{code}
\end{myhs}

  This distinction between patches and changes only plays
an important role when defining the merging algorithm. 
but since one can easily convert between one another
the graphical representation of patches will be that without
a spine.
\victor{If it only matters there, why did I put it here?}

  Converting between patches and changes is simple. Moreover,
if we assume that |PatchPE ki codes| is in fact the result
of anti-unifying the deletion and insertion contexts of a change
-- has a maximal spine -- then we have an isomorphism.

\begin{myhs}
\begin{code}
change2patch :: Chg ki codes at -> PatchPE ki codes at
change2patch (Chg d i) = holesMap (uncurry' Chg) (holesLCP d i)

patch2change :: PatchPE ki codes at -> Chg ki codes at
patch2change p = Chg  (holesJoin (holesMap chgDel  p))
                      (holesJoin (holesMap chgIns  p))
\end{code}
\end{myhs}





\subsection{Relationship with \texttt{gdiff}}

  A |PatchPE| together with an element
in its domain can be transformed into a |PatchGDiff|.

  Not of optimal cost, though.

\subsection{Meta Theory}

  The disadvantage of using a completely different technique
to talk about patches is that we must discuss its metatheory.
In this section we show this design offers a reasnable option
for representing patches.

\victor{
The |PatchPE ki codes| forms either:
\begin{itemize}
\item Partial monoid, if we want |vars ins <= vars del|
\item Grupoid, if we take |vars ins == vars del|
\end{itemize}
}
\section{Merging Patches}

\section{Computing |PatchPE|}

\begin{figure}
\centering
\subfloat[|DM_NoNest| extraction]{%
\begin{forest}
[,rootchange 
  [|Bin| [x,metavar] [k]]
  [|Bin| [x,metavar] [t]]
]
\end{forest}
\label{fig:pepatches:extraction-01:nonest}}%
\quad\quad
\subfloat[|DM_Proper| extraction]{%
\begin{forest}
[,rootchange 
  [|Bin| [|Bin| [x,metavar] [y,metavar]] [k]]
  [|Bin| [|Bin| [x,metavar] [y,metavar]] [x,metavar]]
]
\end{forest}
\label{fig:pepatches:extraction-01:proper}}%
\caption{Computing the |diff| between |Bin (Bin t u) k| and
|Bin (Bin t u) t| using two different extraction methods}
\label{fig:pepatches:extraction-01}
\end{figure}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
