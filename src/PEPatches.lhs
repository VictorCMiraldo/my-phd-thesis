  The \texttt{stdiff} approach gave us a first representation
of tree-sructured patches over tree-structured data but was still flawed in
many ways. These flaws were partly due to the hidden connection to edit
scripts that still remained: subtrees could only be copied once and could not
be permuted. This meant we still suffered the ambuiguity problem,
which was reflected on the coputationally expensive algorithm.
Overcoming these drawbacks required a significant shift in perspective and
represents, finally, a more thorough decoupling from edit-script based 
differencing algorithms.

  Classically, tree differencing algorithms are divided in a matching
phase, which identifies which subtrees should be copied, and later
extrapolates one edit-script from said tree matching
(\Cref{sec:background:tree-edit-distnace}). This separation of
concerns means that we do not have to deal with the ambiguities of
edit scripts, but the desire to obtain said edit script still means
that the matchings produced by these algorithms are very restrictive
-- order preserving partial bijections between the flattened nodes of
the trees in question, \Cref{fig:background:tree-mapping}.

  Suppose we want to write a change that modifies the left element
of a binary tree. If we had the full Haskell programming language available
as the patch language, we would probably write something in the lines of:

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
of the resulting tree as a \emph{insertion} phase. 
The \texttt{hdiff} approach represents the change in |p| exactly as
that: a pattern and a expression. Essentially, we could write |p|
as |patch (Bin (Leaf 10) y) (Bin (Leaf 42) y)| -- represented graphically
as in \Cref{fig:pepatches:example-01}. An important aspect here
is that the graphical notation makes it evident which
constructors were copied until we reach the point where a change
must be made. The notation $\digemFormatMetavar{\square}$ is
used to indicate $\square$ is a metavariable, that is, given a successful
matching of the deletion context against an element $\digemFormatMetavar{\square}$
will be given a value.

\begin{figure}
\centering
\begin{forest}
[|Bin| 
  [|Leaf| [,change [|10|] [|42|]]]
  [,change [y,metavar] [y,metavar]]
]
\end{forest}
\caption{Graphical represntation of a patch that modifies the left
children of a binary node}
\label{fig:pepatches:example-01}
\end{figure}

  In fact, the core idea behind \texttt{hdiff} is to forget about
translating matchings back to edit scripts, using instead the tree
matching \emph{as the patch}.  Consequently, we can also drop the
restrictions on tree matchings and use any matching that we can
compute. On this chapter we shall study how the |PatchPE x| will
encode (relaxed) tree matchings, how to write a synchronizer for these
patches and finally how to compute these patches efficiently.

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


  This chapter arises as a refinement from our ICFP'19
publication~\cite{Miraldo2019}, where we explore the representation
and computation aspects of \texttt{hdiff}.  The big shift in paradigm
of \texttt{hdiff} also requires a more careful look into the
metatheory and nuances of the algorithm, which were not present in
said contribution.  Moreover, we first wrote our
algorithm~\cite{Miraldo2019} using the \texttt{generics-mrsop} library
even though \texttt{hdiff} does not require an explicit sums of
products. This means we can port it to \genericssimpl{} and gather
real world data fort his approach. We present our code in this section
on the \genericssimpl{} library.

\victor{Maybe we write a paper with pierre about it?}

\section{The Type of Patches}

\victor{Actually, my thesis is about understanding the tradeoffs; do we
want alignments? Well, inly if we are interested in merging. Do we
want to identify duplications: different extraction strategies; etc...
There are many design choices in this domain that I have studied;
the point being: no right answer here}

  The type |PatchPE x| encapsulates the transformations we wish to support
over elements of type |x|. In general lines, it consists in (A) a \emph{pattern}, or
deletion context, which instantiates a number of metavariables when matched against
an actual value; and (B) a \emph{expression}, or insertion context, which uses
the instantiation provided by the deletion context to substitute its variables,
yielding the final result. Both insertion and deletion contexts are simply inhabitants
of the type |x| augmented with \emph{metavariables}.

  Augmenting the set of elements of a type with an additional constructor
is a well known technique and is usually done through something in
the lines of a \emph{free monad}. The \genericssimpl{} library provides
exactly what we need: the |HolesAnn kappa fam phi h| datatype 
from \Cref{sec:gp:simplistic:holes}, which is a free monad in |h|. 
Recall its definition below, presented without annotations, that is, |phi = V1|, 
fostering readability here:

\begin{myhs}
\begin{code}
data Holes kappa fam h a where
  Hole  :: h a -> Holes kappa fam h a
  Prim  :: (PrimCnstr kappa fam a)
        => a -> Holes kappa fam h a
  Roll  :: (CompoundCnstr kappa fam a)
        => SRep (Holes kappa fam h) (Rep a)
        -> Holes kappa fam h a
\end{code}
\end{myhs}

  At first, one would think of simply passing |Const Int| in place of |h|,
as in |Holes ki codes (Const Int)|. This gives a functor mapping an
element of the family into its representation, augmented with integers,
representing metavariables. Which is almost good enough, if not for
not being able to infer whether a metavariable matches over
an opaque type or a recursive position, which is crucial if we
are to produce good alignments later on \Cref{sec:pepatches:alignment}.
Consequently, we must keep the opaque values around in order to be 
able to compare their type-level indicies.

\begin{myhs}
\begin{code}
data MetaVar kappa fam at where
  MV_Prim  :: (PrimCnstr kappa fam at)
           => Int -> MetaVar kappa fam at
  MV_Comp  :: (CompoundCnstr kappa fam at)
           => Int -> MetaVar kappa fam at
\end{code}
\end{myhs}

  With |MetaVar| as defined above, we can always fetch the |Int| identifying
the metavar but we posses all the type-level information that we will need
to inspect at run-time later. In fact, it is handy to define the |HolesMV| synonym
for values augmented with metavariables, below.

\begin{myhs}
\begin{code}
type HolesMV kappa fam = Holes kappa fam (MetaVar kappa fam)
\end{code}
\end{myhs}

  So far we have seen the machinery necessary to define \emph{changes},
which consist in a pair of a deletion context and an insertion context for the same type. 
As expected, these contexts are values of the mutually recursive family in question augmented
with metavariables.

\begin{myhs}
\begin{code}
data Chg kappa fam at = Chg
  {  chgDel  :: HolesMV kappa fam at
  ,  chgIns  :: HolesMV kappa fam at
  }
\end{code}
\end{myhs}

  Ideally, however, we would like changes to \emph{not} contain 
redundant information. For example, take the change illustrated in
\Cref{fig:pepatches:example-02:chg}: it inserts the |Bin 84| constructor
at the right child of the root -- but the |Bin| at the root and its
left child, |42|, are duplicated in the deletion and insertion context.
In \Cref{fig:pepatches:example-02:patch}, on the other hand, we see that this
redundant information has been undistributed, making it clear they are 
copied from the source to the destination.

\begin{figure}
\centering
\subfloat[Insertion as a \emph{redundant change}]{%
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [x,metavar]]
  [|Bin| [|42|] [|Bin| [|84|] [x,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-02:chg}}%
\quad\quad\quad
\subfloat[Insertion as a \emph{patch}]{%
\begin{forest}
[|Bin|,s sep = 5mm%make it wider
  [|42|]
  [,change [x,metavar] [|Bin| [|84|] [x,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-02:patch}}%
\caption{A change on the left and its minimal representation on
the right}
\label{fig:pepatches:example-02}
\end{figure}

  The process of extracting and evidentiating the common constructors
in a |Chg|s deletion and insertion context is, in its simplest form,
plain \emph{anti-unification}~\cite{Plotkin1971}. We denote it
by the longest common (tree) prefix of two terms and its definition
is straight forward and is given in \Cref{fig:pepatches:antiunif}.

\begin{figure}
\begin{myhs}
\begin{code}
lcp  :: (All Eq kappa)
     => Holes kappa fam phi at
     -> Holes kappa fam psi at
     -> Holes kappa fam (Holes kappa fam phi :*: Holes kappa fam psi) at
lcp (Prim x) (Prim y) = 
  case witness :: Witness Eq at of -- retrieve correct Eq instance
    Witness ->  if x == y then Prim x else (Prim x :*: Prim y)
lcp x@(Roll rx) y@(Roll ry) = 
  case zipSRep rx ry of
    Nothing  -> Hole (x :*: y)
    Just r   -> Roll (repMap (uncurry' lcp) r)
lcp x y = Hole (x :*: y)
\end{code}
\end{myhs}
\label{fig:pepatches:antiunif}
\caption{Classic anti-unification algorithm~\cite{Plotkin1971}, 
producing the least general generalization of two trees}
\end{figure}

   

\victor{Justify why do I care about scoping... I mean; we could just don't care,
but it helps in isolating changes and making sure they are independent;}
\victor{Would it be interesting to compare the performance of alignment
with and without scoping?}

\victor{decide... is |vars del == vars ins| or |vars ins < vars del|}?

  However, as is usual around calculi involving names and binding, we
are bound to have issues if are not careful. Therefore, we impose the
invariant that changes are \emph{well-scoped}, that is, |vars (chgDel
c) == vars (chgIns c)|.  The |vars| function below the set of
metavariables used in a |HolesMV| together with their arity, \ie, how
many times do they occur. This ensures that all the variables needed to
fully instantiate the insertion context of a change are provided
by the deletion context of the same change.

\begin{myhs}
\begin{code}
vars :: HolesMV kappa fam at -> Map Int Arity
\end{code}
\end{myhs}

  A \emph{patch} is in fact defined as a member of the mutually
recursive family augmented with \emph{non-redundant changes}, or, to put
it in another way, it contains a spine that is copied from
source to destination and has changes in its leaves:

\begin{myhs}
\begin{code}
type PatchPE kapa fam = Holes kappa fam (Chg kappa fam)
\end{code}
\end{myhs}

  Converting from patch back into a potentially redundant change
is very easy. The free monad structure of |Holes| gives us
the monadic multiplication trivially, yielding:

\begin{myhs}
\begin{code}
patch2change :: PatchPE ki codes at -> Chg ki codes at
patch2change p = Chg  (holesJoin (holesMap chgDel  p))
                      (holesJoin (holesMap chgIns  p))
\end{code}
\end{myhs}

  The other way around is not so simple since we must ensure
that changes remain \emph{well-scoped}. For example, 
performing a simple antiunification of the deletion
context against the insertion context might break 
variable scoping.

\begin{figure}
\centering
\subfloat[\emph{well-scoped} swap]{%
\begin{forest}
[,rootchange 
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]
]
\end{forest}
\label{fig:pepatches:example-03:A}}%
\quad\quad\quad
\subfloat[\emph{non-well-scoped} swap]{%
\begin{forest}
[|Bin|,s sep = 5mm%make it wider
  [,change [x,metavar] [y,metavar]]
  [,change [y,metavar] [x,metavar]]
]
\end{forest}
\label{fig:pepatches:example-03:B}}%
\caption{How antiunification of the deletion and insertion context of
a change might break scoping.}
\label{fig:pepatches:example-03}
\end{figure}

\subsection*{Computing Closures}

\subsection*{Aligning Closed Changes}
\label{sec:pepatches:alignments}
 
\victor{\huge I'm here!}


Take for example the
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


  This yields a formal definition of \emph{changes} over elements
of a term algebra.

\newcommand{\termalg}{\ensuremath{\Gamma}}
\newcommand{\varset}{\ensuremath{\mathcal{V}}}
\begin{definition}[Change]
A change consists in an element of \termalg ...
is a term algebra augmented with variables taken from a countable set \varset. We denote the first and
second projections by \emph{deletion} and \emph{insertion} contexts, respectively.
\end{definition}



\victor{
The |PatchPE ki codes| forms either:
\begin{itemize}
\item Partial monoid, if we want |vars ins <= vars del|
\item Grupoid, if we take |vars ins == vars del|
\end{itemize}
}
\section{Merging Patches}

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
