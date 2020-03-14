
\victor{I'm inclined in borrowing a \texttt{\\digress} env
like in Mandelbrot's ``Fractal Geom. of Nature''; where I write
in the first person about my experience doing things; could
be a good way to add bits like the following:
\digress{This hdiff approach as born from ...}}

  The \texttt{stdiff} approach gave us a first representation of
tree-sructured patches over tree-structured data but was still ddeply
connected to edit scripts: subtrees could only be copied once and
could not be permuted. This means we still suffered from ambiguous
patches, and, consequently, a coputationally expensive |diff|
algorithm. Overcoming the drawback of ambiguity requires a shift in
perspective and a thorough decoupling from edit-script based
differencing algorithms. In this section we will explore the the
\texttt{hdiff} approach, where patches allow for trees to be
arbitrarily permuted, duplicated or contracted -- contractions are
dual to duplications.

  Classical tree differencing algorithms start by computing a tree
matchings (\Cref{sec:background:tree-edit-distnace}), which identify
which subtrees should be copied. These tree matchings, however, must
be restricted to order-preserving partial injections in order to be
efficiently translated to edit-scripts later on.  The \texttt{hdiff}
approach never translates to edit-scripts, which means the tree
matchings we compute are subject to \emph{no} restrictions.  In fact,
\texttt{hdiff} uses these unrestricted tree matchings as \emph{the}
patch, instead of translating them \emph{into the}
patch. Consequently, we do not need any of the classical restrictions
imposed on tree matchings.

  Suppose we want to write a change that modifies the left element
of a binary tree. If we had the full Haskell programming language available
as the patch language, we could write something in the lines of:

\begin{myhs}
\begin{code}
p :: Tree -> Maybe Tree
p (Bin (Leaf x) y) 
  | x == 10    = Just (Bin (Leaf 42) y)
  | otherwise  = Nothing
p _            = Nothing
\end{code}
\end{myhs}

  Observing the function |p|, above, we see it has a clear domain -- a
set of |Tree|s that when applied to |p| yields a |Just| -- which is
specified by the pattern and guards. Then, for each tree in the doman
we assign a different tree in the codomain.  The new tree is obtained
from the old tree by replacing the |10| by |42| inplace.  Taking a
magnifying glass at that definition, we can interpret the matching of
the pattern as a \emph{deletion} phase and the construction of the
resulting tree as a \emph{insertion} phase.  The \texttt{hdiff}
approach represents the change in |p| exactly as that: a pattern and a
expression. Essentially, we write |p| as |patch (Bin (Leaf 10) y) (Bin
(Leaf 42) y)| -- represented graphically as in
\Cref{fig:pepatches:example-01}. An important aspect here is that the
graphical notation makes it evident which constructors were copied
until we reach the point where a change must be made. The notation
$\digemFormatMetavar{\square}$ is used to indicate $\square$ is a
metavariable, that is, given a successful matching of the deletion
context against an element, $\digemFormatMetavar{\square}$ will be
given a value.

\begin{figure}
\centering
\begin{myforest}
[|Bin| 
  [|Leaf| [,change [|10|] [|42|]]]
  [,change [y,metavar] [y,metavar]]
]
\end{myforest}
\caption{Graphical represntation of a patch that modifies the left
children of a binary node}
\label{fig:pepatches:example-01}
\end{figure}

  With the added expressivity of refering to subtrees
with metavariables we can represent more transformations
than before. Take, for example, the patch that swaps two subtrees, which cannot
even be written using an edit-script based approach, here it is
given by |patch (Bin x y) (Bin y x)|. Another helpful consequence of
our design is that we effectively bypass the \emph{choice} phase of the
algorithm. When computing the differences between |Bin Leaf Leaf|
and |Leaf|, for example, we do not have to chose one |Leaf| to copy
because we can copy both with the help of a contraction operation,  
with a patch such as: |patch (Bin x x) x|. This aspect is crucial
and enables us to write a linear |diff| algorithm.

  In this chapter we explore the representation and computation
aspects of \texttt{hdiff}.  The big shift in paradigm of
\texttt{hdiff} also requires a more careful look into the metatheory
and nuances of the algorithm, which were not present in said
paper. \digress{We first wrote our algorithm~\cite{Miraldo2019} using
the \texttt{generics-mrsop} library even though \texttt{hdiff} does
not require an explicit sums of products. This means we can port it to
\genericssimpl{} and gather real world data fort his approach. We
present our code in this section on the \genericssimpl{} library.}
The mateiral in this chapter is a refinement from our ICFP'19
publication~\cite{Miraldo2019}.

\victor{Maybe we write another paper with Pierre about it?}

\section{The Type of Patches}

  The type |PatchPE x| encapsulates the transformations we wish to
support over elements of type |x|. A value of type |PatchPE| consists in a
\emph{pattern}, or deletion context, which instantiates a number of
metavariables when matched against an actual value; and a
\emph{expression}, or insertion context, which uses the instantiation
provided by the deletion context to substitute its variables, yielding
the final result. Both insertion and deletion contexts are 
inhabitants of the type |x| augmented with \emph{metavariables}.

  Augmenting the set of elements of a type with an additional constructor
is usually done with a \emph{free monad}, which is provided by the
\genericssimpl{} library. The |HolesAnn kappa fam phi h| datatype 
(\Cref{sec:gp:simplistic:holes}) is a free monad in |h|. 
We recall its definition ignoring annotatios below.

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

  In a first iteration, we could think of passing |Const Int| in
place of |h|, as in |Holes ki codes (Const Int)|.  This gives a
functor mapping an element of the family into its representation
augmented with integers, used to represent metavariables. This does
not yet enable us to infer whether a metavariable matches over an
opaque type or a recursive position, which will come to be important
soon enough (when producing alignments,
\Cref{sec:pepatches:alignment}). Consequently, we will keep the
information about whether the metavariable matches over an opaque
value or not:

\begin{myhs}
\begin{code}
data MetaVar kappa fam at where
  MV_Prim  :: (PrimCnstr kappa fam at)
           => Int -> MetaVar kappa fam at
  MV_Comp  :: (CompoundCnstr kappa fam at)
           => Int -> MetaVar kappa fam at
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

  A \emph{change} is our \emph{unit of transformation}. Patches
will later be defined in terms of changes. A change, then,
consists in a pair of a deletion context and an
insertion context for the same type.  These contexts are
values of the mutually recursive family in question augmented with
metavariables:

\begin{myhs}
\begin{code}
data Chg kappa fam at = Chg
  {  chgDel  :: HolesMV kappa fam at
  ,  chgIns  :: HolesMV kappa fam at
  }
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
c| we would like to guarantee that every metavariabl in |chgIns c|
gets substituted, yielding a term with no holes as a result.
Consequently we expect a value of type |Chg| to be well-scoped, that
is, all the variables that are present in the insertion context must
also occur on the deletion context, or, in Haskell:

\begin{myhs}
\begin{code}
vars        :: HolesMV kappa fam at -> Map Int Arity

wellscoped  :: Chg kappa fam at -> Bool
wellscoped (Chg d i) = keys (vars i) == keys (vars d) 
\end{code}
\victor{decide... is |vars del == vars ins| or |vars ins < vars del|}?
\end{myhs}

  Attempting to apply a non-well-scoped change is a violation of
the contract of |applyChg|. We \texttt{error} out on that situation
and distinguish it from a change |c| not being able to be applied to |x|
because |x| is not an element of the domain of |c|.

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

%%   \digress{There are many ways of representing a |Chg|,
%% in fact, a good part of my research was in understaning
%% the trade-offs between different representations for changes. 
%% I have settled for extracting the constructors that appear 
%% repeated in the deletion and insertion context into a \emph{spine} and 
%% minimizing changes, which later on will be \emph{aligned} to uncover
%% insertions and deletions within the recursive structure.
%% The design decisions I made have been driven by the synchronizatino algorithm.
%% The \emph{spines} help us understand which constructors have been
%% copied even though they might lead to a change further down the tree,
%% whereas the \emph{alignments} enable us to understand which parts
%% of the tree consist entirely of \emph{new information} and can
%% be skipped by the synchronizer. Next we look into these
%% options in more detail.}

  A change, |Chg|, is very similar to a \emph{tree matching} 
(\Cref{sec:background:tree-edit-distance}) with less restrictions.
In other words, it arbitrarily maps subtrees from the source
to the destination. From an algebraic point of view, this already
gives us a desirable structure, as we will explore, in \Cref{sec:pepatches:meta-theory}. 
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
\caption{Misaligned metavariables due to deletinos
in the head of linearly-structured data. This is hard to reconcile.}
\label{fig:pepatches:misalignment}
\end{figure}

  Independently of global or local scoppning,
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
metatheoretical definitions and proofs we will abide by Barendregts
Convention~\cite{Barendregt1984} where no two bound variables are
identified with the same name.  \digress{I wonder how an
implementation using De Bruijn indexes would look like. I'm not
immediatly sure it would be easier to enforce correct indexes. Through
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
\caption{Some non-minimal and one miminal change.}
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
changes well scoped. \Cref{fig:pepatches:example-minimal} illustrates 
some cases. 
%}

  Defining whether a change is closed or not has its nuances. Firstly,
we can only know that a change is in fact closed if we know, at least,
how many times each variable is used globally.  Say a variable |x| is
used |n + m| times in total, and it has |n| and |m| occurences in the
deletion and insertion contexts of |c|, then |x| is not used anythwere
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
receveies a spine with leaves of type |WithVars dots|
and attemps to \emph{enlarge} them as necessary.  
If it is not possible to close the current spine, we
return a |InL dots| equivalent to pusing all the
constructors of the spine down the deletion and insertion contexts.  
The main component behing |closeAux| is |chgVarsDistr|, which distributes 
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
produce an \emph{aligment} of the minimal changes produced by |close|.

\subsection{Aligning Patches}
\label{sec:pepatches:alignments}

  An aligned patch consists in a spine of copied constructors
leading to a \emph{well-scoped aligment}. This alignment, in turn,
consists in a sequence of insertions, deletions or spines,
which finally lead to a |Chg|. This is not so different from
\texttt{stdiff}s' |Almu|, presented in \Cref{sec:stdiff:diff:fixpoint}.
In adition to simple insertions, deletions and spines we also
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
[|Bin|, s sep=4mm
  [,change
    [|Bin| [x,metavar] [y,metavar]]
    [|Bin| [y,metavar] [x,metavar]]]
  [,change
    [z,metavar]
    [|Bin| [|Leaf| [|42|]] [z,metavar]]]]
\end{myforest}}%
\qquad
\subfloat[Result of |align p|]{%
\begin{myforest}
[|Bin| , s sep=12mm
 [|Bin| , alignment
   [|Prm (metavar x) (metavar y)|]
   [|Prm (metavar y) (metavar x)|]]
 [,insctx
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
[, delctx , alignment
  [|(:)| [|42|] [SQ]]
  [|(:)|, s sep=4mm 
      [|Cpy (metavar x)|]
      [|(:)| [|Cpy (metavar y)|] [|Cpy (metavar z)|]]
%     [,change [x,metavar] [x,metavar]]
%     [|(:)|, s sep=4mm
%       [,change [y,metavar] [y,metavar]]
%       [,change [z,metavar] [z,metavar]]]
  ]
]
\end{myforest}
\label{fig:pepatches:alignment-01:B}}%
\caption{Properly aligned version of \Cref{fig:pepatches:misaligment}.}
\label{fig:pepatches:alignment-01}
\end{figure}

  Since our patches are locally scoped, computing an aligned patch
is simply done by maping over the spine and aligning the individual changes.
Computing the \emph{aligment} for a change |c| consists in 
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
we would end up having to work with a patch that is unecessarily
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
are smipler to synchronize than arbitrary changes.  A copy is
witnessed by a change |c = Chg (metavar x) (metavar x)| such that
|metavar x| only occurs twice globally. This means all occurences of
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

  Equipped with a definition for aligments, we move on to defining
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
We ommit the full implementation of |hasRigidZipper| here but invite 
the interested reader to check the source code.\victor{where?}

  Finally, we are ready to define |alignChg| in its entirety.  We
start computing the multiset of variables used througout a patch,
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
betweem alignments and changes. The |disalign| function is plugs
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
opaque values that appear on the alignment's spine. The auxiliar
function |align'| returns the sucessor of the last issued name to
ensure we can easily produce fresh names later on, if need be.
Note that |align| introduces information, namelly, new metavariables
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

  On this setion we will look into how |Chg| admits a simple
composition operation and forms a partial monoid or
a partial grupoid depending on whether we allow metavariables to
be left unused or not. We shall be ignoring the \emph{change-versus-patch}
distinction and working solely with \emph{changes} in this section.
We can always recompute a patch from a change if we wish to do so and,
for metatheoretical concerns, the distinction is artificial nevertheless
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
oportunities. Imagine that |p| inserts a subtree |t| that was
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
of this sextion we will abuse notation and write |sigma x|
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
Becase |x| has no variables, |gamma x == x|.
Hence, |gamma| witnesses the unification of |sigma (ctxDel q)|
and |x|. Hence, |app (after p q) x == gamma (sigma (ctxIns p))|
Finally, a straightforward calculation yeilds that
|gamma (sigma (ctxIns p)) == y|.
\end{enumerate}
\end{description}
\end{proof}

  Once we have estabilished that composition is correct
with respect to application, we would like to ensure
composition is associative. But first, it is handy to
consider an extensional equality over changes. Two
changes are sait to be equal if and only if they are 
undistinguishable through their application semantics:

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

  \Cref{lemma:pepatches:comp-assoc,lemma:pepatches:comp-id} estabilish
a partial monoid structure for |Chg| and |after| under extensional
change equality, |~|. This further strenghtens the applicability
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

\section{Merging Aligned Patches}
\label{sec:pepatches:merging}

  In the previous sections we have seen how |Chg|
can be used as \emph{the} representation of a transformation
between two trees. We have also seen how we can
extract a \emph{spine}, which indicates a prefix of constructors
copied from the source to the destination and leads
to changes, which in turn are \emph{aligned} to reveal
entire insertions and deletions, copies and permutations.
In this section we will be defining our synchronization
algorithm, which uses this extra information to better
merge our patches.

  Recall our patches consist in a spine, which leads to
locally-scoped alignments. These alignments in turn also
have a spine which ultimately leads to modifications. The distinction
between the \emph{outer} spine and the spine inside the
alignments is the scope. Consequently, we can map over
the outer spine without needing to remember information
accross calls but we \emph{must} remember information 
inside the scope of an aligment. Take the example in
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
  [|Bin| , alignment
    [|Prm (metavar y) (metavar z)|]
    [|Prm (metavar z) (metavar y)|]]
]
\end{myforest}}\qquad%
\subfloat[Patch |q|]{%
\begin{myforest}
[|Bin| , s sep=7mm
  [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]]
  [,insctx
    [|Bin| [|Leaf| [|84|]] [SQ]]
    [Cpy]]]
\end{myforest}}

\subfloat[Result of |diff3 p q|]{%
\begin{myforest}
[|Bin| , s sep=10mm
  [,change
    [|Bin| [|Leaf| [|42|]] [|Leaf| [|42|]]]
    [|Leaf| [|42|]]]
  [,insctx
    [|Bin| [|Leaf| [|84|]] [SQ]]
    [|Bin| , alignment
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
synchronizatino is possible and results in \Cref{fig:pepatches:merge-01:C}.

\begin{figure}
\centering
\subfloat[Patch |p|]{%
\begin{myforest}
[|Bin|
  [|Leaf| [,change [|42|] [|84|]]]
  [Cpy]]
\end{myforest}
\label{fig:pepatches:merge-01:A}}%
\qquad%
\subfloat[Change |q|]{%
\begin{myforest}
[|Bin|
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

  Given then two aligned patches, the |diff3 p q| function below
will map over the common prefix of the spines
of |p| and |q|, captured by their least-general-generalization and
produce a patch with might contain conflicts inside.
\digress{In the actual implementation we receive two patches
and align them inside |diff3|, this helps ensuring they will
have a disjoint set of names.}

\victor{Why don't we return |Maybe PatchC|? the |maybe| would
indicate whether or not the arguments form a span}

\begin{myhs}
\begin{code}
diff3  :: PatchAl kappa fam at -> PatchAl kappa fam at -> PatchC kappa fam at
diff3 oa ob = holesMap (uncurry' go) (lgg oa ab)
  where
    go  :: Holes kappa fam (Al kappa fam) at -> Holes kappa fam (Al kappa fam) at
        -> Sum (Conflict kappa fam) (Chg kappa fam) at
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
first record how each subtree was modified and then instante these
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
[|(:)| , alignment
  [|Prm (metavar x) (metavar y)|] 
    [|(:)| [|Prm (metavar y) (metavar x)|] 
      [|[]|]
    ]
]
\end{myforest}}
\qquad\qquad%
\subfloat[|align (diff o b)|]{%
\begin{myforest}
[|(:)| , alignment
  [Cpy]
  [,insctx
    [|(:)| [|42|] [SQ]]
    [Cpy]]]
\end{myforest}}

\subfloat[Result of merge |diff3 oa ob|]{%
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
in |iota| in an important way. The entries |(v , p)| in |iota|
represent a decision made by the merging algorithm: the subtree
located at |v| must be modified acording to patch |p| -- which
means that at the end of the process, there will be no occurences of |v| left. 
The equivalences, on the other hand, represent observations made
by the merging algorithm, that is, an entry |(v , t)| represents
an observation that the subtree at |v| is, in fact, equal to |t|.
These facts may or may not be used later on. For example, if we
already made a decision about how to instantiate |v|, whether or not
it must be equal to |t| is irrelevant -- all occurences of |v| will
disappear. \victor{is it really irrelevant? what if we decide that
|v| was something incompatible with |t|?}

  Conflicts will be handled through the |Except| monad.
Upon finding conflicts, we will simply call |throwError| with a label
that describes the conflict. The |mergeAl| function, then, is
just a wrapper around |mergeAlM|, which is defined in terms of 
the |MergeM| monad for convenience.

\begin{myhs}
\begin{code}
type MergeM kappa fam = StateT (MergeState kappa fam) (Except String)

mergeAl  :: Aligned kappa fam x -> Aligned kappa fam x
         -> Sum (Conflict kappa fam) (Chg kappa fam) x
mergeAl x y = case runExcept (evalStateT (mergeAlM p q) mrgStEmpty) of
                Left err  -> InL (Conflict err p q)
                Right r   -> InR (disalign r)
\end{code}
\end{myhs}

  Finally, the |mergeAlM| function maps over both alignments that
we wish to merge and collects all the constraints and observations.
It then attempts to splits these constraints and observations into 
two maps: (A) a deletion map that contains information
about what a subtree identified by a metariable \emph{was}; and
(B) an insertion map that idenfities what said metavariable \emph{became}.
If it is possible to produce these two idempotent substitutions,
it then makes a second pass computing the final result. 

\begin{myhs}
\begin{code}
mergeAlM  :: Al kappa fam at -> Al kappa fam at 
          -> MergeM kappa fam (Al kappa fam at)
mergeAlM p q = do
  phase1  <- mergePhase1 p q
  info    <- get
  case splitDelInsMap info of
    Left   _   -> throwError "failed-contr"
    Right  di  -> alignedMapM (phase2 di) phase1
\end{code}
\end{myhs}

  The first pass is computed by the |mrgPhase1| function, which will
populate the state with instantiations and equivalences and place
values of type |Phase2| inplace in the alignment. These values instruct
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
  P2Instantiate   :: Chg kappa fam at
                  -> Maybe (HolesMV kappa fam at)
                  -> Phase2 kappa fam at
  P2TestEq        :: Chg kappa fam at
                  -> Chg kappa fam at
                  -> Phase2 kappa fam at
\end{code}
\end{myhs}

  Deciding which instruction should be perfored depends on the
structure of the alignments under synchronization.  Copies are the
identity element. The |mergePhase1| function is shown in its entirety
in \Cref{fig:pepathes:mergePhase1} but discussed in detail below.
It follows similar reasoning from the merge algorithm for \texttt{stdiff} 
(\Cref{sec:stdiff:merge}). In fact, the |Al| datatype resembles the
|Almu| -- both have insertions, deletinos and spines but the former
The |mergePhase1| function proceeds by induction on its arguments.

\begin{myhs}
\begin{code}
mergePhase1  :: Al kappa fam x -> Al kappa fam x
             -> MergeM kappa fam (Al' kappa fam (Phase2 kappa fam) x)
mergePhase1 p q = case (p , q) of dots
\end{code}
\end{myhs}

  The first cases we have to handle are copies, which should de 
the identity of synchronization. That is, if |p| is a copy, 
all we need to do is modify the tree according to |q| at the
current location. We might need to refine |q| according to
other constraints we discovered in other parts of the alignment
in question, so the final instructon is to \emph{instantiate}
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
tree versus the case wher one patch permutes the tree but
the other changes its contents.

\begin{myhs}
\begin{code}
   (Prm x y, Prm x' y')  -> Mod <$$> mrgPrmPrm x y x' y'
   (Prm x y, _)          -> Mod <$$> mrgPrm x y (disalign q)
   (_, Prm x y)          -> Mod <$$> mrgPrm x y (disalign p)
\end{code}
\end{myhs}

  If we are to merge two permutations, |Prm (metavar x) (metavar y)|
against |Prm (metavar x') (metavar y')|, for example, we know that
|metavar x| and |metavar x'| must refer to the same subtree, hence we
register their equivalence. But since the two changes permuted the
same tree, we can only synchronize them if they were permuted to the
\emph{same place}, in other words, if both permutations turn out to be
equal at the end of the process. 

\begin{myhs}
\begin{code}
mrgPrmPrm  :: MetaVar kappa fam x -> MetaVar kappa fam x 
           -> MetaVar kappa fam x -> MetaVar kappa fam x
           -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrmPrm x y x' y'  =   onEqvs (\eqs -> substInsert eqs x (Hole x'))
                     >>  return (P2TestEq (Chg (Hole x) (Hole y)) (Chg (Hole x') (Hole y')))
\end{code}
\end{myhs}

  If we are merging one permutation with something other
than a permutation, however, we know one change modified the location
of a tree, whereas another potentially modified its contents. 
All we must do is record that the tree identified
by |metavar x| was modified according to |c|. After we have made one
entire pass over the alignments being merged, we must instantiate
the permutation with the information we discovered -- the |metavar x|
occurence in the deletion context of the permutation will be |chgDel c|,
potentially simplified or refined. The |metavar y| appearing in
the insertion context of the permutation will be instantiated
with whatever we come to discover about it later. We know there \emph{must}
be a single occurence of |metavar y| in a deletion context because
the alignment flagged it as a permutation.

\begin{myhs}
\begin{code}
mrgPrm  :: MetaVar kappa fam x -> MetaVar kappa fam x
        -> Chg kappa fam x
        -> MergeM kappa fam (Phase2 kappa fam x)
mrgPrm x y c  =   addToIota "prm-chg" x c
              >>  return (P2Instantiate (Chg (Hole x) (Hole y)) Nothing)
\end{code}
\end{myhs}

  The |addToIota| function inserts the |(x, c)| entry in |iota| if |x|
is not yet a member. It throws an error with the supplied label
if |x| is already in |iota| with a value that is different than |c|.
\digress{I believe that we could develop a better algorithm if instead
of forbidding values different than |c| we check to see whether the
two different values can also be merged. I ran into many difficulties
tracking how subtrees were moved and opted for the easy and pragmatic
option of not doing anything difficult here.}

  Insertions must be preserved as long as they do not attempt to
insert different information in the same location.

\begin{myhs}
\begin{code}
   (Ins (Zipper z p'), Ins (Zipper z' q'))
     | z == z'             -> Ins . Zipper z <$$> mergePhase1 p' q'
     | otherwise           -> throwError "ins-ins"
   (Ins (Zipper z p'), _)  -> Ins . Zipper z <$$> mrgPhase1 p' q
   (_ ,Ins (Zipper z q'))  -> Ins . Zipper z <$$> mrgPhase1 p q'
\end{code}
\end{myhs}

  Next we look at deletions. If one patch
deletes a constructor but the other modifies the fields the
constructor, we must ensure that none of the deleted fields
have been modified by the other patch. This is done by the |tryDel|
function, which attempts to delete a zipper from an alignment, and,
if successful, returns the pair of alignments we should continue
to merge.  

\victor{Mention we dont need to swap; this is symmetruic! :)}

\begin{myhs}
\begin{code}
   (Del zp@(Zipper z _), _)  -> Del . Zipper z <$$> (tryDel zp q >>= uncurry mrgPhase1)
   (_, Del zq@(Zipper z _))  -> Del . Zipper z <$$> (tryDel zq p >>= uncurry mrgPhase1)
\end{code}
\end{myhs}

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
  | otherwise  = throwError "del-del"
tryDel (Zipper z h) (Spn rep) = case zipperRepZip z rep of
    Nothing  -> throwError "del-spn"
    Just r   -> let hs = repLeavesList r
                 in case partition (exElim isInR1) hs of
                      ([Exists (InL Refl :*: x)] , xs)
                        | all isCpyL1 xs  -> return (h , x)
                        | otherwise       -> throwError "del-spn"
                      _                   -> throwError "del-spn"
tryDel (Zipper _ _) _ = throwError "del-mod"
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
a |P2Instantiate| instruction for change, being careful that
the variables that show up in the result, after the second phase is done,
do not mention any variable mentioned by the insertion contexts
in the spine.

\begin{myhs}
\begin{code}
   mrgChgSpn  :: (CompoundCnstr kappa fam x) => Chg kappa fam x -> SRep (Al kappa fam) (Rep x)
              -> MergeM kappa fam (Phase2 kappa fam x)
   mrgChgSpn p@(Chg dp _) spn = do
     instM dp (Spn spn) 
     return (P2Instantiate p (Just (chgIns (disalign (Spn spn)))))
\end{code}
\end{myhs}

  \Cref{fig:pepatches:merge-03} illustrates a case where failing to check
this would result in an erroneous duplication of the value |2|. 

  Matching the deletion context of |chg = Chg (metavar c) (: (metavar
a) (metavar c))| against the spine |spn = Spn (: Cpy (Chg (metavar z)
(: (metavar x) (metavar z))))| will yield |c| equal to |spn|, which
means the subtree identified by |c| was modified according to |spn|,
which is correct. The observation, however, is that the insertion
context of |chg| mentions |metavar a|, which is a subtree that comes
from somwhere else other than the deletion context of |chg|. If we
naively substitute |metavar c| in |ctxDel chg| by |ctxDel (disalign spn)|
and in |ctxIns chg| by |ctxIns (disalign spn)|, we would get:

\begin{minipage}{.8\textwidth}
\centering
\begin{myforest}
[,change
  [|(:)| [l,metavar] [z,metavar]]
  [|(:)| [a,metavar]
    [|(:)| [l,metavar] [|(:)| [x,metavar] [z,metavar]]]]]
\end{myforest}
\end{minipage}

  Since we know |metavar x == metavar a|, which was registered when
merging the left hand side of |(,)|, in
\Cref{fig:pepatches:merge-03:A,fig:pepatches:merge-03:B}, we have
that |metavar a| was duplicated. Our implementation will reject this
since it performs the check that the subtrees that appear in the
result of instantiating |chg| are separate from those
that were moved around by |spn|. \digress{I dislike this aspect of
this synchronization algorithm quite a lot, it feels unecessarily complex and with
no good justification. There must be a more disciplined way of
disallowing duplications to be introduced without this but I could
not figure it out.}

\begin{figure}
\begin{minipage}{.65\textwidth}
\centering
\subfloat[Aligned Patch |p|]{%
\begin{myforest}
[|(,)| , s sep=4mm 
  [|(:)| [|Cpy|] [,change [|(:)| [a,metavar] [b,metavar]] [b,metavar]]]
  [,change [c,metavar] [|(:)| [a,metavar] [c,metavar]]]]
\end{myforest}\label{fig:pepatches:merge-03:A}}\qquad
\subfloat[Aligned Patch |q|]{%
\begin{myforest}
[|(,)| , s sep=4mm 
  [|(:)| [|Cpy|] [,change [|(:)| [x,metavar] [y,metavar]] [y,metavar]]]
  [|(:)| [|Cpy|] [,change [z,metavar] [|(:)| [x,metavar] [z,metavar]]]]]
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

  
\victor{Obviously they must be spines over the same constructor; unless
the patchs don't make a span.}

  Merging two spines is simple. We must ensure they are spines over
the same constructor and recurse on the fields of the spine pointwise:

\begin{myhs}
\begin{code}
   (Spn p', Spn q') -> case zipSRep p' q' of
       Nothing -> throwError "spn-spn"
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
mrgChgDup  :: Chg kappa fam x -> Chg kappa fam x
           -> MergeM kappa fam (Phase2 kappa fam x)
mrgChgDup dup@(Chg (Hole v) _) q' = do
  addToIota "chg-dup" v q' 
  return (P2Instantiate dup Nothing)
\end{code}
\end{myhs}

  If they are not duplications, nor none of the cases prevously
handled by |mergePhase1|, then the best we can do is register 
equivalence of their domains -- recall both patches being merged must
form a span -- and synchronize successfully when both changes are
equal.

\begin{myhs}
\begin{code}
mrgChgChg :: Chg kappa fam x -> Chg kappa fam x
          -> MergeM kappa fam (Phase2 kappa fam x)
-- Changes must have unifiable domains
mrgChgChg p' q'
  | isDup p'   = mrgChgDup p' q'
  | isDup q'   = mrgChgDup q' p'
  | otherwise  = case unify (chgDel p') (chgDel q') of
       Left  _   -> throwError "chg-unif"
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
     | otherwise -> throwError "ins-ins"
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
       Nothing -> throwError "spn-spn"
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
|metavar 0| was duplicated somwhere else, and we come accross
an equivalence that says |metavar 1 == metavar 0|. We cannot simply insert
this into |iota| because the merge algorithm made the decision to
remove all occurences of |metavar 0|, not of |metavar 1|, even
though they identify the same subtree. This is important to ensure
we produce patches that can be applied. 

  The |splitDelInsMaps| function is responsible for synthesizing the
information gathered in the first pass of the synchronization
algorithm. Splitting |iota| is easy, we just use the deletion and
insertion context of the changes that overlaped a given
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
           xs  -> throwError ("mov-mov " ++ show xs)
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

\section{Computing Changes}
\label{sec:pepatches:diff}

  In the previous sections we have seen how |Chg| and its cousins,
|Patch| and |PatchAl| make for an reasonable theoretical ground for
structural differencing. They posses a grupoid structure with respect
to composition and can be synchronized. The last aspect, which lifts
\texttt{hdiff} from a theoretical approach into a practical form of
structural differencing is the computation of a |Patch|, or, the
|diff| function. Computing changes relies almost exclusively on being
able to tell whether or not a given subtree could be shared. We do so
by querying a \emph{sharing map}, which is constructed in a first pass
of the algorithm.

  In the domain of diffrencing programming languages, one must 
be careful to not \emph{overshare} trees. That is, a local variable
declaration \verb!int x = 0;! in an arbitrary function should not
be shared with a syntatically equal declaration in another function.
A careful analisys of what can and cannot be shared would require
domain-specific knowledge of the programming language in question --
which we did not have time to pursue, unfortunately. 
Nevertheless, we can impose different restrictions that make
it \emph{unlikely} that values will be shared accross scope boundaries.
A simple and effective such measure is not sharing subtrees with
height strictly less than some configurable parameter, this keeps 
constants and most variable declarations completely un-shareable.   
In fact, we will be implementing this very sharing restriction
but will come back to this point in the Discussion (\Cref{sec:pepatches:discussion}). 

  This section explores the definition of the \emph{sharing map} and
how to compute a |Chg| given such sharing map.
For now, lets just assume the existence of said sharing map,
noting that it is trivial to define an inefficient variant of such map 
 -- a subtree |t| can be shared if and only if we can 
find |t| in the source, |s|, and in the destination, |d|, trees.

  Given two trees, |s| and |d|, we want to produce a change |c| such
that |chgApply c s == Just d|. The obvious option is |Chg s d|, but that
change contains no sharing whatsoever and will synchronize badly. 
Traditional edit-scripts based techniques
optimize for a lower cost, which usually translates to more copies. Yet, this
does not necessarily translate to high quality patches: especially when there
is more than one lowest-cost patch. \digress{In fact, I have not
came up with a satisfactory definition of ``best'' patch in this \texttt{hdiff}
setting.}

  Assuming the existence of said \emph{sharing map}, let its query 
function be |wcs s d| -- which reads as ``which common subtree'' -- with
type |SFix kappa fam at -> Maybe (MetaVar kappa fam at)|, such that
|wcs s d x| returns |Just i| when |x| is a common subtree of |s| and
|d| uniquely identified by |i|. A first, naive, attempt at writing an
extraction function would simply traverse the source and destination
trees substituting those subtrees that should be shared by a
metavariable, like |extract| below.

\begin{myhs}
\begin{code}
extract  :: (forall at' dot SFix kappa fam at' -> Maybe Int) 
         -> SFix kappa fam at -> Holes kappa fam (MetaVar kappa fam) at
extract wcs x = maybe (roll x) Hole (wcs x)
  where
    roll (Prim x) = Prim x
    roll (SFix x) = Roll (repMap (extract wcs) x) 
\end{code}
\end{myhs}

  Here, although |extract| could already produce changes from 
source |s| and destination |d|, it would \emph{not} satisfy the
criteria that |apply (chg s d) s == Just d| for all |s| and |d|.
The problem can be easily seen with a source and
a destination trees such that a common subtree occurs
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
\begin{myhs*}[.40\textwidth]%
\begin{code}
wcs s d (Bin t u)  = Just (metavar x)
wcs s d t          = Just (metavar y)
wcs s d u          = Just (metavar z)
wcs _ _ _          = Nothing
\end{code}
\end{myhs*}
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
well-formed changes. The nested occurence of |t| within |Bin t u|
here yields a change with an undefined variable on its insertion
context.}
\label{fig:pepatches:extract-problem-01}
\end{figure}

\begin{myhs}
\begin{code}
chg :: SFix kappa fam at -> SFix kappa fam at -> Chg kappa fam at
chg s d = let f = wcs s d in Chg (extract f s) (extract f d)
\end{code}
\end{myhs}

  There are two natural ways to solve this problem. Either replace |metavar y|
by |t| and ignore the sharing or replace |metavar x| by |Bin (metavar
y) (metavar z)|, pushing the metavariables to the leaves maximizing
sharing. These would give rise to the changes shown in 
\Cref{fig:pepatches:extract-sol-01}. There is friction
between wanting to maximize the spine but at the same time achieve maximal
sharing without having a clear answer. On the one hand, copies closer
to the root are easier to merge and less sharing means it is 
easier to isolate changes to separate parts of the tree.
On the other hand, sharing as much as possible might better capture
the nature of the change being represented better.

  These two methods are not the only solution, though.  Another option
is to simulate the \unixdiff{} \texttt{--patience} option, which only
copies uniquely ocurring lines -- in our case, we would only share
uniquely occuring subtrees. In fact, to make this easy to experiment,
we will parameterize our |extract| function with which method should
we use.

\begin{myhs}
\begin{code}
data ExtractionMode  =  NoNested
                     |  ProperShare
                     |  Patience
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
are not the same in general. 
  
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
\subfloat[Expand metavariables pursuing all sharing oportunities]{%
\begin{myforest}
[,change
  [|Bin| [|Bin| [y,metavar] [z,metavar]] [k]]
  [|Bin| [|Bin| [y,metavar] [z,metavar]] [y,metavar]]
]
\end{myforest}
\label{fig:pepatches:extract-sol-01:proper}}%
\caption{Context extraction must care to produce
well-formed changes. The nested occurence of |t| within |Bin t u|
here yields a change with an undefined variable on its insertion
context.}
\label{fig:pepatches:extract-sol-01}
\end{figure}

  Finally, the |diff| function receives a source and destination
trees, |s| and |d|, and computes a patch that encodes the information
necessary to transform the source into the destination. In practice,
to achieve an efficient ``which common subtree'' query we need to
preprocess the inputs (\Cref{sec:pepatches:preprocess}) and build the
sharing map from these preprocessed trees.  We then extract the
contexts (\Cref{sec:pepatches:extract}), which yields a |Chg|, and finally translate that |Chg| into
a |Patch| by pulling the largest possible spine, with |close|.

\begin{myhs}
\begin{code}
diff  :: (All Digestible kappa) => SFix kappa fam at -> SFix kappa fam at
      -> Patch kappa fam at
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
values that appear on the spine, as illustrated in \Cref{fig:pepatches:cpyonspine},
where the |42| does not get shared for its height is smaller than 1 but
since it occurs in the same location in the deletion and insertion context,
we flag it as a copy -- which involes issuing a fresh metavariable, hence
the parameter |i| in the code above.

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

  Next we look at how to define the |wcs| oracle efficiently and look 
at the diffrent algorithms for extracting contexts according to
each mode in |ExtractionMode|.

\subsection{Which Common Subtree, Efficiently}

  Next we look at defining |wcs s d| efficiently. This consists,
firstly, in computing a set of trees, containing the trees which
occur as subtrees of |s| and subtrees of |d|, and secondly, being
able to efficiently process membership queries on this set.
This is not a new challenge, in fact, Computer Algebra Systems, 
Theorem Provers and many other symbolic-manipulation-heavy systems 
use a technique known as \emph{hash-consing} to overcome similar problems.
Hash-consing~\cite{Goto1974,Filliatre2006} is a canon of programming
folklore and is most often used as a means of \emph{maximal sharing} of
subtrees in memory and constant time comparisson -- two trees are
equal if they are stored in the same memory location -- but it 
is not limited to it. We will be using a variant of \emph{hash-consing}
to compute |wcs s d|.

  In our setup for computing |wcs s d| we start with transforming
|s| and |d| into \emph{merkle-trees}~\cite{Merkle1988}, that is, 
trees annotated with hashes. We then compute the intersection
of set of hashes that appear in |s| and |d|: these are the
hashes of the trees that appear as subtrees of |s| and |d|, or,
\emph{common subtrees}. Finally, whenever we would like to query 
whether |x| is a common subtree we check if its hash appear
in the set we have just computed.

  Note that we will only be checking whether |x| is a common
subtree of |s| and |d| for the |x|'s that are already subtrees
of |s| \emph{or} |d|. Recall the naive |chg| function:

\begin{myhs}
\begin{code}
chg :: SFix kappa fam at -> SFix kappa fam at -> Chg kappa fam at
chg s d = let f = wcs s d in Chg (extract f s) (extract f d)
\end{code}
\end{myhs}

  This means that we would already have computed the hash of |x|,
in order to have computed the hash of |s| and |d|. Recomputing this
hash would be a waste of precious time. Instead, it is better to just
annotate our trees with hashes at every point -- another situations where
having support for generic annotated fixpoints is crucial.
In fact, prior to doing any diff-related computation, we preprocess our
trees with their hash and their height.

\begin{myhs}
\begin{code}
data PrepData a = PrepData  {  getDigest  :: Digest
                            ,  getHeight  :: Int
                            }  

type PrepFix kappa fam
  = SFixAnn kappa fam PrepData

preprocess  :: (All Digestible kappa) => SFix kappa fam at -> PrepFix kappa fam at
preprocess = synthesize dots
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
        \draw [hdiff-black,->] (A.east) [out=25, in=165]to node[midway,above]{|preprocess|} (!c.west);
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
\caption{Example of annotating a tree with hashes and heights, through the
|preprocess| function.}
\label{fig:pepatches:preprocess}
\end{figure}

 \Cref{fig:pepatches:preprocess} illustrates a call to |preprocess|. The hashes
are computed from the a unique identifier per constructor and a concatenation
of the hashes of the subtrees. The hash of the root in \Cref{fig:pepatches:preprocess},
for example, is computed with a call to |hash (concat ["Main.Tree.Bin", "310dac", "4a32bd"])|.
This ensures that hashes uniquely identify a subtree modulo hash collisions.

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
alloate fresh names without having to go inspect the whole map again.

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
was to avoid the unecessary recomputation of their hashes. Consequently,
we are better off carrying these preprocessed trees everywhere through
the computation of changes. The final |wcs| function wil have its type
slightly adjusted and is defined below.

\begin{myhs}
\begin{code}
wcs  :: (All Digestible kappa) 
     => PrepFix kappa fam at -> PrepFix kappa fam at
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
and ignore the remote possiblity of hash collisions.
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

\subsection{Extracting the Contexts}
\label{sec:pepatches:extract}

  Having an efficient ``which common subtree'' oracle in our toolbox,
we move on to defining the different context extraction techniques,
which are very similar to the naive |extract| that was sketched before.
We traverse the tree and each time we reach a common subtree, substitute
by its corresponding metavariable. 

  To some extent, we could compare context extraction to the translation
of tree mappings into edit-scripts: our tree mappings are given by |wcs|
and instead of computing an edit-scripts, we compute terms with metavariables.
Classical algorithms are focused in computing the \emph{least cost}
edit-script from a given tree mapping. In our case, the notion of
\emph{least cost} hardly makes sense -- besides not having defined
a cost semantics to our changes, we are interested in those that
merge better which might not necessarily be those that insert and delete
the least amount of constructors. Consequently, there is a lot of
freedom in defining our context extraction techniques. We have looked
at three particular examples, but hint at other possibilities
later on in \Cref{sec:pepatches:discussion}.

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

  \Cref{fig:pepatches:extraction-methods} illustrates the changes
that would be extracted folowing each |ExtractionMode| for the 
same |s| and |d|. We will soon define each context extraction method,
but before we do so, we need a few auxiliary definitions.
 
  Computing the set of common subtrees is straight forward and does
not involve many design decisions. Deciding which of those subtrees
are eligible to be shared, though, is an entirely diffrent beast. As
we mentioned before, we surely do not want to share all \texttt{int}
constants throughout a file, for example.  Or, we would not like to
share all variables with the same name as they might be different
variables. As a matter of fact, a good definition of what can be
shared might even be impossible without domain-specific knowledge.

  We chose to never share subtrees with height smaller than a given
parameter. Our choise is very pragmatic in the sense that we have
the height of the trees available from |preprocess| and it does not
involve any domain specific knowledge. \digress{In the code, I abstracted this
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
  =  if h x  then  maybe recurse (mkHole x) $$ lookup (getDigest ann) sm 
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
other occurences of |x|.

  Extracting contexts with under the |ProperShare| mode
consists in annotating the source and destination trees with
a boolean indicating whether or not they are a proper share,
then proceeding just like |Patience|, but instead of checking
that the arity must be two, we check that the tree is classified
as a \emph{proper-share}.

\section{Discussion}
\label{sec:pepatches:discussion}

\victor{Frst person or third person?}

  With \texttt{hdiff} we have seen that detachnig from edit-scripts
might have paid off. We were able to define a computatonally efficient
differencing algorithm and seen how our patches can still be merged
and posses a sensible algebraic structure. In \Cref{chap:experiments} we 
will be discussing the empirical evaluation in detail, but in summary, 
\texttt{hdiff} has shown a very strong potential for practical use. 

\victor{Things I'd like to talk about:
\begin{itemize}
  \item sharing
  \item lack of cost semantics
  \item complexity hypothesis and relation to edit-scripts
\end{itemize}

Yet, some of those might be better off in our Discussion \textbf{chapter}... no?}




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
