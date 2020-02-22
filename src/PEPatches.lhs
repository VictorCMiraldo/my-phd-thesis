  the \texttt{stdiff} approach gave us a first representation
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

  A \emph{changes}, then, is defined as a pair of a deletion context and an
insertion context for the same type.  As expected, these contexts are
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

  Naturally, we expect a change to be well-scoped, that is,
all the variables that are present in the insertion context
must also occur on the deletion context, or, in Haskell:

\begin{myhs}
\begin{code}
vars        :: HolesMV kappa fam at -> Map Int Arity

wellscoped  :: Chg kappa fam at -> Bool
wellscoped (Chg d i) = keys (vars i) == keys (vars d) 
\end{code}
\victor{decide... is |vars del == vars ins| or |vars ins < vars del|}?
\end{myhs}

  The semantics of |Chg| through its application function is simple.
Applying a change |c| to an element |x| consists in unifying |x|
with |chgDel c|, yielding a substitution |sigma| which
can be applied to |chgIns c|. Note that since |x| has no holes,
a successful unification means |sigma| has a term for each metavariable 
in |chgDel c|. When we apply |sigma| to |chgIns c| we are
guaranteed to substitute every metavariable in |chgIns c|
because changes are well-scoped.

\begin{myhs}
\begin{code}
applyChg  :: (All Eq kappa)
          => Chg kappa fam at -> SFix kappa fam at -> Maybe (SFix kappa fam at)
applyChg (Chg d i) x = 
  either  (const Nothing) (Just . holesUncast . flip substApply i) 
          (unify d (holesCast x))
\end{code}
\end{myhs}


\begin{figure}
\centering
\subfloat{%
\begin{myforest}
[,rootchange 
  [|Bin| [x,metavar] [|Leaf| [|5|]]]
  [|Bin| [x,metavar] [|Leaf| [|6|]]]
]
\end{myforest}
\label{fig:pepatches:example-04:A}}%
\quad\quad\quad
\subfloat{%
\begin{myforest}
[,rootchange 
  [|Bin| [|Leaf| [|42|]] [z,metavar]]
  [|Bin| [|Leaf| [|84|]] [|Bin| [z,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:example-04:B}}%
\caption{Example of disjoint changes.}
\label{fig:pepatches:example-04}
\end{figure}

\paragraph{Patch versus Changes.} Our current definition of change is
akin to what is known as a \emph{tree-matching} in the literature of
classical tree differencing, \Cref{sec:background:tree-edit-distance},
albeit our changes are more permissive. Since we do not want to
obtain an edit-script we do not need to enforce any of the
restrictions.  In fact, the engine of our differencing algorithm,
\Cref{sec:pepatches:diff}, will only be concerned with producing a
single |Chg| that transforms the source into the
destination. In fact, \emph{changes} and their application
semantics already gives rise to a satisfactory structure,
which we shall see shortly in \Cref{rec:pepatches:meta-theory}.
Yet, we are interested in more than just applying changes, we would
like to synchronize them, which will require a more refined approach.

  In order to synchronize changes effectively we must
understand which constructors in the deletion context are, in fact, just being 
copied over in the insertion context. Take \Cref{fig:pepatches:example-04}, where 
one change operates exclusively on the right child of a binary tree whereas the other 
alters the left child and duplicates the right child in-place. 
These changes are disjoint and should be possible to be automatically synchronizable. 
Recognizing them as such will require more expressivity than what is provided by |Chg|.
Let there be |PatchPE|.

  In the following we distinguish \emph{changes} from \emph{patches}
and discuss the design space. \Cref{sec:pepatches:closures,sec:pepatches:alignments} 
go more in depth about computing a \emph{patch} from a \emph{change} in a way
that makes synchronization easier.

\begin{figure}
\centering
\subfloat[Insertion as a \emph{change}]{%
\begin{myforest}
[,rootchange 
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

\victor{I'm unsure with this justification of pushing
changes down; I mean... we could just have written a ``better''
merge algorithm}

  A first observation of the definition of |Chg| reveals that the 
deletion context might ``delete'' many constructors that the insertion context later
insert. As is the case with both changes in \Cref{fig:pepatches:example-04}.
This hides away the fact that the |Bin| at the root of the tree
was, in fact, being copied. Following the \texttt{stdiff} nomenclature,
the |Bin| at the root of both changes in \Cref{fig:pepatches:example-04}
should be flagged as belonging to a \emph{spine} of the patch.
That is, it is copied over from source to destination but it leads
to changes further down the tree.

  Another example can be found in \Cref{fig:pepatches:example-02:chg},
where |Bin 42| is repeated in both contexts -- whereas in
\Cref{fig:pepatches:example-02:patch} it has been placed in the spine
and consequently, has become easier to identify as a copy.
In fact, we would like to distinguish a \emph{patch} from a \emph{change}
precisely by the presence of a \emph{spine} which leads
to smaller changes, encoded by the type |PatchPE|:

\begin{myhs}
\begin{code}
type PatchPE kappa fam = Holes kappa fam (Chg kappa fam)
\end{code}
\end{myhs}

  Converting a change to a patch is intuitively done by trying to extract as many
redundant constructors from the change's contexts into the spine as
possible. Another way of looking into it is pushing the changes to the
leaves of the tree. 

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
[,rootchange 
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

  Now, there are two different ways to push changes down to the leaves
of the tree, as illustrated by \Cref{fig:pepatches:example-03}.  We
can consider the patch metavariables to be \emph{globally-scoped},
yielding structurally minimal changes, as in
\Cref{fig:pepatches:example-03:B}.  Or, we could strive for
\emph{locally-scoped}, where each change might still contain repeated
constructors as long as they are necessary to ensure the change is
\emph{closed}, as in \Cref{fig:pepatches:example-03:C}.

  The first option, of \emph{globally-scoped} patches, is
very easy to compute. All we have to do is to compute the
anti-unification of the insertion and deletion context.

\begin{myhs}
\begin{code}
globallyScopedPatch :: Chg ki codes at -> PatchPE ki codes at 
globallyScopedPatch (Chg d i) = holesMap (uncurry' Chg) (lgg d i)
\end{code}
\end{myhs}

  From a synchronization point of view, however, \emph{globally-scoped}
patches are a dangerous road. They do minimize changes, but since 
variables can be referenced anywhere in the patch, the synchronization algorithm
can hardly recognize a local copy. The only real benefit or \emph{globally-scoped}
patches is that they will require up to half the storage space, in the worst
case. We argue this is not enough benefit to outweight the representational
difficulties caused by it. For example, \Cref{fig:pepatches:misaligned} shows 
a globally scoped patch produced from a change that makes it difficult
to understand that the |Bin 42| is has actualy been deleted. 
This is because the first |Bin| constructor
is considered to be in the spine since anti-unification proceeds top-down.
A bottom-up approach would be even harder and would suffer similar issues
for insertions anyway. \victor{This is a problem Harmony also had!}

  Our option of \emph{locally-scoped} changes implies that
changes might still contain repeated constructors in the root
of their deletion and insertion contexts -- hence they will not be
structurally minimal. On the other hand, copies are easy to
identify and reconciliation will happen \emph{in place}. This later
reason being particularly important for a industrial synchronizer --
when synchronization fails, \emph{conflicts} can be issued for
small parts of the tree instead of the whole patch.

\begin{figure}
\centering
\subfloat[Change that deletes |42| at the head of a list.]{%
\begin{myforest}
[,rootchange , s sep=1mm
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

  Regardless of global versus local scope changes, 
forgetting the information about the spine yields a forgetful
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


  We have to be careful with |chgDistr|, as defined above,
not to capture variables. It will only work properly
if all metavariables have already been properly $\alpha$-converted
to avoid capturing. We cannot enforce this invariant for performance reasons.
We will, however, continuously ensure that even though we
produce and work with \emph{locally scoped} patches, all scopes
contains disjoint sets of names and therefore can be safely distributed.

  The application semantics of |Patch| is best defined in terms
of |applyChg|. Assume all metavariable scopes are disjoint, the
application of a patch is defined as:

\begin{myhs}
\begin{code}
apply  :: (All Eq kappa)
       => Patch kappa fam at -> SFix kappa fam at -> SFix kappa fam at
apply  = applyChg . chgDistr
\end{code}
\end{myhs}

  In \Cref{sec:pepatches:meta-theory} we will look at how
this simple application semantics for patches already gives rise to 
familiar structures -- a partial grupoid or monoid depending on whether we
allow metavariables to be left unused. Finally, we discuss how to
optimize our patches for synchronization in \Cref{sec:pepatches:closures}
and \Cref{sec:pepatches:alignment}.
\subsection{Computing Closures}
\label{sec:pepatches:closures}


\begin{figure}
\centering
\subfloat[Not minimal; |Bin| is repeated.]{%
\quad
\begin{myforest}
[,rootchange 
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Bin| [|Leaf| [|84|]] [x,metavar]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:A}}%
\quad\quad
\subfloat[Not minimal; root constructors differ.]{%
\quad
\begin{myforest}
[,rootchange 
  [|Bin| [|Leaf| [|42|]] [x,metavar]]
  [|Tri| [|Leaf| [|42|]] [x,metavar] [|Leaf| [|84|]]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:B}}%

\subfloat[Not minimal; change is ill-scoped.]{%
\quad
\begin{myforest}
[|Bin|, s sep=5mm
  [|Leaf| [,change [|42|] [|84|]]]
  [,change [x,metavar] [y,metavar]]
]
\end{myforest}
\quad
\label{fig:pepatches:example-minimal:C}}%
\quad\quad
\subfloat[Minimal change equivalent to \ref{fig:pepatches:example-minimal:A}]{%
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
  A change |c :: Chg kappa fam at| is said to be in \emph{minimal}
form if and only if is closed with respect to some global scope 
and, either |chgDel c| and |chgIns c| have different
constructors at their root or,  they contain the same constructor and said constructor
is necessary to maintain well-scopedness. That is, when |chgDel c| and
|chgIns c| contain the same constructor, say, |inj|, we have that
|chgDel c = inj d0 dots dn| and |chgIns c = inj i0 dots in|.
If there exists a variable |v| that occurs in |ij| but is not defined in |dj|
then we cannot pull |inj| into a spine and whilst maintaining all
changes well scoped, as is the case in \Cref{fig:pepatches:example-03:C},
for example. \Cref{fig:pepatches:example-minimal} illustrates some cases
of non minimal changes and one minimal change.
%}

  Given a well-scoped change |c :: Chg kappa fam at| we would like to
compute the largest spine |p| such that all changes in the leaves of
|p| are closed. Defining whether a change is closed or not has its
nuances. Firstly, we can only know that a change is in fact closed if
we know, at least, how many times each variable is used.  Say a
variable |x| is used |n + m| times in total, and it has |n| and |m|
occurences in the deletion and insertion contexts of |c|, then |x| is
not used anythwere else but in |c|. If all variables of |c| are
\emph{local} to |c|, we say |c| is closed. Given a multiset of
variables |g :: Map Int Arity| for the global scope, we can encode
|isClosedChg| in Haskell as:

\begin{myhs}
\begin{code}
isClosed :: Map Int Arity -> Map Int Arity -> Map Int Arity -> Bool
isClosed global ds us = M.unionWith (+) ds us `isSubmapOf` global

isClosedChg :: Map Int Arity -> Chg kappa fam at -> Bool
isClosedChg global (Chg d i) = isClosed global (vars d) (vars i)
\end{code}
\end{myhs}

  Given a well-scoped change |c|, we minimize it
by computing the least general generalization |s = lcp (chgDel c) (chdIns c)|, 
which might contain \emph{locally ill-scoped} changes, then pushing
constructors that are in the spine into the changes until they are
all closed. \Cref{fig:pepatches:example-03} provides a good
illustration of this process. Computing the closure of
\Cref{fig:pepatches:example-03:A} is done by computing
\Cref{fig:pepatches:example-03:B}, then \emph{pushing} the the |Bin|
constructor down the changes, fixing their scope, resulting in
\Cref{fig:pepatches:example-03:C}.

  The |close| function, below, is responsible for pushing
constructors through the least general generalization until they
represent minimal changes. It calls an auxiliary version that receives 
the global scope and keeps track of the variables it seen so far.
The worst case scenario happens when the we need \emph{all} constructors
of the spine to close the change, in which case, |close c = Hole c|;
yet, if we pass a well-scoped change change to |close|, we must be able 
to produce a patch.
  
\begin{myhs}
\begin{code}
close :: Chg kappa fam at -> Holes kappa fam (Chg kappa fam) at
close c =  let  global  = vars h
                aux     = holesMap annWithVars (lgg (chgDel d) (chgIns d))
            in case close' global aux of
                 InL _  -> error "invariant failure: c was not well-scoped."
                 InR b  -> Just (holesMap body b)
\end{code}
\end{myhs}
  
  Deciding whether a given change is closed or not requires us to keep
track of the variables we have seen being declared and used in a change.
Recomputing this multisets would be a waste of resources and would yield
a much slower algorithm. The |annWithVars| function below computes the 
variables that occur in two contexts and annotates a change with them:
  
\begin{figure}
\begin{myhs}[0.99\textwidth]
\begin{code}
close'  :: M.Map Int Arity
        -> Holes kappa fam (WithVars (Chg kappa fam)) at
        -> Sum (WithVars (Chg kappa fam)) (Holes kappa fam (WithVars (Chg kappa fam))) at 
-- Primitive values are trivially closed;
close' _  (Prim x)  = InR (Prim x)
-- Changes might be closed, or they require no more work;
close' gl (Hole cv)
  | isClosed gl (decls cv) (uses cv)  = InR (Hole cv)
  | otherwise                         = InL cv
-- Recursive calls need to understand whether /all/ recursive components
-- are closed.
close' gl (Roll x) =
  let aux = repMap (close' gl) x
   in case repMapM fromInR aux of
        -- When all recursive components are closed, /Roll/ goes in the spine.
        Just res -> InR (Roll res)
        -- If at least one component is not closed, we need to distribute /Roll/
        -- through the deletion and insertion contexts and decide whether that
        -- closed the change or not.
        Nothing  -> let  chgs  = repMap (either' id (chgDistr . body)) aux
                         -- Compute unions of the /decls/ and /uses/ multisets
                         dels  = foldr (\c -> unionWith (+) (getDecls c)) empty 
                                       $$ repLeaves chgs
                         inss  = foldr (\c -> unionWith (+) (getUses c)) empty 
                                       $$ repLeaves chgs
                         -- Compute the final deletion and insertion contexts
                         cD    = Roll (repMap (chgDel . body)) chgs
                         cI    = Roll (repMap (chgIns . body)) chgs
                     in if isClosed gl dels inss
                        then InR (Hole  (ChgVars dels inss (Chg cD cI)))
                        else InL        (ChgVars dels inss (Chg cD cI))
  where
    getDecls  :: Exists (WithVars (Chg kappa fam)) -> Map Int Arity
    getUses   :: Exists (WithVars (Chg kappa fam)) -> Map Int Arity
    fromInR   :: Sum f g x -> Maybe (g x)
\end{code}
\end{myhs}
\caption{The |close'| auxiliar function}
\label{fig:pepatches:close-aux}
\end{figure}

\begin{myhs}
\begin{code}
data WithVars x at = WithVars  { decls  :: Map Int Arity
                               , uses   :: Map Int Arity
                               , body   :: x at
                               }

annWithVars :: (Holes kappa fam :*: Holes kappa fam) at -> WithVars (Chg kappa fam) at
annWithVars (d :*: i) = WithVars (vars d) (vars i) (Chg d i)
\end{code}
\end{myhs}
  
  The |close'| function albeit having a somewhat intimidating
implementation, is conceptually simple.
It receveies a spine |s|, with leaves of type |WithVars (Chg dots)|, and attemps
to ``enlarge'' those leaves if necessary. When it is not possible to close 
the current spine, it returns a |WithVars (Chg dots)| equivalent to pusing all the
constructors of |s| down the deletion and insertion contexts.
The implementation of |close'| is shown in its entirety in \Cref{dif:pepatches:close-aux}.
\victor{I'm thinking of moving all these large functions to a separate 
section or chapter somewhere. Does that make sense?}

  It is worth noting that computing a \emph{locally scoped} patch
from a large monolithic change only helps in preventing situations
such the bad alignment presented in \Cref{fig:pepatches:misalignment:A}.
In fact, let |c| be as in \Cref{fig:pepatches:misaligment:A},
a call to |close c| would return |Hole c| -- meaning |c| is already
in minimal closed form and cannot have a larger spine whilst maintaining
well-scopedness. Another way of putting it is that we at least
do not make things worse, but we surely are not able to recognize
the deletion of |Bin 42| effectively either. 

  Recognizing deletions and insertions is crucial for us: no
synchronization algorithm can achieve effective results if it cannot
separate old information from new information. Flagging |Bin 42| as a
deletion in \Cref{fig:pepatches:misaligment:A} means we still must
produce an \emph{aligment} of the minimal changes produced by |close|.

\subsection{Aligning Closed Changes}
\label{sec:pepatches:alignments}

  An \emph{aligment} for a change |c| consists in 
connecting which parts of the deletion context correspond
to which pars of the insertion context, that is, which constructors
or metavariables represent \emph{the same information} in the 
source object of the change.

  Much like in \texttt{stdiff} we will be representing a deletion or
insertion of a recursive ``layer'' by identifying the position
\emph{where} this modification must take place. Moreover, said position
must be a recursive field of the inserted or deleted constructor -- that is, 
the deletions or insertions must not alter the type that our patch
is operating over. This is easy to identify since we 
thanks to our typed approach, where we always have access to type-level 
information. \victor{should I talk a bit about how harmony ``solved'' this differently?}

  Take \Cref{fig:pepatches:alignment-01:A}, for example.
It shows the same problematic change as \Cref{fig:pepatches:misalignment:A}, 
, which had a deletion at the root. Yet, \Cref{fig:pepatches:alignment-01:B}
illustrates what an \emph{aligned} variant of the same change:
The |Bin 42| at the root is identified as a deletion, which in turn, 
puts matches the subsequent |(:)| constructors correctly. As a result, 
it is trivial to identify that |metavar x|, |metavar y| and |metavar z|
are mere copies.

  The deletion of |Bin 42| in \Cref{fig:pepatches:alignment-01:B}
has all fields, except one recursive field, contain no metavariables. 
We call such trees with no metavariables \emph{rigid} trees.
Since \emph{rigid} trees contain no metavariables, none of their
subtrees is being copied, moved or changed anywhere. In fact,
they have been entirely deleted from the source or inserted
at the destination of the change.

\begin{figure}
\centering
\subfloat[Change that deletes |42| at the head of a list.]{%
\begin{myforest}
[,rootchange , s sep=1mm
  [|Bin| [|42|] [|Bin| [x,metavar] [|Bin| [y,metavar] [z,metavar]]]]
  [|Bin| [x,metavar] [|Bin| [y,metavar] [z,metavar]]]
]
\end{myforest}
\label{fig:pepatches:alignment-01:A}}
\quad\quad
\subfloat[Deletion of |Bin 42| correctly identified.]{%
\begin{myforest}
[, delctx 
  [|Bin| [|Leaf| [|42|]] [SQ]]
  [|Bin|, s sep=-4mm 
      [Cpy]
      [|Bin| [Cpy] [Cpy]]
%     [,change [x,metavar] [x,metavar]]
%     [|Bin|, s sep=4mm
%       [,change [y,metavar] [y,metavar]]
%       [,change [z,metavar] [z,metavar]]]
  ]
]
\end{myforest}
\label{fig:pepatches:alignment-01:B}}%
\caption{Properly aligned version of \Cref{fig:pepatches:misaligment}.}
\label{fig:pepatches:alignment-01}
\end{figure}

  In the remainder of this section we shall discuss how to represent
an aligned change, such as \Cref{fig:pepatches:alignment-01:B}, and
how to compute them from a |Chg kappa fam at|. All in all, we are interested
in defining the |align| function, declared below.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
\end{code}
\end{myhs}

  In general, we represent insertions and deletions with a |Zipper|~\cite{Huet1991}, 
discussed in \ref{sec:gp:simplistic-zipper}, which carries
trees with no holes (encoded by |SFix kappa fam|) in all its positions 
except one, where we continue aligning. An alignment |Al kappa fam f at|
represents a sequence of insertions and deletions interleaved with
spines which ultimately lead to \emph{modifications}, which
are typed according to the |f| parameter.

\begin{myhs}
\begin{code}
data Al kappa fam f at where
  Del  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f)  x 
       -> Al kappa fam f at
  Ins  :: Zipper (CompoundCnstr kappa fam at) (SFix kappa fam) (Al kappa fam f) x
       -> Al kappa fam f at
\end{code}
\end{myhs}

  The |CompountCnstr| constraint must be carried around to indicate we are 
aligning a type that belongs to the mutually recursive family and therefore has 
a generic representation -- just a Haskell technicality.

  Naturally, if no insertion or deletion can be made but both 
insertion and deletion contexts have the same constructor, we want to
recognize this constructor as part of the spine and continue aligning
its fields pairwise.

\begin{myhs}
\begin{code}
  Spn  :: (CompoundCnstr kappa fam x)
       => SRep (Al kappa fam f) (Rep x)
       -> Al kappa fam f x
\end{code}
\end{myhs}

  When no |Ins|, |Del| or |Spn| can be used,
we must be fallback to recording a modification, which here
is of type |f at|.
  
\begin{myhs}
\begin{code}
  Mod  :: f at -> Al kappa fam f at
\end{code}
\end{myhs}

  Finally, it is useful to flag copies and permutations early
for they are easy to synchronize. A copy is witnessed by
a change |c = Chg (metavar x) (metavar x)| such that |metavar x|
only occurs twice globally. This means all occurences of |metavar x| have
been accounted for in |c| and the tree at |metavar x| in the source
of the change is not being duplicated anywhere else.

  A permutation, on the other hand, is witnessed
by |c = Chg (metavar x) (metavar y)|, where both |metavar x|
and |metavar y| only occur twice globally. It is a bit more
restrictive than a copy, since this represents that the tree at |metavar x|
is being moved, but at least we know it is not being duplicated
or contracted.

\begin{myhs}
\begin{code}
  Cpy  :: MetaVar kappa fam at                          -> Al kappa fam f at
  Prm  :: MetaVar kappa fam at -> MetaVar kappa fam at  -> Al kappa fam f at
\end{code}
\end{myhs}

\victor{Show how to convert back to |Chg|?}

  Equipped with a definition for aligments, let us
look at how to actually define |alignChg|.
Given a change |c|, the first step of |alignChg c| is to check whether the 
root of |chgDel c| (resp. |chgIns c|) can
be deleted (resp. inserted) -- that is, all of its fields are \emph{rigid}
trees with the exception of a single recursive field. If
we can delete the root, we flag it as a deletion and continue through
the recursive \emph{non-rigid} field. If we cannot perform a
deletion at the root of |chgDel c| nor an insertion at
the root of |chgIns c| but they are constructed with the
same constructor, we recurse on trying on the children.
If |chgDel c| and |chgIns c| do not even have the same constructor
at the root, we fallback and flag an arbitrary modification. 

  Checking for rigid subtrees must be carefully translated into an algorithm if
we ever want to squeeze any performance out of it: we must compute
whether each tree in our input is rigid and annotate this at their root,
otherwise we will be looking into an exponential time alignment algorithm.  
Luckily, our generic programming library has great support for
all variations over fixpoints. Annotating a tree augmented with
holes with information about whether or not any |Hole| constructor
occurs can be done as in \Cref{fig:pepatches:rigidity}.
  
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

  The extraction of a zipper flagging an insertion or deletion
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

  The return type is almost what the |Del| and |Ins|
constructors expect: a value of type |t| where all but one
recursive positions are populated by the |SFix kappa fam| datatype, \ie{},
trees with \emph{no holes} or \emph{rigid}. The identified
recursive position is of type |HolesAnn kappa fam IsRigid dots|,
which is what we will use to continue aligning against.
We ommit the implementation of |hasRigidZipper| but invite the interested
reader to check the source code.\victor{where?}

  Assembling all these pieces will yield the definition of |alignChg|,
which will compute the multiset of variables used througout a change,
annotate the deletion and insertion context with |IsRigid| and proceed
to actually align them with the |al| function, whose full
definition can be found in \Cref{fig:pepatches:align-fulldef}, and,
albeit long, is rather simple. In general lines, |al| attempts to delete as many
constructors as possible, followed by inserting as many constructors
as possible; whenever it finds that it deleted and inserted the same constructor,
it issues a |Spn| alignment and calls itself recursively on the leaves
of the |Spn|. Ultimately it falls back to |Cpy|, |Prm| or |Mod|.

\begin{myhs}
\begin{code}
alignChg  :: Chg kappa fam at -> Al kappa fam (Chg kappa fam) at
alignChg (Chg d i) = al vars (annotRigidity d) (annotRigidity i)
  where vars = chgVars (Chg d i)
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
       Nothing -> alD (alMod vars) d i
       Just r  -> Spn (repMap (uncurry' f) r)
   syncSpine vars _ d i = alD (alMod vars) d i

   -- Records a modification, copy or permutation.
   alMod :: Map Int Arity -> Aligned kappa fam
   alMod vars (Hole' _ vd) (Hole' _ vi) =
     -- are both vd and vi with arity 2?
     | all (== Just 2 . flip lookup vars) [metavarGet vd , metavarGet vi]
        =  if vd == vi 
           then Cpy vd 
           else Prm vd vi
     | otherwise 
        = Mod (Chg (Hole vd) (Hole vi))
   alMod _ d i = Mod (Chg d i)
\end{code}
\end{myhs}
\caption{Complete definition of |al|.}
\label{fig:pepatches:align-fulldef}
\end{figure}

\victor{
Still mention:
\begin{itemize} 
  \item This is an important use of type-level information!
  \item Conjecture: arbitrarily deep zippers will give edit-script like complexity!
that's where the log n is hidden.
\end{itemize}
}

\subsection{Meta Theory}
\label{sec:pepatches:meta-theory}

\victor{UNFINISHED SUBSECTION}

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
possible if and only if the image of |applyChg c0| has elements in common
with the domain of |applyChg c1|. This can be easily witnessed
by trying to unify |i0| with |d1|. If they are unifiable, the changes
are composable. In fact, let |sigma = unify i0 d1|, the
change that witnesses the composition is given by 
|c = Chg (substApply sigma d0) (substApply sigma i1)|.

\begin{myhs}
\begin{code}
after :: Chg kappa fam at -> Chg kappa fam at -> Maybe (Chg kappa fam at)
q `after` p =
  case unify (chgDel q) (chgIns p) of
    Left   _      -> Nothing
    Right  sigma  -> Just (Chg  (substApply sigma (chgDel p))
                                (substApply sigma (chgIns q)))
\end{code}
\end{myhs}

\victor{
The |PatchPE ki codes| forms either:
\begin{itemize}
\item Partial monoid, if we want |vars ins <= vars del|
\item Grupoid, if we take |vars ins == vars del|
\end{itemize}

\begin{myhs}
\begin{code}
alDistr :: Holes kappa fam (Al kappa fam) at -> Al kappa fam at
\end{code}
\end{myhs}
}


\section{Merging Aligned Patches}
\label{sec:pepatches:merging}

\victor{bridge!}

\victor{should I call it |merge| instead of |diff3|? Maybe...
diff3 already exists and is the unix diff3.}

\victor{I'm inclined in borrowing a \texttt{\\digress} env
like in Mandelbrot's ``Fractal Geom. of Nature''; where I write
in the first person about my experience doing things; could
be a good way to add bits like the following:


  \digress{Before going into the details of synchronization, a little
prelude is due. In this section we will discuss the sketch
of a merge algorithm, but this is by no means final. We believe
a more elegant algorithm could be possible, if we have had more
time to think this through better. Yet, unfortunately, at one
point one has to stop and write their thesis. The sketch
we present here was the last aspect we worked on.}
}

  Synchronizing changes is done by the |diff3| function,
which receives two aligned patches |p| and |q| with
a disjoint set of metavariables and such that
|domain p| and |domain q| contain at least one common element
and produces a spine annotated with either conflicts or
changes:

\begin{myhs}
\begin{code}
type PatchC kappa fam at
  = Holes kappa fam (Sum (Conflict kappa fam) (Chg kappa fam)) at
\end{code}
\end{myhs}

  A conflict is issued whenever we were not able to reconcile
the alignments in question. This can happen for two reaons: either
we could not detect that two edits to the same region are safe
or we could not infer that a given metavariable was equal to 
some other, when we are replicating edits through duplications and
contractions. 

\begin{myhs}
\begin{code}
data Conflict kappa fam at where
  FailedContr  :: [Exists (MetaVar kappa fam)]
               -> Conflict kappa fam at
  Conflict     :: String
               -> Aligned kappa fam at
               -> Aligned kappa fam at
               -> Conflict kappa fam at
\end{code}
\end{myhs}

  Since our patches are locally scopped, the |diff3| can safely
map an auxiliary function, |mergeAl|, over the anti-unification of the 
spines of the patches being merged. The |mergeAl| function will then
receive one empty spine with an alignment inside and one non-empty
spine with alignments in its leaves. It does not particularly
matter whether the left or the right spine is empty, what matters
is that at \emph{this} location the source tree was changed
in two different ways. Our task is to reconcile them as best
as we can. 

\begin{myhs}
\begin{code}
diff3 oa ob = holesMap (uncurry' go) (lgg oa ab)
  where
    go  :: Holes kappa fam (Al kappa fam) at
        -> Holes kappa fam (Al kappa fam) at
        -> Sum (Conflict kappa fam) (Chg kappa fam) at
    go ca cb = mergeAl (alDistr ca) (alDistr cb)
\end{code}
\end{myhs}

  This approach reduces the size of the alignments that we have to
synchronize and enable us to place conflicts that are better
localized when synchronization fails, but does not simplify the 
problem conceptually. We still have to synchronize alignments 
in full generality, but let us warm up to before looking
into the definition of |mergeAl|.

  In broad strokes we can say synchronizing alignments is similar to
synchronizing |PatchST|'s, \Cref{sec:stdiff:merging}: insertions
are preserved as long as they do not happen simultaneously.
Deletions must be \emph{applied} before continuing and
copies are the identity of synchronization. The current setting,
however, does not stop there. We also have permutations and
arbitrary changes to look at. 

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
[,rootchange
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]
]
\end{myforest}
\label{fig:pepatches:merge-01:B}}%
\qquad%
\subfloat[Synchronization of |p| and |q|]{%
\begin{myforest}
[,rootchange
  [|Bin| [|Leaf| [|42|]] [y,metavar]]
  [|Bin| [y,metavar] [|Leaf| [|84|]]]
]
\end{myforest}
\label{fig:pepatches:merge-01:C}}
\caption{Example of a simple synchronization.}
\label{fig:pepatches:merge-01}
\end{figure}

  It helps to think about the metavariables in a change as
a unique identifier for a subtree in the source. If one
change changes the subtree |metavar x| into a different
subtree |k|, but the other moves |metavar x| to a different
location in the tree, the merge of these changes should be
the transport of |k| into the new location. The new location
is exactly where |metavar x| appears in the insertion context.
The example in \Cref{fig:pepatches:merge-01} illustrates this very
situation: the source tree identified by |metavar x| in
the deletion context of \Cref{fig:pepatches:merge-01:B} was
changed, by \Cref{fig:pepatches:merge-01:A}, from |Leaf 42| into
|Leaf 84|. Since |p| altered the content of a subtree, but |q|
altered its location, they are \emph{disjoint} -- they
alter different aspects of the common ancestor. Hence, the
synchronizatino is possible and results in \Cref{fig:pepatches:merge-01:C}.

  The general conducting line of our synchronization algorithm
is to record how each subtree was modified and then instantiating
these modifications in the final result. Going back to \Cref{fig:pepatches:merge-01},
we would need to merge a change |q| over a spine |p|, which means
we must match |delCtx q| against |p|. This yeilds an instantiation
of some of the variables in |delCtx q|, in this case, |metavar x| is
instantiated to |Chg (Leaf 42) (Leaf 84)|. We then proceed to split this
instantiation in two maps -- one which records what |x| \emph{was}, and
another which records what |x| \emph{became}. Namelly, |was (metavar x) = Leaf 42|
and |became (metavar x) = Leaf 84|. Finally, we instantiate |q| with
this newly discovered information yielding \Cref{fig:pepatches:merge-01:C}.

  There are some nuances to |mergeAl|, which we will be
highlighting as they appear. The first nuance, however, is that this
assignment of metavariables to how they have been changed is global
and is better taken care of by a state monad. The state we will
be carrying around consists in an instantiation of how subtrees
have changed, |iota|, and a list of equivalences of subtrees, |eqs|. 
\victor{how important is eqs, really? I feel like splitting iota
in two: |iotaIns| and |iotaDel| then using the entries in the
form |x = (Hole y)| in |iotaDel| to estabilish equivalences should work
just fine.} 

\begin{myhs}
\begin{code}
type Subst kappa fam phi = Map (Exists phi) 

data MergeState kappa fam = MergeState
  { iota :: Map (Exists (MetaVar kappa fam)) (Exists (Patch kappa fam))
  , eqs  :: Map (Exists (MetaVar kappa fam)) (Exists (HolesMV kappa fam))
  }
\end{code}
\end{myhs}

  The failures of |mergeAl| will be caught by an |Except| monad, which will 
return a simple description of the conflict. We then define |mergeAl| as
a wrapper around |mergeAlM|, which is defined in terms of the |MergeM|
monad for convenience.

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

\victor{Go into |mrgAlM| but we should make sure we can't define it in any other way}. 



\begin{figure}
\centering
\subfloat[Aligned patch, |p|.]{%
\begin{myforest}
[|Bin|   , s sep=15mm
   [Cpy]
%  [,change [x,metavar] [x,metavar]]
   [,delctx , s sep=8mm
    [|Bin| [|Leaf| [|42|]] [,sq]]
    [Cpy]
%    [,rootchange  
%       [y,metavar]
%       [y,metavar]]
]]
\end{myforest}
\label{fig:pepatches:merge-02:A}}
\subfloat[Aligned patch, |q|.]{%
\begin{myforest}
[|Bin|   % , s sep=4mm
  [|Bin| % , s sep=2mm
    [,change [a,metavar] [b,metavar]]
    [,change [b,metavar] [a,metavar]]]
  [,insctx % , s sep=8mm
    [|Bin| [,sq] [|Leaf| [|84|]]]
    [Cpy]
    % [,rootchange [c,metavar] [c,metavar]]
  ]
]
\end{myforest}
\label{fig:pepatches:merge-02:B}}%
\caption{Properly aligned version of \Cref{fig:pepatches:misalignment}.}
\label{fig:pepatches:merge-02}
\end{figure}

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

\victor{loose paragraphs below}
  We have seen how using unrestricted tree mappings, or |Chg|, makes for
a reasonable formalism for representing patches. They support a merge
operation (\Cref{sec:pepatches:merging}) and satisdy a number of algebraic properties
(\Cref{sec:pepatches:meta-theory}). The only thing left for making |Chg|
into a \emph{usable} formalism is an algorithm for efficiently computing
these objects, which is te focus of this section.

  Given two trees, |s| and |d|, we would like to compute a change |c| such
that |applyChg c s == Just d|. One obvious option would be |Chg s d|, but that
change contains no sharing whatsoever. Traditional edit-scripts based techniques
optimize for a lower cost, which usually translates to more copies. Yet, this
does not necessarily translate to high quality patches: especially when there
is more than one lowest-cost patch.

  Computing a change that transforms a source tree, |s|, into a destination
tree, |d|, consists in two phases. First we compute a \emph{sharing map}, which
contains information about which subtrees are common to both |s| and |d|. 
With that information at hand, we proceed to extracting the deletion
and insertion contexts. In general lines, the deletion context is extracted 
from |s| by substituting the common subtrees by a metavariable, whereas the
insertion context is extracted from |d|. 

  Computing changes relies almost exclusively on being able to tell
whether or not a given subtree could be shared. This is done querying
the aforementioned \emph{sharing map}. It is conceptually easy to
define and inefficient version of it -- a subtree |t| can be shared if
and only if we can find |t| in |s| and in |d|.

  Assume the existence said \emph{sharing map}, which consists of a
function |wcs s d| -- which reads as ``which common subtree'' -- with
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

  With |extract| as above, we could already produce changes from 
source |s| and destination |d| with the |chg| function below.
This |chg| function however, does \emph{not} satisfy the
criteria that |apply (chg s d) s == Just d| for all |s| and |d|,
the problem can be easily spotted by fedding a source and
a destination to |chg| such that a common subtree occurs
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
[,rootchange,
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

  There are two obvious ways to solve this problem. Either replace |metavar y|
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

  Actually, if we stop and think about how else could we extract
contexts from a source and a destination tree we might come up
with a variety of different methods. Another option is to simulate
the \unixdiff{} \texttt{--patience} option, which only copies uniquely
ocurring lines -- in our case, we would only share uniquely occuring
subtrees. In fact, to make this easy to experiment, we will parameterize
our |extract| function with which method should we use.

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
[,rootchange,
  [|Bin| [x,metavar] [k]]
  [|Bin| [x,metavar] [t]]
]
\end{myforest}
\label{fig:pepatches:extract-sol-01:nonest}}%
\qquad\qquad
\subfloat[Expand metavariables pursuing all sharing oportunities]{%
\begin{myforest}
[,rootchange,
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
        \draw [forest-digems-black,->] (A.east) [out=25, in=165]to node[midway,above]{|preprocess|} (!c.west);
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
many times we have seen a tree. We use a Patricia Tree~\cite{Okasaki1998} 
as our data structure. 

\begin{myhs}
\begin{code}
type Arity            = Int

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
and ignore the possiblity of hash collisions de to their negligible
probability. Yet, it is not hard to detect these collisions whilst
computing the arity map, but would cost precious time to compare
trees before inserting them to ensure we have not witnessed
a hash collision. 

\subsection{Extracting the Contexts}

  With an efficient ``which common subtree'' query in our toolbox,
we move on to defining the different context extraction techniques.
They are all very similar to the naive |extract| that was sketched before:
traverse the tree and each time we reach a common subtree, substitute
by its corresponding metavariable. 

  To some extent, we could compare context extraction to the translation
of tree mappings into edit-scripts: our tree mappings are given by |wcs|
and instead of edit-scripts we have terms with metavariables.
Classical algorithms are focused in computing the \emph{least cost}
edit-script from a given tree mapping. In our case, the notion of
\emph{least cost} hardly makes sense -- besides not having defined
a cost semantics to our changes, we are interested in those that
merge better which are not necessarily those that insert and delete
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
[,rootchange 
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
[,rootchange 
  [|Tri| [x,metavar]     [x,metavar] [y,metavar]]
  [|Tri| [|Bin| [b] [a]] [x,metavar] [y,metavar]]
]
\end{myforest}
\label{fig:pepatches:extraction-01:nonest}}%
\quad
\subfloat[|m = ProperShare|]{%
\begin{myforest}
[,rootchange 
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

  Computing the set of common subrtees is straight forward
and does not involve many design decisions. Deciding which
of those subtrees are eligible to be shares is an entirely
diffrent beast. We surely do not want to share all \texttt{int} 
constants throughout a file, for example. Or, we would not like
to share all variables with the same name as they might be
different variables. As a matter of fact, a good definition
of what can be shared might even be impossible without
domain-specific knowledge. We will be abstracting this
decision away by the means of the |CanShare| predicate
and will discuss the pragmatic decisions we made at
a later stage, in \Cref{sec:pepatches:discussion}.

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
extract  :: DiffMode
         -> CanShare kappa fam
         -> IsSharedMap
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
noNested1  :: CanShare kappa fam
           -> T.Trie MetavarAndArity
           -> PrepFix a kappa fam at
           -> Holes kappa fam (Const Int :*: PrepFix a kappa fam) at
noNested1 h sm x@(PrimAnn ann xi)
  = if h x  then maybe (Prim xi) (mkHole x) $$ lookup (getDigest ann) sm 
            else Prim xi
noNested1 h sm x@(SFixAnn ann xi)
  =  if h x  then maybe recurse (mkHole x) $$ lookup (getDigest ann) sm 
             else recurse
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






%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
