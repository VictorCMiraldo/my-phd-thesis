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
\begin{forest}
[,rootchange 
  [|Bin| [x,metavar] [|5|]]
  [|Bin| [x,metavar] [|6|]]
]
\end{forest}
\label{fig:pepatches:example-04:A}}%
\quad\quad\quad
\subfloat{%
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [z,metavar]]
  [|Bin| [|84|] [|Bin| [z,metavar] [z,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-04:B}}%
\caption{Example of disjoint changes.}
\label{fig:pepatches:example-04}
\end{figure}

\paragraph{Patch versus Changes.} Our current definition of change is
akin to what is known as a \emph{tree-matching} in the literature of
classical tree differencing, \Cref{sec:background:tree-edit-distance}.
Our changes are more permissive though -- since we do not want to
obtain an edit-script we do not need to enforce any of the
restrictions.  In fact, the engine of our differencing algorithm,
\Cref{sec:pepatches:diff}, will only be concerned with producing a
single |Chg| that transforms the source into the
destination. Actually, if all one wants to do with \emph{changes} is
applying them, we should go and discuss how to compute \emph{changes}
efficiently, in \Cref{sec:pepatches:diff}.

  A big part of the motivation of this thesis is in synchronizting
changes effectivelly. And this will certainly require a deeper 
understanding of changes. For example, which constructors in the deletion 
context are, in fact, just being copied over in the insertion
context. Take \Cref{fig:pepatches:example-04}, where one change operates
exclusively on the right child of a binary tree whereas the other 
alters the left child and duplicates the right child in-place. 
These changes are disjoint and should be possible to be automatically synchronizable. 
Recognizing them as such will require a more expressive type than |Chg|;
Let there be |PatchPE|.

  In the following we discuss the design space whereas in \Cref{sec:pepatches:closures}
and \Cref{sec:pepatches:alignments} we detail our choices withing de design space.

\begin{figure}
\centering
\subfloat[Insertion as a \emph{change}]{%
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [x,metavar]]
  [|Bin| [|42|] [|Bin| [|84|] [x,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-02:chg}}%
\quad\quad\quad
\subfloat[Insertion as a \emph{spined-change}]{%
\begin{forest}
[|Bin|,s sep = 5mm%make it wider
  [|42|]
  [,change [x,metavar] [|Bin| [|84|] [x,metavar]]]
]
\end{forest}
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
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [|Bin| [x,metavar] [y,metavar]]]
  [|Bin| [|42|] [|Bin| [y,metavar] [x,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-03:A}}

\subfloat[\emph{globally-scoped} swap patch]{%
\begin{forest}
[|Bin|, s sep = 5mm 
 [|42|]
 [|Bin|,s sep = 5mm%make it wider
  [,change [x,metavar] [y,metavar]]
  [,change [y,metavar] [x,metavar]]]
]
\end{forest}
\label{fig:pepatches:example-03:B}}%
\quad\quad\quad
\subfloat[\emph{locally-scoped} swap patch]{%
\begin{forest}
[|Bin|, s sep = 5mm 
 [|42|]
 [,change
  [|Bin| [x,metavar] [y,metavar]]
  [|Bin| [y,metavar] [x,metavar]]]
]
\end{forest}
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
\begin{forest}
[,rootchange , s sep=1mm
  [|Bin| [|42|] [|Bin| [x,metavar] [|Bin| [y,metavar] [z,metavar]]]]
  [|Bin| [x,metavar] [|Bin| [y,metavar] [z,metavar]]]
]
\end{forest}
\label{fig:pepatches:misalignment:A}}
\quad\quad
\subfloat[Top-down spine obscuring deletion at head.]{%
\begin{forest}
[|Bin| , s sep=-3mm
  [,change [|42|] [x,metavar]]
  [|Bin|, s sep=4mm
    [,change [x,metavar] [y,metavar]]
    [,change [|Bin| [y,metavar] [z,metavar]] [z,metavar]]]]
\end{forest}
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

  In the next subsections we shall explore a couple algorithms and
variations over the definition of changes and patches. 

\subsection{Computing Closures}
\label{sec:pepatches:closures}


\begin{figure}
\centering
\subfloat[Not minimal; |Bin| is repeated.]{%
\quad
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [x,metavar]]
  [|Bin| [|84|] [x,metavar]]
]
\end{forest}
\quad
\label{fig:pepatches:example-minimal:A}}%
\quad\quad
\subfloat[Not minimal; root constructors differ.]{%
\quad
\begin{forest}
[,rootchange 
  [|Bin| [|42|] [x,metavar]]
  [|Tri| [|42|] [x,metavar] [|84|]]
]
\end{forest}
\quad
\label{fig:pepatches:example-minimal:B}}%

\subfloat[Not minimal; change is ill-scoped.]{%
\quad
\begin{forest}
[|Bin|, s sep=5mm
  [,change [|42|] [|84|]]
  [,change [x,metavar] [y,metavar]]
]
\end{forest}
\quad
\label{fig:pepatches:example-minimal:C}}%
\quad\quad
\subfloat[Minimal change equivalent to \ref{fig:pepatches:example-minimal:A}]{%
\quad
\begin{forest}
[|Bin|, s sep=5mm
  [,change [|42|] [|84|]]
  [,change [x,metavar] [x,metavar]]
]
\end{forest}
\quad
\label{fig:pepatches:example-minimal:D}}%
\caption{Two non minimal and one miminal change.}
\label{fig:pepatches:example-minimal}
\end{figure}

%{
%format dn = "\HSVar{d_n}"
%format in = "\HSVar{i_n}"
%format dj = "\HSVar{d_j}"
%format ij = "\HSVar{i_j}"
  A change |c :: Chg kappa fam at| is said to be in \emph{minimal}
form if and only if is closed with respect to some global scope 
and either |chgDel c| and |chgIns c| have different
constructors at their root or,  they contain the same constructor and said constructor
is necessary to maintain well-scopedness. That is, when |chgDel c| and
|chgIns c| contain the same constructor, say, |inj|, we have that
|chgDel c = inj d0 dots dn| and |chgIns c = inj i0 dots in|.
If there exists a variable |v| that occurs in |ij| but is not defined in |dj|
then we cannot pull |inj| into a spine and still maintain all
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

  Given a well-scoped change |c|, we can then minimize it
by computing the least general generalization |s = lcp (chgDel c) (chdIns c)|, 
which might contain \emph{locally ill-scoped} changes, then pushing
constructors that are in the spine into the changes until they are
all in minimal form. \Cref{fig:pepatches:example-03} provides a good
illustration for this process. Computing the closure of
\Cref{fig:pepatches:example-03:A} is done by computing
\Cref{fig:pepatches:example-03:B}, then \emph{pushing} the the |Bin|
constructor down the changes, fixing their scope, resulting in
\Cref{fig:pepatches:example-03:C}.

  The |close| function, below, is responsible for pushing
constructors through the least general generalization until they
represent minimal changes. It calls an auxiliary version that receives 
the global scope and keeps track of the variables it seen so far.
The worst case scenario is when the we need \emph{all} constructors
of the spine to close the change, but if we pass a well-scoped change
change to |close|, we must be able to produce a closed change.
  
\begin{myhs}
\begin{code}
close  :: Holes kappa fam (Holes kappa fam :*: Holes kappa fam) at
       -> Holes kappa fam (Chg kappa fam) at
close h =  let global = vars h
           in case close' global (holesMap (uncurry' annWithVars) h) of
                InL _  -> error "invariant failure: h is not well-scoped."
                InR b  -> Just (holesMap body b)
\end{code}
\end{myhs}

  The |annWithVars| function computes the variables that occur in
two contexts and annotates a change with them:
  
\begin{myhs}
\begin{code}
data WithVars kappa fam at
  = WithVars  { decls  :: Map Int Arity
              , uses   :: Map Int Arity
              , body   :: Chg kappa fam x
              }

annWithVars :: (Holes kappa fam :*: Holes kappa fam) at -> WithVars kappa fam at
annWithVars (d :*: i) = WithVars (vars d) (vars i) (Chg d i)
\end{code}
\end{myhs}
  
  The |close'| function, shown in its entirety in \Cref{dif:pepatches:close-aux},
receveies a spine with |WithVars| and returns that very spine if
all its children are already closed or a |WithVars|, indicating
some children are not yet closed. 

\begin{figure}
\begin{myhs}
\begin{code}
close'  :: M.Map Int Arity
         -> Holes kappa fam (ChgVars kappa fam) at
         -> Sum (ChgVars kappa fam) (Holes kappa fam (ChgVars kappa fam)) at 
close' _  (Prim x)  = InR (Prim x)
close' gl (Hole cv)
  | isClosed gl (decls cv) (uses cv) = InR (Hole cv)
  | otherwise   = InL cv
close' gl (Roll x) =
  let aux = repMap (close' gl) x
   in case repMapM fromInR aux of
        Just res -> InR (Roll res)
        Nothing  ->
          -- Distributing closed changes yields closed changes;
          let chgs = repMap (either' InL (InR . chgVarsDistr)) aux
              cD   = Roll $$ repMap (codelta (chgDel . body)) chgs
              cI   = Roll $$ repMap (codelta (chgIns . body)) chgs
              dels = repLeaves (codelta decls) (M.unionWith (+)) M.empty chgs
              inss = repLeaves (codelta uses)  (M.unionWith (+)) M.empty chgs
           in if isClosed gl dels inss
              then InR (Hole (ChgVars dels inss (Chg cD cI)))
              else InL (ChgVars dels inss (Chg cD cI))
\end{code}
\end{myhs}
\caption{The |close'| auxiliar function}
\label{fig:pepatches:close-aux}
\end{figure}

\subsection{Aligning Closed Changes}
\label{sec:pepatches:alignments}

  So far we have placed some conern over the scope of changes, that is,
which constructors constitute the spine, which inform us about where
the changes actually occur.



\subsection{Meta Theory}


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

\victor{Best mereg rate so far is:
\texttt{hdiff merge -d nonest -k spine *.java}
with 900 successes (and 500 merge diffs); check commit \texttt{11aebdf9cf0b57b97734ede0285c7df8d4dfe28a}
on hdiff to reproduce}

\section{Computing Changes}
\label{sec:pepatches:diff}

\begin{figure}
\centering
\subfloat[|DM_NoNest| extraction]{%
\begin{forest}
[|Bin|, s sep=5mm 
  [,change [x,metavar] [x,metavar]]
  [,change [k] [t]]
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
