  The \texttt{gdiff}~\cite{Lempsink2009} approach, discussed
in \Cref{sec:gp:well-typed-tree-diff}, which flattens a
tree into a list, following classical tree edit distance algorithms
encoded through using type-safe edit-scripts, inherits the problems of
edit-script based approaches. These include ambiguity on the
representation of patches, non-uniqueness of optimal solutions and
difficulty of merging. The \texttt{stdiff} approach, discussed
through this chapter, arose from our study of the difficulties
about merging \texttt{gdiff} patches~\cite{Vassena2016}.

  The heterogeneity of |PatchGDiff| makes merging difficult.
Recall that a value of type |PatchGDiff xs ys| transforms a list of trees |xs| into
a list of trees |ys|.  If we are given two patches |PatchGDiff xs ys|
and |PatchGDiff xs zs|, we would like to produce two patches
|PatchGDiff ys rs| and |PatchGDiff zs rs| such that the canonical
merge square commutes. The problem becomes clear when we try to determine |rs| correctly:
sometimes such |rs| might not even exist~\cite{Vassena2016}.

  Our \texttt{stdiff} approach, or, \emph{structural patches}, marks
our first attempt at defining a \emph{type-indexes} patch datatype, |PatchST|,
in pursuit of better behaved merge algorithms. The overall idea consists
in making sure that the type of patches is also \emph{tree structured}, as
opposed to managing a list-like patch data structure that is supposed to
operate over tree structured data. As it turns out, it is not possible to
have fully homogeneous patches, but we were able to identify homogeneous
parts of our patches which we can use to synchronize changes when
defining our merge operation, but let us not get ahead of ourselves.

  \emph{Structural Patches} differ from edit-scripts by using
tree-shaped, homogeneous patch -- a patch transforms two values of the same
type.  The edit operations themselves are analogous to edit
scripts, we support insertions, deletions and copies, but these are
structured to follow the sums-of-products of datatypes: there is one
way of changing sums, one way of changing products and one way of
changing the recursive positions of a value. For example, consider the
following trees:

\begin{myhs}
\begin{code}
t1 = Bin  (Tri a   b c)  d
t2 = Bin  (Bin a'  b)    (Bin d e)
\end{code}
\end{myhs}

  These are the trees that are depicted in \Cref{fig:stdiff:patch0-a}
and \Cref{fig:stdiff:patch0-b} respectively. How should we represent
the transformation mapping |t1| into |t2|? Traversing the trees from
their roots, we see that on the outermost level they both consist of a
|Bin|, yet the fields of the source and destination nodes are
different: the first field changes from a |Bin| to a |Tri|, which
requires us to reconcile the list of fields |[a, b, c]| into |[a' , b]|.
Which can be done by the means of an edit-script. The second field, however,
witnesses a change in the recursive structure of the type. We see that
we have inserted new information, namely |(Bin SQ e)|. After inserting
this \emph{context}, we simply copy |d| from the source to the destination.
This transformation has been sketched graphically in \Cref{fig:stdiff:patch0-c},
and showcases all the necessary pieces we will need to write a general
encoding of transformations between objects that support insertions, deletions
and copies.

\todo{make subtrees triangles}
\begin{figure}
\centering
\subfloat[Source, |t1|]{%
\begin{forest}
[ |Bin| [ |Tri| [a] [b] [c]] [d]]
\end{forest}\quad
\label{fig:stdiff:patch0-a}}%
\qquad
\subfloat[Destination, |t2|]{%
\begin{forest}
[ |Bin| [ |Bin| [a'] [b] ] [|Bin| [d] [e]] ]
\end{forest}
\label{fig:stdiff:patch0-b}}%
\qquad
\subfloat[Graphical Representation of a patch that transforms |t1| into |t2|]{%
%{
%format TO a b = "{" a "}\mathbin{\HS{\mapsto}}{" b "}"
%format Cpy a  = "\HS{=}{" a "}"
%format Ins a  = "\HS{+}{" a "}"
%format Del a  = "\HS{-}{" a "}"
\begin{forest}
[|Cpy Bin|
  [|TO Tri Bin|
    [|TO a a'|]
    [|Cpy b|]
    [|Del c|]]
  [|Ins (Bin SQ e)| [|Cpy d|]]]
\end{forest}}
\caption{Graphical representation of a simple transformation. Copies, insertinos
and deletions around the tree are represented with |Cpy|, |Ins| and |Del| respectively.
Modifications are denoted |TO|.}
%}
\label{fig:stdiff:patch0}
\end{figure}

\victor{How about this little next parargaph?}

  At a glance, the \texttt{stdiff} approach to differencing is a different
way of representing edit-scripts to follow the shape of the datatype in question.
We advance that the approach from \Cref{chap:pattern-expression-patches} supersedes
this approach in all aspects, consequently, we invide the reader who is
interested in understanding methods that work to jump directly
to \Cref{chap:pattern-expression-patches}.

  To write the \texttt{stdiff} algorithms in Haskell, we must rely on
the \texttt{generics-mrsop} library (\Cref{sec:gp:mrsop}) as our
generic programming workhorse for two reasons. First, we do require
the concept of explicit sums of products in the very definition of
|PatchST x|. Secondly, we need \texttt{gdiff}'s assistance in
computing patches (\Cref{sec:stdiff:oraclesenum}) and \texttt{gdiff}
also requires, to a lesser extent, sums of products structured
datatypes, hence is easily written with \texttt{generics-mrsop}, as
seen in \Cref{sec:gp:well-typed-tree-diff}.

  The contributions in this chapter arise from joint work
with Pierre-Evariste Dagand, published in TyDe 2017~\cite{Miraldo2017} and
coded in Agda~\cite{Norell2008}\href{https://github.com/VictorCMiraldo/stdiff}{Agda
repository}%
\footnote{https://github.com/VictorCMiraldo/stdiff}.
Later, we collaborated closely with a MSc student, Arian van Putten, in translating
the Agda code to Haskell, extending its scope to mutually recursive
datatypes. The code presented here, however, is loosely based on van
Putten's translation of our Agda repository to Haskell as part of his
Master thesis work~\cite{Putten2019}.  We chose to present all of our
work in a single programming language to keep the thesis consistent
throughout.

  In this chapter we will delve into the construction of |PatchST| and its
respective components. Firstly, we familiarize ourselves with |PatchST|
and is application function, \Cref{sec:stdiff:patches}. Next we look into
merging and its cummutativity proof in \Cref{sec:stdiff:merging}. Lastly,
we discuss the |diff| function in \Cref{sec:stdiff:diff}, which comprises
a significant drawback of the \texttt{stdiff} approach for its computational 
complexity.

\section{The Type of Patches}
\label{sec:stdiff:patches}

  Next we look at the |PatchST| type, starting with
a single layer of datatype, \ie, a single application of the datatypes pattern functor.
Later, in \Cref{sec:stdiff:diff:fixpoints} we extend this treatment to recursive datatypes,
essentially by taking the fixpoint of the constructions in \Cref{sec:stdiff:diff:functors}.
The \texttt{generics-mrsop} library (\Cref{chap:generic-programming})
will be used throughout the exposition.

  Recall that a datatype, when seen through its initial
algebra~\cite{initial-algebra} semantics, can be seen as an infinite
succession of applications of its pattern functor, call it $F$, to
itself: $\mu F = F (\mu F)$. The |PatchST| type will describe the differences
between values of $\mu F$ by successively applying the description of differences between
values of type $F$, closely following the initial algebra semantics of
datatypes.

\subsection*{Functorial Patches}
\label{sec:stdiff:diff:functor}

  Handling \emph{one layer} of recursion is done by addressing the possible
changes at the sum level, followed by some reconciliation at the product
level when needed.

  The first part of our algorithm handles the \emph{sums} of the
universe. Given two values, |x| and |y|, it computes the
\emph{spine}, capturing the largest
common coproduct structure. We distinguish three possible cases:
%
\begin{itemize}
\item |x| and |y| are fully equal, in which case we copy the full
  values regardless of their contents. They must also be of the same type.
%
\item |x| and |y| have the same constructor -- i.e., |x =
  inj c px| and |y = inj c py| -- but some subtrees of |x|
  and |y| are distinct, in which case we copy the head constructor and
  handle all arguments pairwise.
%
\item |x| and |y| have distinct constructors, in which case we record
  a change in constructor and a choice of the alignment of the
  source and destination's constructor fields. Here, |x| and |y|
  might be of a different type in the family.
\end{itemize}

  The datatype |Spine|, defined below, formalizes this
description. The three cases we describe above correspond to the three
constructors of |Spine|. When two values are not equal, we need to
represent the differences somehow. If the values have the same
constructor we need to reconcile the fields of
that constructor whereas if the values have different constructors
we need to reconcile the products that make the fields of the constructors.
We index the datatype |Spine| by the sum codes it operates over
because we need to lookup the fields of the constructors
that have changed, and \emph{align} them in the case of |SChg|.
Alignments will be introduced shortly, for the time being,
let us continue to focus on spines. Intuitively, Spines act on sums and capture
the ``largest shared coproduct structure'':

\begin{myhs}
\begin{code}
data Spine  (kappa :: kon -> Star) (codes :: [[[Atom kon]]])
            :: [[Atom kon]] -> [[Atom kon]] -> Star where
  Scp   :: Spine kappa codes s1 s1
  SCns  :: Constr s1 c1 -> NP (At kappa codes) (Lkup c1 s1)
        -> Spine kappa codes s1 s1
  SChg  :: Constr s1 c1 -> Constr s2 c2 -> Al kappa codes (Lkup c1 s1) (Lkup c2 s2)
        -> Spine kappa codes s1 s2
\end{code}
\end{myhs}

  Our Agda model~\cite{Miraldo2017} handles
only regular types, or, mutually recursive families consisting of
a single datatype.  Hence, the |Spine| type would arise naturally as a homogeneous
type. While extending the Agda model to a full fledged Haskell
implementation, together with Van Putten~\cite{Putten2019}, we noted
how this would severely limit the number of potential copy
opportunities throughout patches. For example, imagine we want to
patch the following values:

\begin{myhs}
\begin{code}
data TA = TA X Y Z | TAB TB
data TB = TB X Y Z | TBA TA

diff (TA x1 y1 z1) (TB x2 y2 z2) = SChg TA TB ...
\end{code}
\end{myhs}

  With a fully homogeneous |Spine| type, our only option is
to delete |TA|, then insert |TB| at the \emph{recursion} layer
 (\ref{sec:stdiff:diff:fixpoint})
This would be unsatisfactory as it only allows copying of one of the fields,
where \texttt{gdiff} would be able to copy more fields for it does not
care about the recursive structure.

  The semantics of |Spine| are straightforward, but before continuing
with |applySpine|, a short technical interlude is necessary. The
|testEquality|, below, is used to compare the type
indices for propositional equality. It comes from |Data.Type.Equality|
and has type |f a -> f b -> Maybe (a :~: b)|. Also note that we must
pass two |SNat| arguments to disambiguate the |ix| and |iy| type
variables. Without those arguments, these variables would only appear
as an argument to a type family, which may not be injective and would
trigger a type error.  This solution of using the |SNat|
singleton~\cite{Eisenberg2012} is the standard Haskell type-level
programming workaround to this problem.

\begin{myhs}
\begin{code}
data SNat :: Nat -> Star where
  SZ  ::            SNat  (P Z)
  SS  :: SNat n ->  SNat  ((P S) n)
\end{code}
\end{myhs}

  The |applySpine| function is given by
checking the provided value is made up with the required
constructor. In the |SCns| case we we must ensure that type indices
match -- for Haskell type families may not be injective -- then simply
map over the fields with the |applyAt| function, which applies changes
to atoms.  Otherwise, we reconcile the fields with the |applyAl|
function, whose definition follow shortly.

\begin{myhs}
\begin{code}
applySpine  :: (EqHO kappa) -> SNat ix -> SNat iy
            -> Spine kappa codes (Lkup ix codes) (Lkup iy codes)
            -> Rep kappa (Fix kappa codes) (Lkup ix codes)
            -> Maybe (Rep kappa (Fix kappa codes) (Lkup iy codes))
applySpine _ _ Scp x = return x
applySpine ix iy (SCns c1 dxs) (sop -> Tag c2 xs) =  do
  Refl <- testEquality ix iy
  Refl <- testEquality c1 c2
  inj c2 <$$> (mapNPM applyAt (zipNP dxs xs))
applySpine _ _ (SChg c1 c2 al) (sop -> Tag c3 xs) = do
  Refl <- testEquality' c1 c3
  inj c2 <$$> applyAl al xs
\end{code}
\end{myhs}

  The |Spine| datatype and |applySpine| are responsible for matching the
\emph{constructors} of two trees, but we still need to determine how to
continue representing the difference in the products of data stored therein.
At this stage in our construction, we are given two heterogeneous lists, corresponding
to the fields associated with two distinct constructors. As a result,
these lists need not have the same length nor store values of the same
type. To do so, we need to decide how to line up the constructor
fields of the source and destination. We shall refer to the process of
reconciling the lists of constructor fields as solving an
\emph{alignment} problem.

  Finding a suitable alignment between two lists of constructor fields
amounts to finding a suitable \emph{edit-script}, that relates source
fields to destination fields. The |Al| datatype below describes such
edit-scripts for a heterogeneously typed list of atoms. These scripts
may insert fields in the destination (|Ains|), delete fields from the
source (|Adel|), or associate two fields from both lists (|AX|).

\begin{myhs}
\begin{code}
data Al  (kappa :: kon -> Star) (codes :: [[[Atom kon]]])
         :: [Atom kon] -> [Atom kon] -> Star where
  A0    :: Al kappa codes (P []) (P [])
  AX    :: At kappa codes x -> Al kappa codes xs ys
        -> Al kappa codes (x Pcons xs)  (x Pcons ys)
  ADel  :: NA kappa (Fix kappa codes) x -> Al kappa codes xs ys
        -> Al kappa codes (x Pcons xs) ys
  AIns  :: NA kappa (Fix kappa codes) x -> Al kappa codes xs ys
        -> Al kappa codes xs (x Pcons ys)
\end{code}
\end{myhs}

  We require alignments to preserve the order of the arguments of each
constructor, thus forbidding permutations of arguments. In effect,
the datatype of alignments can be viewed as an intentional
representation of (partial) \emph{order and type preserving maps},
along the lines of McBride's order preserving
embeddings~\cite{McBride2005}, mapping source fields to destination
fields. This makes sure that our patches also give rise to tree
mappings (\Cref{sec:background:tree-edit-distance}) in the classical
tree-edit distance sense.

  Provided a partial embedding for atoms, we can therefore interpret
alignments into a function transporting the source fields over to the
corresponding destination fields, failure potentially occurring when
trying to associate incompatible atoms. Recall |(:*)| and
|NP0| are the constructors of type |NP|:

\begin{myhs}
\begin{code}
applyAl  :: (EqHO kappa)
         => Al kappa codes xs ys
         -> PoA kappa (Fix kappa codes) xs
         -> Maybe (PoA kappa (Fix kappa codes) ys)
applyAl A0                NP0         = return NP0
applyAl (AX    dx  dxs)   (x :*  xs)  = (:*)    <$$> applyAt (dx :*: x) <*> applyAl dxs xs
applyAl (AIns  x   dxs)          xs   = (x :*)  <$$> applyAl dxs xs
applyAl (ADel  x   dxs)   (y :*  xs)  = guard (eq1 x y) *> applyAl dxs xs
\end{code}
\end{myhs}

  Finally, when synchronizing atoms we must distinguish between a recursive position
or opaque data. In case of opaque data, we simply record the old value and the new value.

\begin{myhs}
\begin{code}
data TrivialK (kappa :: kon -> Star) :: kon -> Star where
  Trivial :: kappa kon -> kappa kon -> TrivialK kappa kon
\end{code}
\end{myhs}

  In case we are at a recursive position, we record a potential change in
the recursive position with |Almu|, which we will get to shortly.

\begin{myhs}
\begin{code}
data At  (kappa :: kon -> Star) (codes :: [[[Atom kon]]])
         :: Atom kon -> Star where
  AtSet  :: TrivialK kappa kon -> At kappa codes ((P K kon))
  AtFix  :: (IsNat ix)
         => Almu kappa codes ix ix -> At kappa codes ((P I ix))
\end{code}
\end{myhs}

  The application function for atoms follows the same structure. In
case we are applying a patch to an opaque type, we must understand
whether said patch represents a copy, \ie, the source and destination
values are the same. If that is the case, we simply copy the provided
value. Otherwise, we must ensure the provided value matches the source
value. The recursive position case is directly handled by the
|applyAlmu| function.

\begin{myhs}
\begin{code}
applyAt  :: EqHO ki
         => At kappa codes at
         -> NA kappa (Fix kappa codes)) at
         -> Maybe (NA kappa (Fix kappa codes) at)
applyAt (AtSet (Trivial x y)) (NA_K a)
  | eqHO x y   = Just (NA_K a)
  | eqHO x a   = Just (NA_K b)
  | otherwise  = Nothing
applyAt (AtFix px) (NA_I x) = NA_I <$$> applyAlmu px x
\end{code}
\end{myhs}

  The last step is to address how to make changes over the
recursive structure of our value, defining |Almu| and |applyAlmu|,
which will be our next concern.

\subsection*{Recursive Changes}
\label{sec:stdiff:diff:fixpoint}

  In the previous section, we presented patches describing changes to
the coproducts, products, and atoms of our \emph{SoP} universe. This
treatment handled just a single layer of the fixpoint construction. In
this section, we tie the knot and define patches describing changes to
arbitrary \emph{recursive} datatypes.

  To represent generic patches on values of |Fix codes ix|, we will define
two mutually recursive datatypes |Almu| and |Ctx|. The semantics of
both these datatypes will be given by defining how to \emph{apply}
them to arbitrary values:

\begin{itemize}
\item Much like alignments for products, a similar phenomenon appears
  at fixpoints. When comparing two recursive structures, we can
  insert, remove or modify constructors. Since we are working over mutually
  recursive families, removing or inserting constructors can change the
  overall type. We will use |Almu ix iy| to
  specify these edit-scripts at the constructor-level, describing a transformation
  from |Fix codes ix| to |Fix codes iy|.

\item Whenever we choose to insert or delete a recursive subtree, we
  must specify \emph{where} this modification takes place.  To do so,
  we will define a new type |Ctx dots :: P [Atom kon] -> Star|, inspired by
  zippers~\cite{Huet1997,McBride2001}, to navigate through our data-structures. A
  value of type |Ctx dots p| selects a single atom |I| from the product of type
  |p|.
\end{itemize}

Modeling changes over fixpoints closely follows our definition of
alignments of products.  Instead of inserting and deleting elements of
the product we insert, delete or modify \emph{constructors}. Our
previous definition of spines merely matched the constructors of the
source and destination values -- but never introduced or removed
them. It is precisely these operations that we must account for here.

\begin{myhs}
\begin{code}
data Almu  (kappa :: kon -> Star) (codes :: [[[Atom kon]]])
           :: Nat -> Nat -> Star where
  Spn  :: Spine kappa codes (Lkup ix codes) (Lkup iy codes)
       -> Almu kappa codes ix iy
  Ins  :: Constr (Lkup iy codes) c
       -> InsCtx kappa codes ix (Lkup c (Lkup iy codes))
       -> Almu kappa codes ix iy
  Del  :: Constr (Lkup ix codes) c
       -> DelCtx kappa codes iy (Lkup c (Lkup ix codes))
       -> Almu kappa codes ix iy
\end{code}
\end{myhs}

The first constructor, |Spn|, does not perform any new insertions and
deletions, but instead records a spine and an alignment of the
underlying product structure. This closely follows the patches we have
seen in the previous section. To insert a new constructor, |Ins|,
requires two pieces of information: a choice of the new constructor to
be introduced, called |c|, and the fields associated with that
constructor. Note that we only need to record \emph{all but one} of
the constructor's fields, as represented by a value of type |InsCtx
ki codes ix (Lkup c (Lkup iy codes))|. Deleting a constructor
is analogous to insertions, with |InsCtx| and |DelCtx| being
slight variations over |Ctx|, where one actually flips the arguments
to ensure the transformation is on the right direction.

\begin{myhs}
\begin{code}
type InsCtx kappa codes  = Ctx kappa codes        (Almu kappa codes)
type DelCtx kappa codes  = Ctx kappa codes (Flip  (Almu kappa codes))

newtype Flip f ix iy = Flip { unFlip :: f iy ix }
\end{code}
\end{myhs}

Our definition of insertion and deletions relies on identifying
\emph{one} recursive argument among the product of possibilities. To
model this accurately, we define an indexed zipper to identify a
recursive atom (indicated by a value of type |I|) within a product of
atoms.  Conversely, upon deleting a constructor from the source
structure, we exploit |Ctx| to indicate find the subtree that should
be used for the remainder of the patch application, discarding all
other constructor fields. We parameterize the |Ctx| type
with a |Nat -> Nat -> Star| argument to distinguish between these
two cases, as seen above.

\begin{myhs}
\begin{code}
data Ctx (kappa :: kon -> Star) (codes :: [[[Atom kon]]]) (p :: Nat -> Nat -> Star)
         (ix :: Nat) :: [Atom kon] -> Star where
  H  :: IsNat iy
     => p ix iy
     -> PoA kappa (Fix kappa codes) xs
     -> Ctx kappa codes p ix ((P I iy) Pcons xs)
  T  :: NA kappa (Fix kappa codes) a
     -> Ctx kappa codes p ix xs
     -> Ctx kappa codes p ix (a Pcons xs)
\end{code}
\end{myhs}

  Consequently, we will have two application functions for contexts,
one that inserts and one that removes contexts. This makes
clear the need to flip the type indexes of |Almu| when defining
|DelCtx|. Inserting a context is done by receiving a tree and
returning the product stored in the context with the distinguished
field applied to the received tree:

\begin{myhs}
\begin{code}
insCtx  :: (IsNat ix, EqHO kappa)
        => InsCtx kappa codes ix xs
        -> Fix kappa codes ix
        -> Maybe (PoA kappa (Fix kappa codes) xs)
insCtx (H x rest) v  = (:* rest) . NA_I  <$$> applyAlmu x v
insCtx (T a ctx)  v  = (a :*)            <$$> insCtx ctx v
\end{code}
\end{myhs}

  The deletion function discards any information we have about all the
constructor fields, except for the subtree used to continue the patch
application process. This is a consequence of our design decision, at the time,
of having application functions as permissive as possible.
Intuitively, the deletion context identifies the only field that
should not be deleted. By not checking whether the elements
we are applying to match the ones that should be deleted, we get
an application function that applies to more elements for free.

\begin{myhs}
\begin{code}
delCtx  :: (IsNat ix, EqHO kappa)
        => DelCtx kappa codes ix xs
        -> PoA kappa (Fix kappa codes) xs
        -> Maybe (Fix kappa codes ix)
delCtx (H x rest)  (NA_I v  :* p) = applyAlmu (unFlip x) v
delCtx (T a ctx)   (at      :* p) = delCtx ctx p
\end{code}
\end{myhs}

  Finally, the application function for |Almu| is
nothing but selecting whether we should use the spine
functionality or insertion and deletion of a context.

\begin{myhs}
\begin{code}
applyAlmu  :: (IsNat ix, IsNat iy, EqHO kappa)
           => Almu kappa codes ix iy
           -> Fix kappa codes ix
           -> Maybe (Fix kappa codes iy)
applyAlmu (Spn sp)      (Fix rep)  = Fix <$$> applySpine _ _ spine rep
applyAlmu (Ins  c ctx)  (Fix rep)  = Fix . inj c <$$> insCtx ctx f
applyAlmu (Del  c ctx)  (Fix rep)  = delCtx ctx <$$> match c rep
\end{code}
\end{myhs}

  The two underscores at the |Spn| case are just an extraction of
the necessary singletons to make the |applySpine| typecheck. These
can be easily replaced by |getSNat| with the correct proxies.

\begin{myhs}
\begin{code}
type PatchST kappa codes ix = Almu kappa codes ix ix

applyST  :: (IsNat ix , EqHO kappa) => PatchST kappa codes ix -> Fix codes ix
         -> Maybe (Fix codes ix)
applyST  = applyAlmu
\end{code}
\end{myhs}

  An easily overlooked property of our patch definition is that the
destination values it computes are guaranteed to be type-correct \emph{by
construction}. This is unlike the line-based or untyped approaches
(which may generate ill-formed values) and similar to earlier
results on type-safe differences~\cite{Lempsink2009}.

\section{Merging Patches}
\label{sec:stdiff:merging}

  The patches encoded in the |PatchST| type clearly identify
a prefix of constructors copied from the root of a tree up until the
location of the changes and any insertion or deletions that might happen
along the way. Moreover, since these patches also mirror the tree structure
of the data in question, it becomes quite natural to identify separate changes.
For example, if one change works on the left subtree of the root, and another
on the right, they are clearly disjoint and can be merged. Finally,
the explicit representation of insertions and deletions at the
fixpoint level gives us a simple global alignment for our synchronizer.

  In this section we discuss a simple merging algorithm,
which reconciles changes from two different patches whenever these
are \emph{non-interfering}, for example, as
in \Cref{fig:stdiff:merging0}. We call non-interfering patches
\emph{disjoint}, as they operate on separate parts of a tree.

\begin{figure}
\centering
Draw a simple example of mergeable patches here
\caption{A simple example of mergeable patches.}
\label{fig:stdiff:merging0}
\end{figure}

  A positive aspect of the |PatchST| approach in comparison with
a purely edit-scripts based approach is the significantly
simpler merge function. This is due to |PatchST| being having clear
homogeneous sections. Consequently, the type of the merge function is simple
and reflects the fact that we expect a patch that operates over
the values of the same type as a result:

\begin{myhs}
\begin{code}
merge :: PatchST kappa codes ix -> PatchST kappa codes ix -> Maybe (PatchST kappa codes ix)
\end{code}
\end{myhs}

  A call to |merge|, in Haskell, returns |Nothing| if the patches have non-disjoint changes,
that is, if both patches want to change the \emph{same part} of the source tree.

%{
%option agda
  Prior to prototyping \texttt{stdiff} in Haskell, we already had a working model
of \texttt{stdiff} in Agda~\cite{Miraldo2017}, which was created with the goal of proving
that the merging algorithm would respect locality. In our Agda model, we have divided
the merge function and the notion of disjointness, which yields a total merge function
for the subset of disjoint patches:

\begin{myhs}
\begin{code}
merge : (p q : Patch kappa codes ix) -> Disjoint p q -> Patch kappa codes ix
\end{code}
\end{myhs}

  A value of type |Disjoint p q| corresponds to a proof that |p|
and |q| change different parts of the source tree and is a symmetric relation --
that is, |Disjoint p q| iff |Disjoint q p|. This separation makes reasoning about
the merge function much easier. In fact, we have proven that the merge function
over regular datatypes commutes. A simplified statement of our theorem
is given below:

%format mergecommutes = "\HVNI{\hbox{\it merge-{\hskip-0.3em}-commutes}}"
\begin{myhs}
\begin{code}
mergecommutes  :   (p q : Patch kappa codes ix)
               ->  (hyp : Disjoint p q)
               ->  apply (merge p q hyp) . q == apply (merge q p (sym hyp)) . p
\end{code}
\end{myhs}

  It is also worth noting that encoding the |merge| to be applied to the
divergent replicas instead of the common ancestor -- \emph{residual-like} approach
to merging,\Cref{sec:background:synchronizing-changes} -- is instrumental to
write a concise property and, consequently, prove the result. A merge
function that applies to the common ancestor would probably require a
much more convoluted encoding of |mergecommutes| above.

%}

  In a Haskell development, however, it is simpler to rely on the
|Maybe| monad for disjointness.  In fact, we define disjointness
as whether or not merge returns a |Just|:

\begin{myhs}
\begin{code}
disjoint :: Patch kappa codes ix -> Patch kappa codes ix -> Bool
disjoint p q = maybe (const True) False (merge p q)
\end{code}
\end{myhs}

  The definition of the |merge| function is given in its entirety in
\Cref{fig:stdiff:mergest}, but we discuss some interesting cases
inline next.  For example, when one change deletes a constructor
but the other performs a change within said constructor we must
check that they operate over \emph{the same} constructor. When that
is the case, we must go ahead and ensure the deletion context, |ctx|,
and the changes in the product of atoms, |at|, are compatible.

\begin{myhs}
\begin{code}
merge (Del c1 ctx) (Spn (SCns c2 at)) = testEquality c1 c2 >>= \Refl -> mergeCtxAt ctx at
\end{code}
\end{myhs}

  A (deletion) context is disjoint from a list of atoms if the patch in
the hole of the context returns the same type of element than the patch
on the product of patches and they are both disjoint. Moreover, the rest
of the product of patches must consist in identity patches. Otherwise, we risk
deleting newly introduced information.

\begin{myhs}
\begin{code}
mergeCtxAt  :: DelCtx kappa codes iy xs -> NP (At kappa codes) xs -> Maybe (Almu kappa codes ix iy)
mergeCtxAt (H (AlmuMin almu') rest) (AtFix almu :* xs) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- mergeAlmu almu' almu
  guard (and $ elimNP identityAt xs)
  pure x
mergeCtxAt (T at ctx) (x :* xs) = guard (identityAt x) >> mergeCtxAt ctx xs
\end{code} %$
\end{myhs}

  The |testEquality| is there to ensure the patches to be merged are producing
the same element of the mutually recursive family. This is one of the two
places where we need these checks when adapting our Agda model to work
over mutually recursive types. The second adaptation is shown shortly.

  The |mergeAtCtx| function, dual to |mergeCtxAt|, merges a
|NP (At kappa codes) xs| and a |DelCtx kappa codes iy xs| into a |Maybe
(DelCtx kappa codes iy xs)|, essentially preserving the |T at| it finds on
the recursive calls.  Another interesting case happens on one of the
|mergeSpine| cases, whose full implementation can be seen in
\Cref{fig:stdiff:mergespine}.  The |SChg| over |SCns| case must ensure
we are working over the same element of the mutually recursive family,
with a |testEquality ix iy|.  This is the second place where we need
to adapt the code in the Agda repository to work over mutually
recursive types.

\begin{myhs}
\begin{code}
mergeSpine  :: SNat ix -> SNat iy
            -> Spine kappa codes (Lkup ix codes) (Lkup iy codes)
            -> Spine kappa codes (Lkup ix codes) (Lkup iy codes)
            -> Maybe (Spine kappa codes (Lkup ix codes) (Lkup iy codes))
mergeSpine ix iy (SChg cx cy al) (SCns cz zs)  = do  Refl <- testEquality ix iy
                                                     Refl <- testEquality cx cz
                                                     SCns cy <$$> mergeAlAt al zs
\end{code}
\end{myhs}

\begin{figure}
\begin{myhs}
\begin{code}
-- Non-disjoint recursive spines:
merge (Ins _ _)            (Ins _ _)           = Nothing
merge (Spn (SChg _ _ _))   (Del _ _)           = Nothing
merge (Del _ _)            (Spn (Schg _ _ _))  = Nothing
merge (Del _ _)            (Del _ _)           = Nothing

-- Obviously disjoint recursive spines:
merge (Spn Scp)            (Del c2 s2) = Just (Del c2 s2)
merge (Del c1 s2)          (Spn Scp)   = Just (Spn Scp)

-- Spines might be disjoint from spines and deletions:
merge (Spn s1)             (Spn s2)
  = Spn <$$> mergeSpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) s1 s2

merge (Spn (SCns c1 at1))  (Del c2 s2)
  = Del c1 <$$> mergeAtCtx at1 s2

merge (Del c1 s1)          (Spn (SCns c2 at2))
  = do  Refl <- testEquality c1 c2 -- disjoint if same constructor
        mergeCtxAt s1 at2

-- Insertions are disjoint from anything except insertions.
-- Overall disjointness does depend on the recursive parts, though.
merge (Ins c1 s1)  (Spn s2)     = Spn . SCns c1  <$$> mergeCtxAlmu s1 (Spn s2)
merge (Ins c1 s1)  (Del c2 s2)  = Spn . SCns c1  <$$> mergeCtxAlmu s1 (Del c2 s2)

merge (Spn s1)     (Ins c2 s2)  = Ins c2         <$$> (mergeAlmuCtx (Spn s1) s2)
merge (Del c1 s1)  (Ins c2 s2)  = Ins c2         <$$> (mergeAlmuCtx (Del c1 s1) s2)
\end{code}
\end{myhs}
\caption{Definition of |merge|}
\label{fig:stdiff:mergest}
\end{figure}

\begin{figure}
\begin{myhs}
\begin{code}
-- Non-disjoint spines:
mergeSpine _ _ (SChg _ _ _)       (SChg _ _ _)  = Nothing

-- Obviously disjoint spines:
mergeSpine _ _ Scp                s             = Just s
mergeSpine _ _ s                  Scp           = Just Scp

-- Disjointness depends on recursive parts:
mergeSpine _ _ (SCns cx xs) (SCns cy ys)       = do  Refl <- testEquality cx cy
                                                     SCns cx <$$> mergeAts xs ys

mergeSpine _ _ (SCns cx xs)  (SChg cy cz al)   = do  Refl <- testEquality cx cy
                                                     SChg cy cz <$$> mergeAtAl xs al

mergeSpine ix iy (SChg cx cy al) (SCns cz zs)  = do  Refl <- testEquality ix iy
                                                     Refl <- testEquality cx cz
                                                     SCns cy <$$> mergeAlAt al zs
\end{code} %$
\end{myhs}
\caption{Definition of |mergeSpine|}
\label{fig:stdiff:mergespine}
\end{figure}

\section{Computing |PatchST|}
\label{sec:stdiff:diff}

  In the previous sections, we have devised a typed representation for
differences. We have seen that this representation is interesting in
and by itself: being richly-structured and typed, it can be thought of
as a non-trivial programming language whose denotation is given by the
application function. Moreover, we have seen how to
merge two disjoint differences. However, as programmers, we are mainly
interested in \emph{computing} patches from a source and a
destination. Unfortunately, however, this is where the good news
stops. Computing a value of type |PatchST| is computationally expensive
and represents one of the main downsides of this approach.

  In this section we explore our attempts at
computing differences with the \texttt{stdiff} framework.
We start by outlining a nondeterministic specification
of an algorithm for computing a |PatchST|, in \Cref{sec:stdiff:naiveenum}.
We then provide example algorithms that implemented said specification
in \Cref{sec:stdiff:oraclesenum}. All these approaches
however, we will always need to make choices. Moreover, the rich structure
of |PatchST| makes a memoized algorithm much more difficult to
be written. Consequently, computing a |PatchST|
will always be a computationally inefficient process, rendering
it unusuable in practice.

\subsection{Naive enumeration}
\label{sec:stdiff:naiveenum}

  The simplest option for computing a patch that transforms
a tree |x| into |y| is enumerating all possible patches and filtering
our those with the smallest \emph{cost}, for some \emph{cost} metric.
In this section, we will write a naive enumeration engine for
|PatchST| and argue that regardless of the \emph{cost} notion,
the state space explodes quickly and becames intractable.

  The enumeration follows the Agda model~\cite{Miraldo2017}
closely and is not very surprising. Nevertheless, it does
act as a good specification for a better implementation later.
Just like for the linear case,
the changes that can transform two values |x| and |y| of a given mutually
recursive family into one another are the deletion of a constructor from |x|,
the insertion of a constructor from |y| or changing the constructor
of |x| into the one from |y|, as witnessed by the |enumAlmu| function below.

\begin{myhs}
\begin{code}
enumAlmu  :: Fix ki codes ix -> Fix ki codes iy -> [Almu ki codes ix iy]
enumAlmu x y  =     enumDel (sop $ unFix x)  y
              <|>  enumIns x (sop $ unFix y)
              <|>  Spn <$> enumSpn  (snatFixIdx x) (snatFixIdx y)
                                    (unFix x) (unFix y)
  where
    enumDel (Tag c p) y0  = Del c <$> enumDelCtx p y0
    enumIns x0 (Tag c p)  = Ins c <$> enumInsCtx x0 p
\end{code} %$
\end{myhs}

  Enumerating all the patches from a deletion context of a given product |p|
against some fixpoint |y| consists of enumerating the patches
that transform all of the fields of |p| into |y|. The handling of insertion
contexts is analogous, hence it is ommited here.
Recall that the |AlmuMin|, below, is used to flag the resulting context as
a deletion context.

\begin{myhs}
\begin{code}
enumDelCtx  :: PoA ki (Fix ki codes) prod -> Fix ki codes iy -> [DelCtx ki codes iy prod]
enumDelCtx Nil              _  = []
enumDelCtx (NA_K x  :* xs)  f  = T (NA_K x) <$> enumDelCtx xs f
enumDelCtx (NA_I x  :* xs)  f  =    (flip H xs . AlmuMin)  <$> enumAlmu x f
                               <|>  T (NA_I x)         <$> enumDelCtx xs f
\end{code} %$
\end{myhs}

  Next we look into enumerating the spines between |x| and |y|, that is,
changes to the coproduct structure from |x| to |y|. Unlike
our Agda model, we need to know over which element of the mutually
recursive family we are operating. This will dictate which
constructors from |Spine| we are allowed to use. We gather this
information through two auxiliary |SNat| parameters.

\begin{myhs}
\begin{code}
enumSpn  :: SNat ix -> SNat iy
         -> Rep ki (Fix ki codes) (Lkup ix codes)
         -> Rep ki (Fix ki codes) (Lkup iy codes)
         -> [Spine ki codes (Lkup ix codes) (Lkup iy codes)]
enumSpn six siy (sop -> Tag cx px) (sop -> Tag cy py)
  = case testEquality six siy of
      Nothing -> SChg cx cy <$> enumAl px py
      Just Refl -> case testEquality cx cy of
           Nothing   -> SChg cx cy <$> enumAl px py
           Just Refl ->  if eqHO px py
                         then return Scp
                         else SCns cx <$> mapNPM (uncurry' enumAt) (zipNP px py)
\end{code} %$
\end{myhs}

  Note how the choice of the spine operation is deterministic. Each
situation is uniquely determined by a |Spine| constructor. Enumerating
atoms, |enumAt|, is trivial. Atoms are either opaque types or recursive
positions. Opaque types are handled by |TrivialK| and recursive positions
are handled recursively by |enumAlmu|. Finally, alignments of products is analogous
to the longest common subsequence, except that we must make sure that we only
synchronize atoms with |AX| if they have the same type.
The |enumAl| below illustrates the non-deterministic enumeration
of alignments over two products-of-atoms.


\begin{myhs}
\begin{code}
enumAl  :: PoA ki (Fix ki codes) p1 -> PoA ki (Fix ki codes) p2 -> [Al ki codes p1 p2]
enumAl Nil        Nil        = return A0
enumAl (x :* xs)  Nil        = ADel x  <$> enumAl xs Nil
enumAl Nil        (y :* ys)  = AIns y  <$> enumAl Nil ys
enumAl (x :* xs)  (y :* ys)  =    (ADel x <$> enumAl xs (y :* ys))
                             <|>  (AIns y <$> enumAl (x :* xs) ys)
                             <|>  case testEquality x y of
                                      Just Refl  -> AX <$> (enumAt x y) <*> enumAl xs ys
                                      Nothing    -> mzero
\end{code} %$
\end{myhs}


  Looking at |enumAlmu| and |enumAl|, we can see why this algorithm
explodes and becomes intractable quickly. In |enumAlmu| we must
choose between inserting, deleting or copying a recursive constructor.
In case we chose to copy, we then might call |enumAl|, where
we must chose between inserting, deleting or copying fields
of constructors.


\subsection{Translating from \texttt{gdiff}}
\label{sec:stdiff:oraclesenum}

  Since enumerating all possible patches and then filtering a chosen
one is time consuming and requires an complex notion
of cost over |PatchST|, it was clear we should be pursuing better
algorithms for our |diff| function. We have attempted two similar approaches to
filter the unintersting patches out and optimize the search space.

  A first idea, which arose in conjuncton with Pierre-Evariste Dagand
(private communication), was to use the already existing \unixdiff{}
tool as some sort of \emph{oracle}.  That is, we should only consider
inserting and deleting elements that fall on lines marked as such by
\unixdiff{}. This idea was translated into Haskell by Giovani
Garuffi~\cite{Garuffi2018}, but the performance was still very poor
and computing the |PatchST| of two real-world Clojure files still
required several minutes.

  From these experiments \cite{Garuffi2018} we learnt that simply restricting
the search space was not sufficient.
Besides the complexity introduced by arbitrary heuristics,
using the \unixdiff{} to flag elements of the AST was still too
coarse. For one, the \unixdiff{} can insert and delete the same line
in some situations. Secondly, many elements of the AST may fall on the same line.

  The second option is related, but instead of using a line-based
oracle, we can use \texttt{gdiff}~\Cref{sec:gp:well-typed-tree-diff} as the oracle,
enabling us to annotate every node of the source and destination trees
with a information about whether that node was copied or not.  This
strategy was translated into Haskell by A. van
Putten~\cite{Putten2019} as part of his MSc work. The gist of it
is that we can use annotated fixpoints -- provided by \texttt{generics-mrsop},
\Cref{sec:gp:mrsop:holes} -- to tag each constructor
of a tree with added information. In this case, we are interested
in whether this node would be copied or not by \texttt{gdiff}:

\begin{myhs}
\begin{code}
data Ann = Modify | Copy
\end{code}
\end{myhs}

  A |Modify| annotation corresponds to a deletion or insertion
depending on whether it is the source or destination tree
respectively.  Recall that an edit-script produced by \texttt{gdiff}
has type |ES kappa codes xs ys|, where |xs| is the list of types of the
source trees and |ys| is the list of types of the destination trees.
The definition of |ES| -- introduced in
\Cref{sec:gp:well-typed-tree-diff} -- is repeated below.

\begin{myhs}
\begin{code}
data ES (kappa :: kon -> Star) (codes :: [[[Atom kon]]])
    :: [Atom kon] -> [Atom kon] -> Star where
  ES0  :: ES kappa codes (P []) (P [])
  Ins  :: Cof kappa codes a t  -> ES kappa codes          i   (t :++:  j)  -> ES kappa codes           i   (a Pcons  j)
  Del  :: Cof kappa codes a t  -> ES kappa codes (t :++:  i)           j   -> ES kappa codes (a Pcons  i)            j
  Cpy  :: Cof kappa codes a t  -> ES kappa codes (t :++: i)   (t :++:  j)  -> ES kappa codes (a Pcons i)   (a Pcons  j)
\end{code}
\end{myhs}

  Given a value of type |ES kappa codes xs ys|, we have information
about which constructors of the trees in |NP (NA kappa (Fix kappa
codes)) xs| should be copied. Our objective then is to annotated the
trees with this very information. This is done by the |annSrc| and
|annDst| functions. We will only look at |annSrc|, the definition of
|annDst| is symmetric.

  Annotating the source forest with a given edit-script
consists in matching which constructors present in the forest
correspond to a copy and which correspond to a deletion.
The insertions in the edit-script concern the destination forest only.
The |annSrc| function, below, does exactly that, proceeding
by induction on the edit-script.

\begin{myhs}
\begin{code}
annSrc  :: NP (NA kappa (Fix kappa codes)) xs -> ES kappa codes xs ys
        -> NP (NA kappa (FixAnn kappa codes (Const Ann))) xs
annSrc xs         ES0         = Nil
annSrc Nil        _           = Nil
annSrc xs         (Ins c es)  = annSrc' xs es
annSrc (x :* xs)  (Del c es)  = let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Modify) (annSrc' (appendNP poa xs) es)
annSrc' (x :* xs) (Cpy _ c es) = let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Copy) (annSrc' (appendNP poa xs) es)
\end{code}
\end{myhs}

  The deterministic diff function for |Almu| then starts by checking
the annotations present at the root of its argument trees. In case both
are copies, we start with a spine. If at least one of them is not
a copy we insert or delete the constructor not flagged as a copy.
We must guard for the case that there exists a copy in the inserted
or deleted subtree. In case that does not hold, we would not
be able to choose an argument of the inserted or deleted constructor
to continue diffing against, in |diffCtx|. When there are no more copies to be performed,
we just return a \emph{stiff} patch, which deletes the entire source
and inserts the entire destination tree.

\begin{myhs}
\begin{code}
diffAlmu  :: FixAnn kappa codes (Const Ann) ix -> FixAnn kappa codes (Const Ann) iy
          -> Almu kappa codes ix iy
diffAlmu x@(FixAnn ann1 rep1) y@(FixAnn ann2 rep2) =
  case (getAnn ann1, getAnn ann2) of
    (Copy, Copy)      -> Spn (diffSpine  (getSNat $ Proxy @ix)
                                         (getSNat $ Proxy @iy)
                                         rep1 rep2)

    (Copy, Modify)    ->  if hasCopies y  then diffIns x rep2
                                          else stiffAlmu (forgetAnn x) (forgetAnn y)

    (Modify, Copy)    ->  if hasCopies x  then diffDel rep1 y
                                          else stiffAlmu (forgetAnn x) (forgetAnn y)

    (Modify, Modify)  ->  if hasCopies x  then diffDel rep1 y
                                          else stiffAlmu (forgetAnn x) (forgetAnn y)
    where
      diffIns x rep  = case sop rep of Tag c ys -> Ins c (diffCtx CtxIns x ys)
      diffDel rep y  = case sop rep of Tag c xs -> Del c (diffCtx CtxDel y xs)
\end{code}
\end{myhs}

  The |diffCtx| function selects an element of
a product to continue diffing against. We naturally select the
element that has the most constructors marked for copy as the element
we continue diffing against. The other fields of the product
are placed on the \emph{rigid} part of the context, that is,
the trees that will be deleted or inserted entirely, without
sharing any of their subtrees.

\begin{myhs}
\begin{code}
diffCtx  :: InsOrDel kappa codes p -> FixAnn kappa codes (Const Ann) ix
         -> NP (NA kappa (FixAnn kappa codes (Const Ann))) xs
         -> Ctx kappa codes p ix xs
\end{code}
\end{myhs}

  The other functions for translating two |FixAnn kappa codes (Const Ann) ix|
into a |PatchST| are straightforward and follow a similar reasoning process:
extract the annotations and defer copies until both source and destination
annotation flag a copy.

  This version of the |diff| function runs in $\mathcal{O}(n^2)$ time, where
$n$ is the the number of constructors in the bigger input tree. Although
orders of magnitude better than naive enumeration or using the \unixdiff{}
as an oracle, a quadratic algorithm is still not practical, particularly
when $n$ tens do be large -- real-world source files have tens of thousands
abstract syntax elements.

\section{Discussion}

  With \texttt{stdiff} we learned that the difficulties
of edit-script based approaches are not due, exclusively, to
using linear data to represent transformations to tree structured data.
Another important aspect that we unknowingly overlooked, and ultimately did
lead to a prohibitively expensive |diff| function, was the necessity to choose
a single copy opportunity. This happens whenever a subtree could be copied in two or
more different ways, and, in tree differencing this occurs often.

  The |PatchST| datatype has many interesting aspects that deserve some
mention. First, by being globally synchronized -- that is, explicit insertions
and deletions with one hole -- these patches are easy to merge. Moreover,
we have seen that it is possible, and desirable, to encode patches
as homogeneous types: a patch transform two values of the same
member of the mutually recursive family.

  In conclusion, lacking an efficient |diff| algorithm meant that
\texttt{stdiff} was an important step leading to new insights,
but unfortunately was not worth pursuing further. This meant that a number
of interesting topics such as the algebra of |PatchST| and the notion
of cost for |PatchST| were abandoned indefinitely.

%%  If we attempt to write a cost function for |PatchST| we also
%%run into intersting challenges. Recall that the \emph{cost} function
%%provides a metric to decide which patch is preferred.
%%Now take insertions and deletions at the |Almu| level
%%and changes at the spine leven, |Spn (SChg c1 c2 al)|.
%%The second clearly offers many more
%%copy opportunities, and hence, should be preferred.
%%Now consider the two patches below, that transform |t1| into |t2|,
%%illustrated in \Cref{fig:stdiff:patch1}.
%%
%%\begin{myhs}
%%\begin{code}
%%good  = Spn (SChg Bin Tri (AX (diff a a') (AIns Leaf (AX (diff b b') A0))))
%%
%%bad   = Del Bin (There a  (Here
%%            (Ins Tri (There a' (There Leaf (Here (diff b b') [] End)))) End))
%%\end{code}
%%\end{myhs}
%%
%%
%%\begin{figure}
%%\centering
%%\subfloat[Source tree, |t1|]{%
%%\begin{forest}
%%[ |Bin| [a] [b] ]
%%\end{forest}\qquad
%%\label{fig:stdiff:patch1-a}
%%}%
%%\qquad
%%\subfloat[Destination tree, |t2|]{%
%%\begin{forest}
%%[ |Tri| [a'] [Leaf] [b'] ]
%%\end{forest}\qquad
%%\label{fig:stdiff:patch1-b}}
%%\caption{Source and destination trees where we clearly prefer an |Spn (SChg _ _ _)| over
%%|Ins Tri (dots (Del Bin dots) dots)|}
%%\label{fig:stdiff:patch1}
%%\end{figure}
%%
%%  We would like to distinguish |good| from |bad| above by the means
%%of |cost|, that is, |cost good < cost bad|. Consequently, the cost
%%of insertions and deletions \emph{must} carry the size of the subtrees
%%they fix.
%%
%%Yet, in situations where
%%|a| and |a'| above have no copy oportunities,
%%
%%  Recall that on the longest common subsequence scenario,
%%\Cref{sec:background:string-edit-distance}, the cost function was
%%essentially counting insertions and deletions and the heuristics were
%%to minizesaid count. Another way to look at it was to count possible
%%copies and maxime it. This duality is not present on the tree world.
%%Counting copies can be misleading. If |cost (diff a a')|, above, is high,
%%it is likely that the |bad| patch is chosen instead of what we would expect.
%%The reason is because deletions and insertions for tree shaped
%%data are not atomic, and hence, should not have a fixed cost. They insert
%%and delete entire trees.
%%
%%\victor{We do not have a full answer to this problem; how should I write this?}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
