\newcommand{\ie}{i.e.}

  When working with \texttt{gdiff}-style patches, where a patch that
transforms a list of trees |xs| into a list of trees |ys| is given by
a heterogeneous type -- |PatchGDiff xs ys| -- it is inevitable to
stumble upon a difficult issue when dealing with the merge problem.
If we are given two patches |PatchGDfiff xs ys| and |PatchGDiff xs
zs|, we would like to produce two patches |PatchGDiff ys rs| and
|PatchGDiff zs rs| such that the cannonical square commutes. The issue
here is determining |rs| correctly and sometimes, said |rs| might not
even exist~\cite{Vassena2016}.

  \emph{Structural Patches} was our first attempt at detaching from
edit-scripts, looking for a homogeneous representation for patches,
\ie, a patch transforms two values of the same type. Consequently, we do
not have a problem to determine the indexes when merging patches, all
the patches involved will be of type |PatchST x|, where |x| is the
type of the object being merged. The \texttt{stdiff} algorithm support
a similar set of operations to edit scripts, but these are structured
in a way that mirrors the sums-of-products structure of datatypes: there
is one way of changing sums, one way of changing products and one way
of changing the recursive structure of the type. For example, consider
the following trees:

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
Which can be done by the means of an edit script. The second field, however,
witnesses a change in the recursive structure of the type. We see that
we have inserted new information, namelly |(Bin SQ e)|. After inserting
this \emph{context}, we simply copy |d| from the source to the destination.
And in this example we see all the necessary pieces to write a general
encoding of transformations between objects that support insertions, deletions
and copies.

\todo{make subtrees triangles}
\begin{figure}
\centering
\subfloat[Source tree, |t1|]{%
\begin{forest}
[ |Bin| [ |Tri| [a] [b] [c]] [d]]
\end{forest}\qquad
\label{fig:stdiff:patch0-a}
}%
\qquad 
\subfloat[Destination tree, |t2|]{%
\begin{forest}
[ |Bin| [ |Bin| [a'] [b] ] [|Bin| [d] [e]] ]
\end{forest}\qquad
\label{fig:stdiff:patch0-b}}
\caption{Graphical representation of a simple transformation}
\label{fig:stdiff:patch0}
\end{figure}

  In this chapter we will delve into the construction of |PatchST| and its
respective components. Firstly, we familirizie ourslelves with |PatchST| 
and is application function, \Cref{sec:stdiff:patches}. Next we look into
merging and its cummutativity proof in \Cref{sec:stdiff:merging}. Lastly,
we discuss the |diff| function in \Cref{sec:stdiff:diff}, which comprises
a significant drawback of the \texttt{stdiff} approach for
its computational complexity. 

  The contributions in this chapter arises from joint
published work with Pierre-Evariste Dagand~\cite{Miraldo2017} which later
evolved into an \href{https://github.com/VictorCMiraldo/stdiff}{Agda repository}%
\footnote{https://github.com/VictorCMiraldo/stdiff}. The code presented here however
is based on Arian's translation of our Agda repository to Haskell as part of
his Master thesis work. 
\victor{We chose to use a single programming language bla bla bla}

\victor{|PatchST| also suffers from the ambiguity problem; Arian used
heuristics; the code presented here is his; even with \texttt{gdiff-as-a-service}
the performance was bad for real life}.

\victor{Code is here: \url{https://github.com/arianvp/generics-mrsop-diff/blob/master/src/Generics/MRSOP/Diff.hs}}

\victor{Shall we present things with or without |kappa|? I'm leaning
towards without}

\section{The Type of Patches}
\label{sec:stdiff:patches}

  The |PatchST| type is but an intensional model for
patches over mutually recursive families. We will be using the
\texttt{generics-mrsop} library (\Cref{chap:generic-programming})
throughout the exposition. We first consider a single layer of datatype,
\ie, a single application of the datatypes pattern functor. 
In \Cref{sec:stdiff:diff:fixpoints} we extend this treatment to recursive datatypes,
essentially by taking the fixpoint of the constructions in \Cref{sec:stdiff:diff:functors}.

  A datatype, when seen through its initial
algebra~\cite{initial-algebra} semantics, can be seen as an infinite
sucession of applications of its pattern functor, call it $F$, to
itself: $\mu F = F (\mu F)$. The \texttt{stdiff} approach to
structural differencing describes differences between values of $\mu
F$ by successively applying the description of differences between
values of type $F$, closely following the initial algebra semantics of
datatypes.

\subsection{Functorial Patches}
\label{sec:stdiff:diff:functor}

  Handling \emph{one layer} or recursion is done by addressing the possible
changes at the sum level, followed by some reconciliation at the product
level when needed. 

  The first part of our algorithm handles the \emph{sums} of the
universe. Given two values, |x| and |y|, it computes the
\emph{spine}\index{Structural Patches!Spine}, capturing the largest
common coproduct structure. We distinguish three possible cases:
%
\begin{itemize}
\item |x| and |y| are fully equal, in which case we copy the full
  values regardless of their contents.
%
\item |x| and |y| have the same constructor -- i.e., |x =
  (inject C) px| and |y = (inject C) py| -- but some subtrees of |x|
  and |y| are distinct, in which case we copy the head constructor and
  handle all arguments pairwise.
%
\item |x| and |y| have distinct constructors, in which case we record
  a change in constructor and a choice of the alignment of the
  source and destination's constructor fields.
\end{itemize}

  The datatype |Spine|, defined below, formalizes this 
description. The three cases we describe above correspond to the three
constructors of |Spine|. When the two values are not equal, we need to
represent the differences somehow. If the values have the same 
constructor we need to reconcile the fields of 
that constructor whereas if the values have different constructors 
we need to reconcile the products that make the fields of the constructors.
We index the data type |Spine| by the sum codes it operates over.
That is because we need to lookup the fields of the constructors
that have changed, and \emph{align} them in the case of |SChg|.
Intuitively, Spines act on sums and capture the ``largest shared coproduct structure'':

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

  The semantics of |Spine| are straightforward. Its application function
is given by pattern matching on the provided value and checking it is
made up with the required construtor. In the |SCns| case we simply map over
the fields with the |applyAt| function, for applying changes to atoms.
Otherwise, we reconcile the fields with the |applyAl| function.

\victor{Should we show compiling code or simplify the proxies away?}
\victor{Maybe find a syntax-coloring that shades out the unintersting part?
we are dvidied in this opinion}
\begin{myhs}
\begin{code}
applySpine  :: (EqHO kappa)
            -> SNat ix -> SNat iy
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

  Where |testEquality|\index{testEquality}, here, is used to compare
the type indices for porpositional equality. It comes from |Data.Type.Equality|
and has type |f a -> f b -> Maybe (a :~: b)|.

  Note that we must pass two |SNat| arguments to disambiguate
the |ix| and |iy| type variables. Without those arguments, these
variables would only appear as an argument to a type family, which
may not be injective.
\victor{Explain singletons somewhere}

  Whereas the previous section showed how to match the
\emph{constructors} of two trees, we still need to determine how to
continue diffing the products of data stored therein. At this stage in
our construction, we are given two heterogeneous lists, corresponding
to the fields associated with two distinct constructors. As a result,
these lists need not have the same length nor store values of the same
type. To do so, we need to decide how to line up the constructor
fields of the source and destination. We shall refer to the process of
reconciling the lists of constructor fields as solving an
\emph{alignment} problem. 

  Finding a suitable alignment\index{Structural Patches!Alignment}
between two lists of constructor fields amounts to finding a suitable
\emph{edit script}, that relates source fields to destination
fields. The |Al| data type below describes such edit scripts for a
heterogeneously typed list of atoms. These scripts may insert fields
in the destination (|Ains|), delete fields from the source (|Adel|),
or associate two fields from both lists (|AX|).  Depending on whether
the alignment associates the heads, deletes from the source list or
inserts into the destination, the smaller recursive alignment has
shorter lists of constructor fields at its disposal.

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
constructors, thus forbidding permutations of arguments. In effect,
the datatype of alignments can be viewed as an intensional
representation of (partial) \emph{order and type preserving maps},
along the lines of McBride's order preserving
embeddings~\cite{McBride2005}, mapping source fields to destination
fields. This makes sure that our patches also give rise to tree 
mappings~\Cref{sec:background:tree-edit-distance} in the classical
tree-edit distance sense. Enabling us to see our patches as
some sort of homogeneous type-safe edit scripts. The advantages will
become clear when we look into the merge function.

  Provided a partial embedding for atoms, we can therefore interpret
alignments into a function transporting the source fields over to the
corresponding destination fields, failure potentially occurring when
trying to associate incompatible atoms:

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

  The last step is to address how to makde changes over the
recursive structure of our value, defining |Almu| and |applyAlmu|,
which will be our next concern.

\subsection{Recursive Changes}
\label{sec:stdiff:diff:fixpoint}

  In the previous section, we presented patches describing changes to
the coproducts, products, and atoms of our \emph{SoP} universe. This
treatment handled just a single layer of the fixpoint construction. In
this section, we tie the knot and define patches describing changes to
arbitrary \emph{recursive} datatypes.

  To represent generic patches on values of |Fix codes ix|, we will define
two mutually recursive data types |Almu|\index{Structural Patches!Recursive Alignment} and |Ctx|
\index{Structural Patches!Context}. The semantics of
both these datatypes will be given by defining how to \emph{apply}
them to arbitrary values:

\begin{itemize}
\item Much like alignments for products, a similar phenomenom appears
  at fixpoints. When comparing two recursive structures, we can
  insert, remove or modify constructors. Since we are working over mutually
  recursive families, removing or inserting constructors can change the
  overall type. We will use |Almu ix iy| to
  specify these edit scripts at the constructor-level, describing a transformation
  from |Fix codes ix| to |Fix codes iy|.

\item Whenever we choose to insert or delete a recursive subtree, we
  must specify \emph{where} this modification takes place.  To do so,
  we will define a new type |Ctx dots :: P [Atom kon] -> Star|, inspired by
  zippers~\cite{McBride2001}, to navigate through our data-structures. A
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
type InsCtx kappa codes = Ctx kappa codes        (Almu kappa codes)
type DelCtx kappa codes = Ctx kappa codes (Flip  (Almu kappa codes)) 

newtype Flip f ix iy = Flip { unFlip :: f iy ix }
\end{code}
\end{myhs}

Our definition of insertion and deletions relies on identifying
\emph{one} recursive argument among the product of possibilities. To
model this accurately, we define an indexed zipper to identify a
recursive atom (indicated by a value of type |I|) amongst a product of
atoms.  Conversely, upon deleting a constructor from the source
structure, we exploit |Ctx| to indicate find the subtree that should
be used for the remainder of the patch application, discarding all
other constructor fields. We parametrize the |Ctx| type
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
application process. This greatly increases the domain of
the application function. \victor{this deserves more info...}

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

\victor{Did we even explain |EqHO|?}
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

  In fact, defining |PatchST ix| as |Almu ix ix| will fit the 
our abstract formulation of differencing\victor{Where is this?}.

\begin{myhs}
\begin{code}
type PatchST kappa codes ix = Almu kappa codes ix ix

applyST  :: (IsNat ix , EqHO kappa)
         => PatchST kappa codes ix
         -> Fix codes ix
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


  One advantage of the |PatchST| approach is the natural merging
algorithm it yields. A merging algorithm reconciles changes from two
different patches whenever these are non interfering, for example, as
in \Cref{fig:stdiff:merging0}. We call non interfering patches
\emph{disjoint}, as they operate on separate parts of a tree.

\begin{figure}
\centering
Draw a simple example of mergeable patches here
\caption{A simple example of mergeable patches.}
\label{fig:stdiff:merging0}
\end{figure}

\victor{%
\begin{itemize}
  \item We have done this in Agda; show the types!
  \item Talk about disjointness and conflict placement.
  \end{itemize}}

\victor{\Huge temporary}

There are two
ways of looking into merging 

receives a span of patches,
that is, patches |p| and |q| with a common element in their
domains, and computes a patch that apply the changes
of |p| adapted to work over the codomain of |q|, as shown
in \Cref{fig:stdiff:mergesquare}.

\begin{figure}
\centering
\subfloat[Residual based merge operation]{%
\qquad $$
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} & \\
          a \ar[dr]_{|merge q p|} & & b \ar[dl]^{|merge p q|} \\
            & c &}
$$ \qquad
\label{fig:stdiff:mergesquare-resid}}%
\qquad%
\subfloat[Three-way based merge operation]{%
\qquad $$
\xymatrix{ & o \ar[dl]_{p} \ar[dr]^{q} \ar[dd]^(0.8){|merge p q|} & \\
          a & & b \\
            & c &}
$$ \qquad
\label{fig:stdiff:mergesquare-threeway}}
\caption{Two different ways to look at the merge problem.}
\label{fig:stdiff:mergesquare}
\end{figure}

  A positive aspect of the |PatchST| approach in comparison with
a purely edit-scripts based approach is the significantly
simpler merge function. This is due to |PatchST| being homogeneous.
Consequently, the type of the merge function very simple
and corresponds to what one would expect.

\begin{myhs}
\begin{code}
mergeST :: PatchST kappa codes ix -> PatchST kappa codes ix -> Maybe (PatchST kappa codes ix)
\end{code}
\end{myhs}

  A call to |mergeST| returns |Nothing| if the patches have non-disjoint changes,
that is, if both patches want to change the \emph{same part} of the source tree.
In our agda model, we have divided the merge function and the notion of disjointness,
which yields a total merge function:

%{
%option agda

\begin{myhs}
\begin{code}
merge : (p q : Patch kappa codes ix) -> Disjoint p q -> Patch kappa codes ix
\end{code}
\end{myhs}

  Where a value of type |Disjoint p q| is essentially a proof that |p|
and |q| change different parts of the source tree. This makes reasoning about
the merge function much easier. In fact, we have proven that the merge function
commutes as one would expect. A simplified statement of our theorem
given below, with |sym| witnessing the fact the disjointness is a symmetric relation.

\begin{myhs}
\begin{code}
mergecommutes  :   (p q : Patch kappa codes ix) 
               ->  (hyp : Disjoint p q)
               ->  apply (merge p q hyp) . q == apply (merge q p (sym hyp)) . p
\end{code}
\end{myhs}

%}

  Comming back to Haskell, it is simpler to rely on the |Maybe| monad for disjointness.
In fact, we could define disjointness as whether or not merge returns
a |Just|:

\begin{myhs}
\begin{code}
disjoint :: Patch kappa codes ix -> Patch kappa codes ix -> Bool
disjoint p q = maybe (const True) False (merge p q)
\end{code}
\end{myhs}

  The definition of the |mergeST| function can be seen in \Cref{fig:stdiff:mergest},
where we outline the classes of situations, some of which deserve some attention.
For example, when the numerator deletes a constructor but the denominator performs
a change within said constructor we must check that they operator over \emph{the same}
constructor. When that is the case, we must go ahead and ensure the deletion
context, |ctx|, and the changes in the product of atoms, |at|, are compatible.

\begin{myhs}
\begin{code}
mergeST (Del c1 ctx) (Spn (SCns c2 at)) = do  Refl <- testEquality c1 c2 
                                              mergeCtxAt ctx at
\end{code}
\end{myhs}

  A (deletion) context is disjoint from a list of atoms if the patch in
the hole of the context returns the same type of element than the patch
on the product of patches and they are both disjoint. Moreover, the rest
of the product of patches must consist in identity patches. Otherwise, we risk
deleting newly introduced information.

\victor{IMPORTANT: Arian forgot to ensure the |identityAt x| on the cases below;
I need to rerun his experiments}
\begin{myhs}
\begin{code}
mergeCtxAt  :: DelCtx kappa codes iy xs
            -> NP (At kappa codes) xs
            -> Maybe (Almu kappa codes ix iy)
mergeCtxAt (H (AlmuMin almu') rest) (AtFix almu :* xs) = do
  Refl <- testEquality (almuDest almu) (almuDest almu')
  x <- mergeAlmu almu' almu
  guard (and $ elimNP identityAt xs)
  pure x
mergeCtxAt (T at ctx) (x :* xs) 
  = guard (identityAt x) >> mergeCtxAt ctx xs
\end{code} %$
\end{myhs}

  Note the |textEquality| ensuring the patches to be merged are producing
the same element of the mutually recursive family. This is one of the two
places where we need these checks when adapting our Agda model to work
over mutually recursive types.

  The |mergeAtCtx| function, which is dual to |mergeCtxAt|, merges a
|NP (At kappa codes) xs| and a |DelCtx kappa codes iy xs| into a |Maybe
(DelCtx kappa codes iy xs)|, essentially preserving the |T at| it find on
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
...
mergeSpine ix iy (SChg cx cy al) (SCns cz zs)  = do  Refl <- testEquality ix iy
                                                     Refl <- testEquality cx cz
                                                     SCns cy <$$> mergeAlAt al zs
...

\end{code}
\end{myhs}


\begin{figure}
\begin{myhs}
\begin{code}
-- Non-disjoint recursive spines:
mergeST (Ins _ _)            (Ins _ _)           = Nothing
mergeST (Spn (SChg _ _ _))   (Del _ _)           = Nothing
mergeST (Del _ _)            (Spn (Schg _ _ _))  = Nothing
mergeST (Del _ _)            (Del _ _)           = Nothing

-- Obviously disjoint recursive spines:
mergeST (Spn Scp)            (Del c2 s2) = Just (Del c2 s2)
mergeST (Del c1 s2)          (Spn Scp)   = Just (Spn Scp)

-- Spines might be disjoint from spines and deletions:
mergeST (Spn s1)             (Spn s2) 
  = Spn <$$> mergeSpine (getSNat (Proxy @ix)) (getSNat (Proxy @iy)) s1 s2
mergeST (Spn (SCns c1 at1))  (Del c2 s2) 
  = Del c1 <$$> mergeAtCtx at1 s2
mergeST (Del c1 s1)          (Spn (SCns c2 at2)) 
  = do  Refl <- testEquality c1 c2 -- disjoint if same constructor
        mergeCtxAt s1 at2

-- Insertions are disjoint from anything except insertions.
-- Overall disjointness does depend on the recursive parts, though.
mergeST (Ins c1 s1)  (Spn s2)     = Spn . SCns c1  <$$> mergeCtxAlmu s1 (Spn s2)
mergeST (Ins c1 s1)  (Del c2 s2)  = Spn . SCns c1  <$$> mergeCtxAlmu s1 (Del c2 s2)
mergeST (Spn s1)     (Ins c2 s2)  = Ins c2         <$$> (mergeAlmuCtx (Spn s1) s2)
mergeST (Del c1 s1)  (Ins c2 s2)  = Ins c2         <$$> (mergeAlmuCtx (Del c1 s1) s2)
\end{code} 
\end{myhs}
\caption{Definition of |mergeST|}
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

\victor{I'm here}


  Our merge function is very simple and returns |Nothing| if the patches have
non-disjoint changes, that is, if the 

\victor{I need examples on the previous section to which I
can refer here}

  Intuitively, if two patches work over different parts of the abstract
syntax tree, we should be able to merge them quite easily. This is
what we call disjoint patches.

  The main advantage of the \texttt{stdiff} approach is the simple
merging algorithm that comes with it. 

\victor{%
\begin{itemize}
\item Easy to define disjointness
\item algo follows from it
\end{itemize}}

\section{Computing |PatchST|}
\label{sec:stdiff:diff}

  In the previous sections, we have devised a typed representation for
differences. We have seen that this representation is interesting in
and by itself: being richly-structured and typed, it can be thought of
as a non-trivial programming language whose denotation is given by the
application function. Moreover, we have seen how to
merge two disjoin differences. However, as programmers, we are mainly 
interested in \emph{computing} patches from a source and a
destination. Unfortunately, this is one of the main downsides
from the |PatchST| approach.

  In this section we start by outlining a nondeterministic specification
of an algorithm for computing a |PatchST|, in \Cref{sec:stdiff:naiveenum}.
We then provide example algorithms that implemented said specification
in \Cref{sec:stdiff:oraclesenum}. No matter the length of our efforts,
however, we will always be bound by the necessity of making choices
which is inherent to edit scripts. Consequently, computing a |PatchST|
will always be a computationally inefficient process.

\subsection{Naive enumeration}
\label{sec:stdiff:naiveenum}

\victor{I'm unsure whether we should spell out the details of the
enumeration; it's pretty straightforward...}

\victor{Answer is yes; talk about it and use it to show the tensions
around copy definitions: counting copies; depth of copies; size of copied subtrees etc;
each definition will have corner cases}

  The simplest option for computing a patch that transforms
a tree |x| into |y| is enumerating all possible patches and filtering
our those with the smallest \emph{cost}, for \emph{cost} an
arbitrary metric.

  It is straightforward to enumerate all possible patches,
as we have done for our Agda model~\cite{Miraldo2017}. 

\victor{
Very slow; suffers from the same heuristic
problems as the edit-script approaches. Plus,
definition of cost is more complicated here.
}

\subsection{Translating from \texttt{gdiff}}
\label{sec:stdiff:oraclesenum}

  Enumerating all possible patches and then filtering the one
with the least cost is a very time consuming. That is due to
the exponential number of patches that transforms a tree into another tree.
Most of these patches are far from optimal and, therefore, we should not be
spending time with them. We have attempted two approaches to
filter the unintersting patches out.

  A first attempt was done by \citet{Garuffi2018}, where
the notion of oracles where used to restrict the paths of the enumeration engine.
This enables one to easily instruct the enumeration engine to traverse
the search space in specific ways, for example, to never attempt
a deletion after an insertion. Moreover, the oracle approach
can receive external information. Ultimately, \citet{Garuffi2018}
used the \unixdiff{} as an oracle, instructing the enumeration engine
to only pursue insertions or deletions on the lines that were
marked as such by the \unixdiff{}. The performance was still very
low and could not compute the |PatchST| of two real Clojure files in
less than a couple minutes.

  From the experiments of \citet{Garuffi2018} we learnt that restricting
the search space was not sufficient. The reasons were manifold, really. 
Besides the complexity introduced by arbitrary heuristics, using the \unixdiff{}
to flag elements of the AST was still too coarse. Many elements of the AST
fall under the same line. The next idea was then to use \texttt{gdiff}~\Cref{sec:gp:well-typed-tree-diff},
as the oracle, enabling us to annotate every node of the source and destination
trees with a information about whether that node was copied or not.
\victor{Mention that Arian implemented our original Agda model}

\begin{myhs}
\begin{code}
data Ann = Modify | Copy
\end{code}
\end{myhs}

  A |Modify| annotation corresponds to a deletion or insertion
dependending on whether it is the source or destination tree
respectively.  Recall that an edit script produced by \texttt{gdiff}
has type |ES kappa codes xs ys|, where |xs| is the list of types of the
source trees and |ys| is the list of types of the destination trees.
The definition of |ES| -- introduced in
\Cref{sec:gp:well-typed-tree-diff} -- is repeated below.

\begin{myhs}
\begin{code}
data ES (kappa :: kon -> Star) (codes :: [[[Atom kon]]]) 
    :: [Atom kon] -> [Atom kon] -> Star where
  ES0  :: ES kappa codes Pnil Pnil
  Ins  :: Cof kappa codes a t  -> ES kappa codes i            (t :++: j)  
                            -> ES kappa codes i            (a Pcons j)
  Del  :: Cof kappa codes a t  -> ES kappa codes (t :++: i)   j           
                            -> ES kappa codes (a Pcons i)  j
  Cpy  :: Cof kappa codes a t  -> ES kappa codes (t :++: i)   (t :++: j)  
                            -> ES kappa codes (a Pcons i)  (a Pcons j)
\end{code}
\end{myhs}

  Given a value of type |ES kappa codes xs ys|, we have information about which constructors
of the trees in |NP (NA kappa (Fix kappa codes)) xs| should be copied. Our objective
then is to annotated the trees with this very information. This is done by the
|annSrc| and |annDst| functions. We will only look at |annSrc|, the definition
of |annDst| is symmetric.

\begin{myhs}
\begin{code}
annSrc :: NP (NA kappa (Fix kappa codes)) xs
       -> ES kappa codes xs ys
       -> NP (NA kappa (AnnFix kappa codes (Const Ann))) xs
annSrc xs         ES0         = Nil
annSrc Nil        _           = Nil
annSrc xs         (Ins c es)  = annSrc' xs es
annSrc (x :* xs)  (Del c es)  =
  let poa = fromJust $ matchCof c x
   in insCofAnn c (Const Modify) (annSrc' (appendNP poa xs) es)
annSrc' (x :* xs) (Cpy _ c es) =
  let poa = fromJust $ matchCof c x
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
diffAlmu  :: AnnFix kappa codes (Const Ann) ix
          -> AnnFix kappa codes (Const Ann) iy
          -> Almu kappa codes ix iy
diffAlmu x@(AnnFix ann1 rep1) y@(AnnFix ann2 rep2) =
  case (getAnn ann1, getAnn ann2) of
    (Copy, Copy)      -> Spn (diffSpine  (getSNat $ Proxy @ix) 
                                         (getSNat $ Proxy @iy) 
                                         rep1 rep2)
    (Copy, Modify)    ->  if hasCopies y 
                          then diffIns x rep2 
                          else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Copy)    ->  if hasCopies x 
                          then diffDel rep1 y 
                          else stiffAlmu (forgetAnn x) (forgetAnn y)
    (Modify, Modify)  ->  if hasCopies x 
                          then diffDel rep1 y 
                          else stiffAlmu (forgetAnn x) (forgetAnn y)
    where
      diffIns x rep  = case sop rep of Tag c ys -> Ins c (diffCtx CtxIns x ys)
      diffDel rep y  = case sop rep of Tag c xs -> Del c (diffCtx CtxDel y xs)
\end{code}
\end{myhs}

  The |diffCtx| function, which selects an element of the
a product to continue diffing against. We naturally select the
element that has the most constructors marked for copy as the element
we continue diffing against. The other fields of the product
are placed on the rigid part of the context.

\begin{myhs}
\begin{code}
diffCtx  :: InsOrDel kappa codes p
         -> AnnFix kappa codes (Const Ann) ix
         -> NP (NA kappa (AnnFix kappa codes (Const Ann))) xs
         -> Ctx kappa codes p ix xs
\end{code}
\end{myhs}

  The other functions for translating two |AnnFix kappa codes (Const Ann) ix|
into a |PatchST| are straightforward and follow a similar reasoning process:
extract the anotations and defer copies until both source and destination
annotation flag a copy.

\section{Discussion}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
