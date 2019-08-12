
%format SQ = "\HSVar{\square}"
%format PatchGDiff = "\HSCon{\mathit{Patch}_\textsc{gd}}"
%format PatchST    = "\HSCon{\mathit{Patch}_\textsc{st}}"
\newcommand{\ie}{i.e.}
\newcommand{\stdiff}{\texttt{st-diff}}

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
\ie, a patch transforms two values of the same type. In turn, we do
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
a significant drawback of the \texttt{stdiff} approach because of
its computational complexity. 

\victor{|PatchST| also suffers from the ambiguity problem; Arian used
heuristics; the code presented here is his; even with \texttt{gdiff-as-a-service}
the performance was bad for real life}.

\victor{Code is here: \url{https://github.com/arianvp/generics-mrsop-diff/blob/master/src/Generics/MRSOP/Diff.hs}}

\victor{Shall we present things with or without |ki|? I'm leaning
towards without}

\section{The Type of Patches}
\label{sec:stdiff:patches}

  The |PatchST| type is but an intensional model for
patches over mutually recursive families. We will be using the
\texttt{generics-mrsop} library (\Cref{chap:generic-programming})
throughout the exposition. We first consider a single layer of datatype,
\ie, a single application of the datatypes pattern functor. 
In \Cref{sec:stdiff-fixpoints} we extend this treatment to recursive datatypes,
essentially by taking the fixpoint of the constructions in \Cref{sec:stdiff-functors}.

  A datatype, when seen through its initial algebra~\cite{initial-algebra} semantics, can be seen as an infinite sucession of applications of its pattern functor,
call it $F$, to itself: $\mu F = F (\mu F)$. The \stdiff{} approach to structural
differencing describes differences between values of $\mu F$ by successively
applying the description of differences between values of type $F$, closely
following the initial algebra semantics of datatypes. 

\subsection{Functorial Patches}
\label{sec:stdiff:diff:functor}

  Handling \emph{one layer} or recursion is done by addressing the possible
changes at the sum level, followed by some reconciliation at the product
level when needed. 

  The first part of our algorithm handles the \emph{sums} of the
universe. Given two values, |x| and |y|, it computes the
\emph{spine}, capturing the largest common coproduct structure. We distinguish 
three possible cases:
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
\victor{why?}

Spines act on sums and capture the ``largest shared coproduct structure''
\begin{myhs}
\begin{code}
data Spine  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
            :: [[Atom kon]] -> [[Atom kon]] -> Star where
  Scp   :: Spine ki codes s1 s1
  SCns  :: Constr s1 c1 -> NP (At ki codes) (Lkup c1 s1) 
        -> Spine ki codes s1 s1
  SChg  :: Constr s1 c1 -> Constr s2 c2 -> Al ki codes (Lkup c1 s1) (Lkup c2 s2)
        -> Spine ki codes s1 s2
\end{code}
\end{myhs}

  The semantics of |Spine| are straightforward. Its application function
is given by pattern matching on the provided value and checking it is
made up with the required construtor. In the |SCns| case we simply map over
the fields with the |applyAt| function, for applying changes to atoms.
Otherwise, we reconcile the fields with the |applyAl| function.

\victor{Should we show compiling code or simplify the proxies away?}
\begin{myhs}
\begin{code}
applySpine  :: (EqHO ki)
            -> SNat ix -> SNat iy
            -> Spine ki codes (Lkup ix codes) (Lkup iy codes)
            -> Rep ki (Fix ki codes) (Lkup ix codes)
            -> Maybe (Rep ki (Fix ki codes) (Lkup iy codes))
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

  Note that we must pass two |SNat| arguments to disambiguate
the |ix| and |iy| type variables. Without those arguments, these
variables would only appear as an argument to a type family, which
may not be injective.

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

  Finding a suitable alignment between two lists of constructor fields
amounts to finding a suitable \emph{edit script}, that relates source
fields to destination fields. The |Al| data type below describes such
edit scripts for a heterogeneously typed list of atoms. These scripts
may insert fields in the destination (|Ains|), delete fields from the
source (|Adel|), or associate two fields from both lists (|AX|).
Depending on whether the alignment associates the heads, deletes from
the source list or inserts into the destination, the smaller recursive
alignment has shorter lists of constructor fields at its disposal.

\begin{myhs}
\begin{code}
data Al  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
         :: [Atom kon] -> [Atom kon] -> Star where
  A0    :: Al ki codes (P []) (P [])
  AX    :: At ki codes x -> Al ki codes xs ys 
        -> Al ki codes (x Pcons xs)  (x Pcons ys)
  ADel  :: NA ki (Fix ki codes) x -> Al ki codes xs ys 
        -> Al ki codes (x Pcons xs) ys
  AIns  :: NA ki (Fix ki codes) x -> Al ki codes xs ys 
        -> Al ki codes xs (x Pcons ys)
\end{code}
\end{myhs}

  We require alignments to preserve the order of the arguments of each
constructors, thus forbidding permutations of arguments. In effect,
the datatype of alignments can be viewed as an intensional
representation of (partial) \emph{order and type preserving maps},
along the lines of McBride's order preserving
embeddings~\cite{McBride2005}, mapping source fields to destination
fields.

  Provided a partial embedding for atoms, we can therefore interpret
alignments into a function transporting the source fields over to the
corresponding destination fields, failure potentially occurring when
trying to associate incompatible atoms:

\begin{myhs}
\begin{code}
applyAl  :: (EqHO ki)
         => Al ki codes xs ys
         -> PoA ki (Fix ki codes) xs
         -> Maybe (PoA ki (Fix ki codes) ys)
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
data TrivialK (ki :: kon -> Star) :: kon -> Star where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon 
\end{code}
\end{myhs}

  In case we are at a recursive position, we record a potential change in
the recursive position with |Almu|, which we will get to shortly.

\begin{myhs}
\begin{code}
data At  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
         :: Atom kon -> Star where
  AtSet  :: TrivialK ki kon -> At ki codes (P K kon)
  AtFix  :: (IsNat ix) 
         => Almu ki codes ix ix -> At ki codes (P I ix)
\end{code}
\end{myhs}


  The application function for atoms follows the same structure. In case
we are applying a patch to an opaque type, we must understand whether said patch
represents a copy, \ie, the source and destination values are the same. If that is the
case, we simply copy the provided value. Otherwise, we must ensure the provided value matches
the source value. The recursive position case is directly handled by the |applyAlmu| function.

\begin{myhs}
\begin{code}
applyAt  :: EqHO ki
         => At ki codes at
         -> NA ki (Fix ki codes)) at
         -> Maybe (NA ki (Fix ki codes) at)
applyAt (AtSet (Trivial x y)) (NA_K a)  
  | eqHO x y   = Just (NA_K a)
  | eqHO x a   = Just (NA_K b)
  | otherwise  = Nothing
applyAt (AtFix px) (NA_I x) = NA_I <$$> applyAlmu px x
\end{code}
\end{myhs}

\subsection{Recursive Changes}
\label{sec:stdiff:diff:fixpoint}

A recursive alignment lets us know which constructors
must be inserted or deleted. Note how the insertion
and deletion operation are different from the XML based
patches.

\begin{myhs}
\begin{code}
data Almu  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
           :: Nat -> Nat -> Star where
  Spn  :: Spine ki codes (Lkup ix codes) (Lkup iy codes) 
       -> Almu ki codes ix iy
  Ins  :: Constr (Lkup iy codes) c
       -> InsCtx ki codes ix (Lkup c (Lkup iy codes))
       -> Almu ki codes ix iy
  Del  :: Constr (Lkup ix codes) c
       -> DelCtx ki codes iy (Lkup c (Lkup ix codes))
       -> Almu ki codes ix iy
\end{code}
\end{myhs}

  Contexts, here, are just one-hole contexts. We parametrize
it by the action on atoms for insertion and deletion contexts
will be slightly different.

\begin{myhs}
\begin{code}
data Ctx  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) (p :: Nat -> Nat -> Star) (ix :: Nat) 
          :: [Atom kon] -> Star where
  H  :: IsNat iy
     => p ix iy
     -> PoA ki (Fix ki codes) xs
     -> Ctx ki codes p ix ((P I iy) Pcons xs)
  T  :: NA ki (Fix ki codes) a
     -> Ctx ki codes p ix xs
     -> Ctx ki codes p ix (a Pcons xs)
\end{code}
\end{myhs}

  Deletion contexts reverse the indexes

\begin{myhs}
\begin{code}
data InsOrDel  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
               :: (Nat -> Nat -> Star) -> Star where
  CtxIns  :: InsOrDel ki codes (Almu     ki codes)
  CtxDel  :: InsOrDel ki codes (AlmuMin  ki codes)
\end{code}
\end{myhs}

\begin{myhs}
\begin{code}
newtype AlmuMin ki codes ix iy 
  = AlmuMin  { unAlmuMin :: Almu ki codes iy ix }

type InsCtx ki codes ix xs  = Ctx ki codes (Almu ki codes) ix xs
type DelCtx ki codes ix xs  = Ctx ki codes (AlmuMin ki codes) ix xs
\end{code}
\end{myhs}

\subsection{Application Semantics}

a.k.a: Denotational

\section{Merging Patches}
\label{sec:stdiff:merging}

\victor{%
\begin{itemize}
\item Easy to define disjointness
\item algo follows from it
\end{itemize}}

\section{Computing |PatchST|}
\label{sec:stdiff:diff}

Here is where we have a problem!

\subsection{Naive enumeration}

Very slow; suffers from the same heuristic
problems as the edit-script approaches. Plus,
definition of cost is more complicated here.

\subsection{Using Oracles}

Instead, we attempted using existing solutions to guide
the enumeration.

\subsubsection{\unixdiff{} as an Oracle}
 Giovanni's work; very slow

\subsubsection{\texttt{gdiff} as an Oracle}
 Arian's work; much better, still slow.

\section{Discussion}

