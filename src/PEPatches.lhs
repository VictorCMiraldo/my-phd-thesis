  The \texttt{stdiff} approach, which provided a first representation
of tree-sructured patches for tree-structured data was stil very
much coupled with edit-scripts. We still suffered the ambuiguity problem,
and this was reflected on the coputationally expensive algorithm. We were also
subject to being unable to represent permutations and moves efficiently.
These drawbacks motivated us to look for a better solution, which is
turned out to become |PatchH x|, our second attempt at detaching from 
edit scripts.

  Suppose we want to have a patch that modifies the left element
of a binary tree. If we had Haskell available to us, we would probably
write somethgin in the lines of:

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
as |patch (Bin (Leaf 10) y) (Bin (Leaf 42) y)|.

  With this added expressivity we can represent more transformations
than before. Take the patch that swaps two subtrees, which cannot
even be written using an edit-script based approach, here it is
given by |patch (Bin x y) (Bin y x)|. Another helpful consequence of
our design is that we bypass the \emph{choice} phase of the
algorithm. When computing the differences between |Bin Leaf Leaf|
and |Leaf|, for example, we do not have to chose one |Leaf| to copy
because we can simply copy both with a contraction. The patch
that witnesses this would be |patch (Bin x x) x|. This optimization
enables us to write linear |diff| algorithms. 

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

  Just like \texttt{stdiff}, \Cref{chap:structural-patches}, we will rely on
\texttt{generics-mrsop} to encode our operations. The first step in representing
our patches here is to augment the generic representation of our trees
with metavariables. Luckily, \texttt{generics-mrsop} provides the |Holes|
type (\Cref{sec:gp:holes}). Recall its definition:

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
representing metavariables. 

\victor{an example, please; also, try simplifying |MetaVarIK ki| in the code;
on the latest version is looks like we can remove it altogether}


\begin{myhs}
\begin{code}
type Chg ki codes at = (Holes ki codes (MetaVar ki) :*: Holes ki codes (MetaVar kki)) at
\end{code}
\end{myhs}



\subsection{Relationship with \texttt{gdiff}}

  A |PatchPE| together with an element
in its domain can be transformed into a |PatchGDiff|.

  Not of optimal cost, though.

\section{Computing |PatchPE|}

\section{Merging Patches}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
