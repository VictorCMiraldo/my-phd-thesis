
\begin{itemize}
  \item first paper
  \item proof of merge cumutativity
  \item Problems with performance
  \item using diff as an oracle
  \item arian's and giovanni's work,
\end{itemize}

\victor{Code is here: \url{https://github.com/arianvp/generics-mrsop-diff/blob/master/src/Generics/MRSOP/Diff.hs}}

\victor{As we seen in Background, es are hard to merge.
Why?
\begin{itemize}
  \item when typed, they are heterogeneous
  \item What to do instead?
\end{itemize}}

\victor{Shall we present things with or without |ki|? I'm leaning
towards without}

\section{Structure of Patches}
\subsection{Trivial Changes}

\victor{Present the infamous |Patch a = (a , a)|; show the
spec, bla bla bla}

\begin{myhs}
\begin{code}
data TrivialK (ki :: kon -> Star) :: kon -> Star where
  Trivial :: ki kon -> ki kon -> TrivialK ki kon 
\end{code}
\end{myhs}

\subsection{Functorial Changes}

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

As soon as said structure disagrees, we use the LCS to
align the disgreements.
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

Finally, when synchronizing atoms we must know whether we
are in a recursive position or not.
\begin{myhs}
\begin{code}
data At  (ki :: kon -> Star) (codes :: [[[Atom kon]]]) 
         :: Atom kon -> Star where
  AtSet  :: TrivialK ki kon -> At ki codes (P K kon)
  AtFix  :: (IsNat ix) 
         => Almu ki codes ix ix -> At ki codes (P I ix)
\end{code}
\end{myhs}

Talking about recusive positions:


\subsection{Recursive Changes}

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

\victor{%
\begin{itemize}
\item Easy to define disjointness
\item algo follows from it
\end{itemize}}

\section{Enumerating Patches}

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

