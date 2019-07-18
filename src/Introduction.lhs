
\newcommand{\unixdiff}{\texttt{UNIX diff}}

\victor{This is some loose paragraphs that need gluing}

  Version Control is an essential technique for any kind of distributed
collaborative work. 

  Any form of distributed collaborative work must address the situation
where two maintainers changed a piece of information in seemingly
different ways. One option is to lock further edits until a human
decides how to reconcile the changes, regardless of the changes. 
Yet, some changes can be reconciled automatically.

  Software engineers usually rely on version control systems to
help with this distributed workflow. These tools keep track of the
changes performed to the objects under version control, computing
changes between old and new versions of an object. When 
time comes to reconcile changes, it runs a \emph{merge} algorithm
that inspects these patches and decides whether they can be automatically
merged or not. At the heart of this process is (A) the representation of 
changes, usually denoted a \emph{patch} and (B) computing a \emph{patch}
between two objects. The merge algorithm can only be as good as how much
information \emph{patches} carry. 

  The most widespread representation for \emph{patches} comes from the
\unixdiff{}~\cite{McIlroy1976}. Tools such as git, mercurial and darcs,
that enable multiple developers to collaborate effectively, are all
built around the \unixdiff{} utility, that computes a patch
between two versions of a file.  It compares files on a line-by-line
basis attempting to share as many lines as possible between the source
and the destination files.

  A consequence of the \emph{by line} granularity of the UNIX
\texttt{diff} is it inability to identify more fine grained changes in
the objects it compares.  For example, if two parts of a program were
changed, but happen to be printed on the same line, the UNIX
\texttt{diff} sees this as a \emph{single} change.  Ideally, however,
the objects under comparison should dictate the granularity of change
to be considered. This is precisely the goal of \emph{structural
differencing} tools.

  In general, we aim to compute the difference between two values
of type |a|, and represent these changes in some type, |Patch a|.  The
|diff| function computes these differences between two values of type
|a|, and |apply| attempts to transform one value according to the
information stored in the |Patch| provided to it.
\begin{myhs}
\begin{code}
diff   :: a -> a -> Patch a
apply  :: Patch a -> a -> Maybe a 
\end{code}
\end{myhs}

  Note that the |apply| function may fail, for example, when attempting
to delete data that is not present. Yet when it succeeds, the |apply|
function must return a value of type |a|. This may seem like an
obvious design choice, but this property does not hold for the
approaches~\cite{Asenov2017,Falleri2014} using \texttt{xml} or
\texttt{json} to represent their abstract syntax trees, where the
result of applying a patch may produce ill-typed results, i.e.,
schema violations.

  The \unixdiff{}~\cite{McIlroy1976} satisfies these properties
for the specific type of lines of text, or, |a == [String]|.  It
represents patches as a series of insertions, deletions and copies of
lines and works by enumerating all possible patches that transform the
source into the destination and chooses the `best' such patch.  There
have been several attempts at generalizing these results to handle
arbitrary datatypes~\cite{Loh2009,Miraldo2017}, but following the
same recipe: enumerate all combinations of insertions, deletions and
copies that transform the source into the destination and choose the
`best' one. This design has some challenges at its core as we 
can see in \Cref{sec:background:edit-scripts}.

\victor{Literature review?}

% Problem 
%   - small summary shortcommings
% Contributions
% Outline and Papers

\section{Contributions} 

\begin{itemize}
  \item Generic Programming libraries
  \item \texttt{stdiff} approach
  \item \texttt{hashdiff} approach
\end{itemize}

\section{Outline and Papers}

  \Cref{chap:generic-programming} introduces the generic programming library we
have developed, \texttt{generics-mrsop}~\cite{Miraldo2018}. This library enabled
us to represent and manipulate mutually recursive families of datatype in Haskell, being the backbone of our differencing algorithms.

  During our period studying differeinving, two approaches have stood out. 
In \Cref{chap:structural-patches} we look into our first attempt at representing
patches~\cite{Miraldo2017}. This work was developed in Agda and later translated to Haskell using by A. van Putten~\cite{Putten2019}, during his Master Thesis.
\victor{mention Giovanni?}
\victor{Polish; present ins and outs}

\victor{mention trips to Paris}

  Finally, whilst on the quest of searching for an efficient algorithm,
we forked into a radically different approach, explored in \Cref{chap:pattern-expression-patches}.


% chapter X is based on paper Y, which was wrote with Alice and Bob
% and my contribution is Z to that paper.