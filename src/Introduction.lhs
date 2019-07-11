 The UNIX \texttt{diff}~\cite{McIlroy1976} is an essential tool in
modern software development. It has seen a number of use cases ever
since it was created and lies at the heart of today's Software Version
Control Systems.  Tools such as git, mercurial and darcs, that enable
multiple developers to collaborate effectively, are all built around the
UNIX \texttt{diff} utility, that computes a patch between two
versions of a file. It compares files on a line-by-line basis
attempting to share as many lines as possible between the source and
the destination files.

  A consequence of the \emph{by line} granularity of the UNIX
\texttt{diff} is it inability to identify more fine grained changes in
the objects it compares.  For example, if two parts of a program were
changed, but happen to be printed on the same line, the UNIX
\texttt{diff} sees this as a \emph{single} change.  Ideally, however,
the objects under comparison should dictate the granularity of change
to be considered. This is precisely the goal of \emph{structural
differencing} tools.

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