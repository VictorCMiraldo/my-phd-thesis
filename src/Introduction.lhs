
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

  Maintaining a software as complex as an operating system with as
many as several thousands contributors is a technical feat made
possible thanks, in part, to a venerable Unix utility:
\unixdiff{}~\cite{McIlroy1976}. It computes the
line-by-line difference between two textual files, determining the
smallest set of insertions and deletions of lines to transform one
file into the other. In other words, it tries to share as many lines
between source and destination as possible.  This is, in fact, the
most widedespread representation for \emph{patches}, used by tools
such as git, mercurial and darcs.

  This limited grammar of changes works particularly well for
programming languages that organize a program into lines of code. For
example, consider the following modification that extends an existing
\texttt{for}-loop to not only compute the sum of the elements of an
array, but also compute their product:
%
\begin{alltt}
    sum := 0;
 +  prod := 1;
    for (i in is) \{
      sum += i;
 +    prod *= i;     
    \}
\end{alltt}
  
However, the bias towards \emph{lines} of code may lead to
(unnecessary) conflicts when considering other programming
languages. For instance, consider the following diff between two
Haskell functions that adds a new argument to an existing function:
%
\begin{alltt}
 - head []        = error "?!"
 - head (x :: xs) = x
 + head []        d = d
 + head (x :: xs) d = x
\end{alltt}
This modest change impacts all the lines of the function's definition.

The line-based bias of the diff algorithm may lead to unnecessary
\emph{conflicts} when considering changes made by multiple developers.
Consider the following innocuous improvement of the original |head|
function, that improves the error message raised when the list is empty:
%
\begin{alltt}
head []        = error "Expecting a non-empty list."
head (x :: xs) = x
\end{alltt}
Trying to apply the patch above to this modified version of the |head|
function will fail, as the lines do not match -- even if both changes modify 
distinct parts of the declaration in the case of non-empty lists. 

  This is a major consequence of the \emph{by line} granularity of
\emph{patches} -- their inability to identify more fine grained
changes in the objects it compares. Ideally, however, the objects
under comparison should dictate the granularity of change to be
considered. This is precisely the goal of \emph{structural
differencing} tools.

  If we reconsider the example aboce, we could give a more accurate
description of the modification made to the |head| function by
describing the changes made to the constituent declarations and
expressions:
%
\begin{alltt}
head []        \{+d+\} = error \{-"?!"-\} \{+"Expect..."+\}
head (x :: xs) \{+d+\} = x 
\end{alltt}
There is more structure here than mere lines of text. In particular,
the granularity is at the abstract syntax elements level.

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
arbitrary datatypes~\cite{Lempsink2009,Miraldo2017}, but following the
same recipe: enumerate all combinations of insertions, deletions and
copies that transform the source into the destination and choose the
`best' one. This design has some challenges at its core as we 
can see in \Cref{sec:background:string-edit-distance}.

\victor{Literature review?}

% Problem 
%   - small summary shortcommings
% Contributions
% Outline and Papers

\section{Contributions and Outline} 
\label{sec:intro:contributions}

  This thesis arises from a number of papers and two Master's thesis.
In this section we summarize their contributions and direct the reader
to the relevant chapter for more information. \Cref{chap:generic-programming,chap:structural-patches,chap:pattern-expression-patches} contain our scientific
contributions whereas the rest of the thesis contains general discussions.
Here we outline the thesis in its chronological order, instead of
chapter order.

  In \Cref{chap:background} one can find some preliminary important
notions underlying the topic of generic structural differencing. We
start by reviewing the \emph{longest common subsequence} algorithm,
then showing how it generalizes to (untyped) trees and finish with a
short summary of how we enforce well-typedness onto said
generalization. We also provide some background on generic
programming, mainly explaining the existing approaches that led to our
developments.

  Our first serious attempt at structural differencing happens 
in \Cref{chap:structural-patches}, and comes from our first
publication~\cite{Miraldo2017}. At the time we were working with the
Agda programming language on the modeling side of things. 
\victor{bla... bla... bla...}

  \Cref{chap:generic-programming} explains
\texttt{generics-mrsop}~\cite{Miraldo2018} -- a library that enables
streamlined generic programming for mutually recursive families. This
library arose from the wish to explore and address the performance
issues we were facing with our first serious attempt at structural
differencing, moreover, it would allow us to switch from Agda to
Haskell. We did need something that could handle arbitrary abstract
syntax trees in Haskell, and as seen in
\Cref{sec:background:generic-programming}, the existing approachs
would not be enough.

\begin{itemize}
  \item Generic Programming libraries
  \item \texttt{stdiff} approach
  \item \texttt{hashdiff} approach
\end{itemize}

\subsection*{Summary of Papers and Thesis}
\label{sec:intro:paper-summary}

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