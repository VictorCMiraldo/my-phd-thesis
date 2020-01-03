
  Version Control is an essential technique for any kind of distributed
collaborative work. And, as any form of distributed work it must address the situation
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

  If we reconsider the example above, we could give a more accurate
description of the modification made to the |head| function by
describing the changes made to the constituent declarations and
expressions:
%
\begin{alltt}
head []        \{+d+\} = error \{-"?!"-\} \{+"Expect..."+\}
head (x :: xs) \{+d+\} = x 
\end{alltt}
There is more structure here than mere lines of text. In particular,
the granularity is at the abstract syntax elements level. \Cref{chap:structural-patches,chap:pattern-expression-patches} discusses two different 
approaches for representing changes to this desired granularity of
AST elements.

  In general, our approaches share a simple framework. 
We aim to compute the difference between two values
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
`best' one. Consequently, these attempts suffer from the same
downsides as classic edit-distance, which we will discuss in
in \Cref{sec:background:string-edit-distance}.

  Once we have a |diff| and an |apply| functions handy, we
move on to the |merge| function. Which is responsible for
synchronizing two different changesets into a single
one, when possible. Naturally not all patches can be merged, 
in fact, we can only merge those patches that alter \emph{disjoint} parts of the AST. 
Hence, the merge function must be partial, returning a conflict whenever
patches change the same part of the tree.
\begin{myhs}
\begin{code}
merge :: Patch a -> Patch a -> Either Conflicts (Patch a)
\end{code}
\end{myhs}

  How many patches can be merged by the |merge| function is 
a consequence of the degree of information provided by the |Patch| 
datatype. As we have seen, if we only posses information on the
line-level of the source code, there is very little we can merge.
In order to have more information available about the structure of
the changes being performed, then, we need more expressive |Patch| types.
\victor{bla bla generic programming is also important for us bla bla}

  \victor{I'd like to talk a bit about other areas where 
diffing can be interesting, i.e., biology; Should it go here?
I'm leaning towards leaving them on the discussion section
at the end.}

\subsection{Literature Review}

  Tree-differencing shows up in many different areas, from
Computational Biology, where it is used to align phylogentic trees and
compare RNA secondary structures
\cite{Akutsu2010b,Henikoff1992,McKenna2010}, all the way to inteligent
tutoring systems where we must provide good hints to student's
solutions to exercises by understanding how far they are from the
correct solutions \cite{Paassen2017,Rohan2016}.  Our particular focus
lies in the application of structural differencing to software
components. Currently, the best tree edit-distance algorithm
is \emph{RTED}~\cite{Pawlik2013}...
\victor{Mine more related work, RWS-Diff has a good related work section}

  A number of algorithms have been created with the intent of being
better suited towards operations over source code. Notable examples
include \emph{GumTree}~\cite{Falleri2014} which is a full suite for
source code differencing with a custom algorithn and
\emph{RWS-Diff}~\cite{Finis2013} which is a tree differencing
algorithms supporting some custom edit operations, such as node relabeling.
Both \emph{GumTree} and \emph{RWS-Diff} are tools created to handle source
code, in contrast with general purpose tree differencing algorithms.
\victor{more text; some merging?}

  Neighbouring source-code differencing we have patch inference
and tools, where Coccinelle~\cite{Andersen2008,Palix2011} is the
\emph{de-facto} standard. These tools receive as input a number of
patches, $P_0, \cdots, P_n$, that come from differencing many 
source and target files, $P_i = \mathit{diff }s_i\;t_i$. 
The objective then is to infer a common transformation that was 
applied everywhere. One can think of determining the \emph{common
denominator} of $P_0, \cdots, P_n$.

  Refactoring Tools~\cite{Tonder2019} and a plethora of domain specific tools,
such as \texttt{latexdiff}~\cite{LatexDiff} are also worth mentioning.
\victor{Find more; for example, efficient xml diffs and the 3DM algo}

\section{Contributions} 
\label{sec:intro:contributions}

  Next we outline the provenance of
the constributions on which this thesis is built upon.

\begin{enumerate}
  \item \Cref{chap:generic-programming} discusses the 
\texttt{generics-mrsop}~\cite{Miraldo2018} library, which improves
the Haskell ecosystem with combinator-based generic programming for
mutually recursive families. This work came out of close
collaboration with Alejandro Serrano on a variety of
generic programming topics.

  \item \Cref{chap:structural-patches} is derived from a published
joint collaboration \cite{Miraldo2017} with Pierre-\'{E}variste 
Dagand. We worked closely together to define a type-indexed datatype
used to represent changes in a more structured way than edit-scripts.
\Cref{chap:structural-patches} goes further onto developing
a merging algorthm and exploring different ways to compute 
patches given two concrete values.

  \item \Cref{chap:pattern-expression-patches} comes as the refinement
of our paper~\cite{Miraldo2019} on an efficient algorithm for
computing patches, where we attempt to tackle the problems from
\Cref{chap:structural-patches} with a different representation
for patches altogether.

  \item \victor{Hopefully we will publish something on experiments?}
\end{enumerate}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
