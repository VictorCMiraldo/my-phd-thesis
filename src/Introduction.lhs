
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
the granularity is at the abstract syntax elements level. 
\Cref{chap:structural-patches,chap:pattern-expression-patches} discusses two different 
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

  The success rate of the |merge| function is a consequence of the
degree of information provided by the |Patch| datatype. As we have
seen, if we only posses information on the line-level of the source
code, there is very little we can merge.  In order to have more
information available about the structure of the changes being
performed, then, we need to represent patches in a datatype that
closely follows the structure of the data being differenced.

\victor{What follows is a little bridge into ``GP is also important for us'';
I'm not 100\% happy with it, though}

  Structural differencing can be seen as a textbook example of generic
programming: we want our differencing algorithms to work over
arbitrary datatypes, but maintaining the type-safety that a language
like Haskell provides. This added safety means that all the
manipulations we perform on the patches are guaranteed to never break
the abstract syntax, which is often not the case.  It is common to
translate abstract syntax trees into a XML-like datatype and only then
compute the differences. We call these \emph{untyped} tree
differencing algorithms in contrast with our \emph{typed} approach.
  
  Writing \emph{typed} generic programming algorithms for regular
types is an estabilished technique\victor{find some citations}. 
Translating these techniques to mutually recursive datatypes -- as is
the case of most real programming languages abstract syntaxes --
is non-trivial and, in fact, is almost non existent. Consequently,
we must also overtake these challanges and create generic programming
techniques to write our algorithms and be able to test them against
real world data.

\section{Literature Review}
\label{sec:intro:literature-review}
  
  Computing the tree edit distance -- classically -- is the
problem of computing a minimum cost edit script that transforms a
target into a source ordered tree.  This edit script can be seen as a
sequence of edit operations. These operations often include, for
example, \emph{insert node}, \emph{delete node} and \emph{relabel
node}.  Zhang and Sasha~\cite{Zhang1989} provide a number of
algorithms which were later improved on by Klein et
al.~\cite{Klein1998} and Dulucq et al.~\cite{Dulucq2003}. Finally,
Demaine et al.~\cite{Demaine2007} presents an algorithm of cubic
complexity and proves this is the best possible worst case. Zhang and
Sasha algorithm is still faster in many pratical scenarios,
though. The more recent \emph{RTED}~\cite{Pawlik2012} algorithm
maintains the cubic worst case complexity and compares or outruns any
of the other algorithms, rendering it the standard choice for
computing tree edit distance based on the classic edit operations.  In
the case of unordered trees the best we can rely on are approximations
\cite{Augsten2008,Augsten2010} since the problem is
NP-hard~\cite{Zhang1992}.

  Tree edit distance has seen multidisciplinary interest. From
Computational Biology, where it is used to align phylogentic trees and
compare RNA secondary structures
\cite{Akutsu2010b,Henikoff1992,McKenna2010}, all the way to inteligent
tutoring systems where we must provide good hints to student's
solutions to exercises by understanding how far they are from the
correct solutions \cite{Paassen2017,Rohan2016}.  In fact, from the
\emph{tree edit distance} point of view, we are only concerned with a
number, the \emph{distance} between objects, quantifying how similar
they are. 

  From the perspective of \emph{tree differencing}, on the other hand,
we actually care about the edit operations and might want to perform
computations such as composition and merging of
differences. Naturally, however, the choice of edit operations heavily
influence the complexity of the |diff| algorithm. Allowing a
\emph{move} operation already renders string differencing
NP-complete~\cite{Shapira2002}. Tree differencing algorithms,
therefore, tend to run approximations of the best edit distance. Most
of then still suffer from at least quadratic time complexity, which is
prohibitive for most pratical applications or are defined for domain
specific data, such as the \texttt{latexdiff}~\cite{LatexDiff} tool.
A number of algorithms specific for XML and imposing different
requirements on the schemas have been developped~\cite{Peters2005}.
LaDiff~\cite{Chawathe1996}, for example, imposes restrictions on the
hierarchy between labels, it is implemented into the
\texttt{DiffXML}~\cite{Mouat2002} and
\texttt{GumTree}~\cite{Falleri2014} tools and is responsible
from deducing an edit script given tree matchings, the tree matching
phase differs in each tool. A notable mention is the
\texttt{XyDiff}~\cite{Marian2002}, which uses hashes to compute
matchings and, therefore, supports \emph{move} operations maintaining
almost linear complexity.  This is perhaps the closes to our approach
in \Cref{chap:pattern-expression-patches}. The
\texttt{RWS-Diff}~\cite{Finis2013} uses approximate matchings by
finding trees that are not necessarily equal but \emph{similar}, this
yeilds a robust algorithm, which is applicable in practice.
Most of these techniques recycle list differencing and can be seen
as some form of string differencing over the preorder (or postorder)
traversal of trees, which has quadratic upper bound~\cite{Guha2002}.
A careful encoding of the edit operations enables one to have edit scripts
that are guarnateed to preserve the schema of the data under manipulation
\cite{Lempsink2009}.

  Besides computing differences, we are also interested in merging the
computed differences, effectively synchronizing
changes~\cite{Balasubramaniam1998}. Naturally, merging algorithms are
heavily dependent on the representation of objects and edit scripts imposed 
by the underlying differencing algorithm.
The \texttt{diff3}~\cite{Smith1988}, developed by Randy Smith in 1988, is still the
most widely used synchronizer. It has received a formal treatment
and specification \cite{Khanna2007} posterior to its development, however.
Algorithms for synchronizing changes over tree shaped data 
include \texttt{3DM}~\cite{Lindholm2004} which merges
changes over XML documents, \texttt{Harmony}~\cite{Foster2007},
which works internally with unordered edge-labelled trees and
\texttt{FCDP}~\cite{Lanham2002}, which uses XML as its internal
representation.

 Also worth mentioning is the generalization
of \texttt{diff3} to tree structured data using well-typed approaches
due to Vassena~\cite{Vassena2016}, which uncovered the demotivating flaw
of failure due to schema violations, even in the presence of 
type edit scripts.

  Neighbouring source-code differencing we have patch inference and
generation tools. Some infer patches from human created data
\cite{Kim2013}, whereas other, such as
\texttt{Coccinelle}~\cite{Andersen2008,Palix2011}, receive as input a
number of diffs, $P_0, \cdots, P_n$, that come from differencing many
source and target files, $P_i = \mathit{diff }s_i\;t_i$.  The
objective then is to infer a common transformation that was applied
everywhere. One can think of determining the \emph{common denominator}
of $P_0, \cdots, P_n$. Refactoring and Rewritting Tools
\cite{Medeiros2017,Maletic2015} must also be mentioned. Some of these
tools define each supported language AST
separately~\cite{Bravenboer2008,Klint2009}, whereas others
\cite{Tonder2019} support a universal approach similar to
\emph{S-expressions}. They identify only parenthesis, braces and
brackets and hence, can be applied to a plethora of programming
languages out-of-the-box.

\victor{should I go into this next paragraph?}
  Which brings us to the second underlying aspect of this thesis,
\emph{generic programming}. Although different ... 

\section{Contributions and Outline} 
\label{sec:intro:contributions}

  The main chapters of this thesis are based on peer-reviewed
publications. Namellly,  

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

\victor{I'd also like to write a bit about how things 
took place: the GHC bug, which means we can't run our |PatchStruct| 
in the same amount of data as |PatchPE|; developping two generic programming
libraries; the time spent on Agda, etc... Is there a place for this in
the introduction or not?}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
