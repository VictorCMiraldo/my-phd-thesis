
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

\subsection{Literature Review}

  Tree-differencing shows up in many different areas, from Computational Biology,
where it is used to align phylogentic trees and compare RNA secondary structures
\cite{Akutsu2010b,Henikoff1992,McKenna2010}, all the way to inteligent tutoring systems
where we must provide good hints to student's solutions to exercises by
understanding how far they are from the correct solutions \cite{Paassen2017,Rohan2016}.
Our particular focus lies in the application of structural differencing to software
components.

  There has been a large body of work on providing better tooling for
software engineers by the means of structure-aware differencing
tools. A number of algorithms have been created with the intent of
being better suited towards operations over source code. Notable
examples include \emph{GumTree}~\cite{Falleri2014} which is a full
suite for source code differencing and
\emph{RWS-Diff}~\cite{Finis2013} which is a tree differencing
algorithms with a number of different edit operations.


  Coccinelle~\cite{Andersen2008,Palix2011}

  GumTree~\cite{Falleri2014}

  Refactoring Tools~\cite{Tonder2019} and a plethora of domain specific tools,
such as \texttt{latexdiff}~\cite{LatexDiff}
 
\section{Chronology of Contributions} 
\label{sec:intro:contributions}

  This thesis arises from a number of contributions.  In this section
we summarize their contributions and direct the reader to the relevant
chapter for more information. \Cref{chap:generic-programming,
chap:structural-patches, chap:pattern-expression-patches} contain our
scientific contributions whereas the rest of the thesis contains
general discussions.  Here we outline the thesis in its chronological
order, instead of chapter order.

  In \Cref{chap:background} one can find some preliminary important
notions underlying the topic of generic structural differencing. We
start by reviewing the \emph{longest common subsequence} algorithm,
then showing how it generalizes to (untyped) trees and finish with a
short summary of how we enforce well-typedness onto said
generalization. We also provide some background on generic
programming, mainly explaining the existing approaches that led to our
developments.

  \Cref{chap:structural-patches} portrays my first research visti.
Back in October of 2016 I made my first visit to Pierre-\'{E}variste
Dagand, where we worked on our first attempt on datatype-generic,
type-safe differencing~\cite{Miraldo2017}. This work consisted mainly
in crafting a representation for patches that could distance itself
from edit-scripts and better exploit the structure of the datatype in
question. Up to this point, all of our work was done in the Agda
programming language. Much later, in 2018, Arian van
Puten~\cite{Arian2019} adapted our Agda code into Haskell as part of
his Master thesis, implementing a few of our ideas on how to tackle
the computation of patches. We base the presentation in
\Cref{chap:structural-patches} on Arian's code, keeping the
programming language consistent throughtout this thesis. Nevertheless,
\Cref{chap:structural-patches} explores a definition of patches for
arbitrary mutually recursive types that support a simple merging
algorithm.  This algorithm has been proven to correctly merge disjoint
patches, but the computation of patches was still a challange.

  After my first visit to Paris, it was clear that we needed some
better way of computing patches if we ever wanted a practical approach
to structural differencing. Any algorithm slower than amortized linear
time would be too much for a tool supposed to be called many times
during the process of developing software. This would require a
significant re-engineering of our algorithms and a change of
programming language. It was time to rely to Haskell as our main
language. For that, however, we would need to create our own generic
programming tools. Together with Alejandro Serrano, we wrote and
published the \texttt{generics-mrsop}~\cite{Miraldo2018} library.
\Cref{chap:generic-programming} explains how the
\texttt{generics-mrsop} and shows its streamlined generic programming 
capabilities for mutually recursive families.

  With \texttt{generics-mrsop} at hand, the cost of creating prototypes
suddenly decreased significantly. In middle 2018 we decided to try
a radically different approach. Instead of modelling the patches first
then attempting to write an efficient algorithm that could compute
said patches, we started with writing a fast algorithm and explore what
are the patch definitions that would arise from it. 
\victor{bla... bla... bla..}

\subsection*{Summary of Papers}
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
