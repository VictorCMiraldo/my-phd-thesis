
  Version Control is essential for any kind of distributed
collaborative work. It enables contributors to operate independently
and later combine their work. For that, though, it must
address the situation where two developers changed a piece of
information in different ways. One option is to lock
further edits until a human
decides how to reconcile the changes, regardless of the changes.
Yet, many changes can be reconciled \emph{automatically}.

  Software engineers usually rely on version control systems to
help with this distributed workflow. These tools keep track of the
changes performed to the objects under version control, computing
changes between old and new versions of an object. When
time comes to reconcile changes, it runs a \emph{merge} algorithm
that decides whether the changes can be synchronized or not.
At the heart of this process is (A) the representation of
changes, usually denoted a \emph{patch} and (B) the
computation of a \emph{patch} between two objects.
% The merge algorithm can only be as good as how much
% information \emph{patches} carry.

  Maintaining software as complex as an operating system with as
many as several thousands contributors is a technical feat made
possible thanks, in part, to a venerable Unix utility:
\unixdiff{}~\cite{McIlroy1976}. It computes the
line-by-line difference between two textual files, determining the
smallest set of insertions and deletions of lines to transform one
file into the other. In other words, it tries to share as many lines
between source and destination as possible.  This is, in fact, the
most widespread representation for \emph{patches}, used by tools
such as git, mercurial and darcs.

  The limited grammar of changes used by the \unixdiff{} works
particularly well for programming languages that organize a program
into lines of code. For example, consider the following modification
that extends an existing \texttt{for}-loop to not only compute the sum
of the elements of an array, but also compute their product:
%
\begin{alltt}\small
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
Haskell functions that add a new argument to an existing function:
%
\begin{alltt}\small
 - head []        = error "?!"
 - head (x :: xs) = x
 + head []        d = d
 + head (x :: xs) d = x
\end{alltt}
This modest change impacts all the lines of the function's definition,
even though it affects relatively few elements of the abstract-syntax.

The line-based bias of the diff algorithm may lead to unnecessary
\emph{conflicts} when considering changes made by multiple developers.
Consider the following innocuous improvement of the original \texttt{head}
function, which improves the error message raised when the list is empty:
%
\begin{alltt}\small
head []        = error "Expecting a non-empty list."
head (x :: xs) = x
\end{alltt}
Trying to apply the patch above to this modified version of the \texttt{head}
function will fail, as the lines do not match -- even if both changes modify
distinct parts of the declaration in the case of non-empty lists.

  The inability to identify more fine grained changes in the objects
it compares is a consequence of the \emph{by line} granularity of
\emph{patches}. Ideally, however, the objects under comparison should
dictate the granularity of change to be considered. This is precisely
the goal of \emph{structural differencing} tools.

  If we reconsider the example above, we could give a more detailed
description of the modification made to the \texttt{head} function by
describing the changes made to the constituent declarations and
expressions:
%
\begin{alltt}\small
head []        \{+d+\} = error \{-"?!"-\} \{+"Expect..."+\}
head (x :: xs) \{+d+\} = x
\end{alltt}
There is more structure here than mere lines of text. In particular,
the granularity is at the abstract-syntax level. It is worthwhile to note
that this problem also occurs in languages which tend to be organized in
a line-by-line manner. Modern languages
which contain any degree of object-orientation will also group several
abstract-syntax elements on the same line. Take the Java function below,
%
\begin{alltt}\small
public void test(obj) \{
  assert(obj.size(), equalTo(5));
\}
\end{alltt}

 Now consider a situation where one developer updated the test to
require the size of \texttt{obj} to be 6, but another developer
changed the function that makes the comparison, resulting
in the two orthogonal versions below;

\noindent
\begin{minipage}[t]{.5\textwidth}
\begin{alltt}\small
public void test(obj) \{
  assert(obj).hasSize(5);
\}
\end{alltt}
\end{minipage}%
\begin{minipage}[t]{.5\textwidth}
\begin{alltt}\small
public void test(obj) \{
  assert(obj.size(), equalTo(6));
\}
\end{alltt}
\end{minipage}


  It is straightforward to see that the desired \emph{synchronized} version
can incorporate both changes, calling { \small \verb!assert(obj).hasSize(6)!}.
Combining these changes would be impossible without access to information
about the old and new state of \emph{individual abstract-syntax elements}.
Simple line-based information is insufficient, even in line-oriented
languages.

  Differencing and synchronization algorithms tend to follow a common framework --
compute the difference between two values
of some type |a|, and represent these changes in some type, |Patch a|.
The |diff| function \emph{computes} the differences
between two values of type |a|, whereas |apply| attempts to transform a
value according to the information stored in the |Patch| provided to it.

\begin{myhs}
\begin{code}
diff   :: a -> a -> Patch a
apply  :: Patch a -> a -> Maybe a
\end{code}
\end{myhs}

  A definition of |Patch a| which has access to information about the
structure of |a| enables us to represent changes at a more refined
granularity.  In
\Cref{chap:structural-patches,chap:pattern-expression-patches} we
discuss two different definitions of |Patch|, both capturing changes
at the granularity of abstract-syntax elements.

  Note that the |apply| function is inherently partial, for example, when attempting
to delete data which is not present applying the patch will fail.
Yet when it succeeds, the |apply|
function must return a value of type |a|. This may seem like an
obvious design choice, but this property does not hold for the
approaches~\cite{Asenov2017,Falleri2014} using \texttt{xml} or
\texttt{json} to represent abstract syntax trees, where the
result of applying a patch may produce ill-typed results, i.e.,
schema violations.

  \unixdiff{}~\cite{McIlroy1976} follows this very framework too, but
for the specific type of lines of text, taking |a| to be |[String]|.  It
represents patches as a series of insertions, deletions and copies of
lines and works by enumerating all possible patches that transform the
source into the destination and chooses the best such patch.  There
have been several attempts at generalizing these results to handle
arbitrary datatypes~\cite{Zhang1989,Demaine2007,Pawlik2012,Lempsink2009}, including
our own attempt discussed in \Cref{chap:structural-patches}.
All of these follow the same recipe: enumerate all combinations of
insertions, deletions and
copies that transform the source into the destination and choose the
`best' one. Consequently, they also suffer from the same
drawbacks as classic edit-distance -- which include non-uniqueness of the best solution
and slow algorithms. We will discuss them in more detail in \Cref{sec:background:string-edit-distance}.

  Once we have a |diff| and an |apply| functions handy, we
move on to the |merge| function, which is responsible for
synchronizing two different changes into a single
one, when they are compatible. Naturally not all patches can be merged,
in fact, we can only merge those patches that alter \emph{disjoint} parts of the AST.
Hence, the merge function must be partial, returning a conflict whenever
patches change the same part of the tree in different ways.

\begin{myhs}
\begin{code}
merge :: Patch a -> Patch a -> Either Conflicts (Patch a)
\end{code}
\end{myhs}

  A realistic merge function should naturally distribute conflicts
to their specific locations inside the merged patch and still try to
synchronize non-conflicting parts of the changes. This is orthogonal
to our objective, however. The abstract idea is still the same:
two patches can either be reconciled fully or there exists conflicts
between them.

  The success rate of the |merge| function -- that is, how often it
is able to reconcile changes -- can never be 100\%. There will always be
changes that require human intervention to be synchronized.
Nevertheless, the quality of the synchronization algorithm directly
depends on the expressivity of the |Patch| datatype.
If |Patch| provides information solely on which lines of the source have changed,
there is little we can merge.  Hence, we want that values of type |Patch| to
carry information about the structure of |a|.
% Think of, for example,
% |Patch JavaProg| being the type of changes that can be performed over \texttt{java}
% programs.
Naturally though, we do not want to build domain specific tools for each programming
language for which we wish to have source files under version control -- which would be
at least impractical. The better option is to use a \emph{generic representation},
which can be used to encode arbitrary programming languages, and describe
the |Patch| datatype generically.

  Structural differencing is a good example of the need for generic
programming: we would like to have differencing algorithms to work over
arbitrary datatypes, but maintaining the type-safety that a language
like Haskell provides. This added safety means that all the
manipulations we perform on the patches are guaranteed to never
produce ill-formed elements, which is a clear advantage
over using something like XML to represent our data, even though there
exists differencing tools that use XML as their underlying representation
for data.  We refer to these as \emph{untyped}
tree differencing algorithms in contrast
the \emph{typed} approach, which guarantees type safety by construction.

  The Haskell type-system is expressive enough to enable one to write
\emph{typed} generic programming algorithms. These algorithms, however,
can only be applied to datatypes that belong in the set of types
handled by the generic programming library of choice. For example,
the \texttt{regular}~\cite{Noort2008} approach is capable of handling types which have
a \emph{regular} recursive structure -- lists, $n$-ary trees, etc --, but
cannot represent nested types, for example. In \Cref{sec:background:generic-programming}
we will give an overview of existing approaches to generic programming in Haskell.
No library, however, was capable of handling mutually recursive
types -- which is the universe of datatypes that context free languages belong in --
in a satisfactory manner. This means that to explore differencing
algorithms for various programming languages we would have to first
develop the generic programming functionality necessary for it.
Gladly, Haskell's type system has evolved enough since the initial
efforts on generic programming for mutually recursive types
(\texttt{multirec}~\cite{Yakushev2009}), enabling us to write significantly
better libraries, as we will discuss in \Cref{chap:generic-programming}.

\section{Contributions and Outline}
\label{sec:intro:contributions}

  This thesis documents a number of peer-reviewed contributions,
namely:

\begin{enumerate}
  \item \Cref{chap:generic-programming} discusses the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, which offers
combinator-based generic programming for mutually recursive
families. This work came out of close collaboration with Alejandro
Serrano on a variety of generic programming topics.

  \item \Cref{chap:structural-patches} is derived from a paper published
with \cite{Miraldo2017} with Pierre-\'{E}variste
Dagand. We worked closely together to define a type-indexed datatype
used to represent changes in a more structured way than edit-scripts.
\Cref{chap:structural-patches} goes further into developing
a merging algorithm and exploring different ways to compute
patches given two concrete values.

  \item \Cref{chap:pattern-expression-patches} is the refinement
of our paper~\cite{Miraldo2019} on an efficient algorithm for
computing patches, where we tackle the problems from
\Cref{chap:structural-patches} with a different representation
for patches altogether.
\end{enumerate}

  Other contributions that have not been peer-reviewed include:

\begin{enumerate}[resume]
  \item \Cref{chap:generic-programming} discusses the
\texttt{generics-simplistic} library, a different approach to generic
programming that overcomes an important space leak in the Haskell compiler,
which rendered \texttt{generics-mrsop} unusable in large, real-world, examples.

  \item \Cref{chap:pattern-expression-patches} introduces a merging
algorithm and \Cref{chap:experiments} discusses its empirical evaluation
over a dataset of real conflicts extracted from \texttt{GitHub}.
\end{enumerate}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
