  The most popular tool for computing differences
between two files is the \unixdiff{}~\cite{McIlroy1976},
it works by comparing files in a \emph{line-by-line} basis and
attempts to match lines from the source file to lines
in the destination file. For example, consider the
two files below:

{
\footnotesize
\begin{minipage}{.45\textwidth}
\begin{alltt}
1    res := 0;
2    for (i in is) \{
3      res += i;
4    \}
\end{alltt}
\end{minipage}\qquad%
\begin{minipage}{.45\textwidth}
\begin{alltt}
1    print("summing up");
2    sum := 0;
3    for (i in is) \{
4      sum += i;
5    \}
\end{alltt}
\end{minipage}
}

  Lines 2 and 4 in the source file, on the left, match
lines 3 and 5 in the destination. These are identified
as copies. The rest of the lines, with no matches,
are marked as deletions or insertions. In this example,
lines 1 and 3 in the source are deleted and lines
1,2 and 4 in the destination are inserted.

  This information about which lines have been \emph{copied},
\emph{deleted} or \emph{inserted} is then packaged into
an \emph{edit-script}: a list of operations that transforms
the source file into the destination file. For the example above,
the edit-script would read something like: delete the first line;
insert two new lines; copy a line; delete a line; insert a line
and finally copy the last line. The output we would see from
the \unixdiff{} would show deletions prefixed with a minus sign
and insertions prefixed with a plus sign. Copies have no prefix.
In our case, it would look something like:%
\begin{alltt}\footnotesize
-    res := 0;
+    print("summing up");
+    sum := 0;
     for (i in is) \{
-      res += i;
+      sum += i;
     \}
\end{alltt}

  The edit-scripts produced by the \unixdiff{} contain information
about transforming the source into the destination file by operating
exclusively at the \emph{lines-of-code} level.
Computing and representing differences
in a finer granularity than \emph{lines-of-code} is usually done
by parsing the data into a tree and later flattening said
tree into a list of nodes, where one then reuses existing
techniques for computing differences over lists, \ie{}, think
of printing each constructor of the tree into its own line.
This is precisely how most of the classic work on tree edit distance
computes tree differences (\Cref{sec:background:tree-edit-distance}).

  Recycling linear edit distance into tree edit distance, however,
also comes with its drawbacks. Linear differencing uses \emph{
edit-scripts} to represent the differences between two objects.  Edit-scripts
are composed of atomic operations, which traditionally include
operations such as \emph{insert}, \emph{delete} and \emph{copy}. These
scripts are later interpreted by the application function, which gives
the semantics to these operations. The notion of \emph{edit distance}
between two objects is defined as the cost of the least cost
\emph{edit-script} between them, where cost is some defined metric,
often context dependent. One major drawback, for example, is the least
cost edit-script is chosen arbitrarily in some situations, namely,
when it is not unique. This makes the results computed by these
algorithms hard to predict. Another issue, perhaps even more central,
are the algorithms that arise from this ambiguity which are inherently slow.

  The algorithms computing edit-scripts must either
return an approximation of the least cost edit-script or check
countless ambiguous choices to return the optimal one.  Finally,
manipulating edit-scripts in an untyped fashion, say, for instance in
order to merge then, might produce ill-typed trees -- as in \emph{not
abiding by a schema} -- as a result~\cite{Vassena2016}.  We can get
around this last issue by writing edit-scripts in a typed
form~\cite{Lempsink2009}, but this requires some non-trivial generic
programming techniques to scale.

  The second half of this chapter is the
state-of-the-art of the generic programming ecosystem in Haskell. Including
the \texttt{GHC.Generics} and \texttt{generics-sop}
libraries, which introduce all the necessary parts for us to build
our own solutions later, in \Cref{chap:generic-programming}.

\section{Differencing and Edit Distance}
\label{sec:background:tree-edit-dist}

  The \emph{edit distance} between two objects is
defined as the cost of the least-cost edit-script that transforms
the source object into the target object -- that is,
the edit-script with the least insertions and deletions.
Computing edit-scripts is often referred to as \emph{differencing} objects.
Where edit distance computation is only concerned with how
\emph{similar} one object is to another, \emph{differencing},
on the other hand, is actually concerned with how to transform
one objects into another. Although very closely related, these do make up
different problems.
In the biology domain \cite{Akutsu2010b,Henikoff1992,McKenna2010},
for example, one is concerned solely in finding similar
structures in a large set of structures, whereas
in software version control systems manipulating and combining
differences is important.

  The wide applicability of differencing and edit distances
leads to a variety of cost notions, edit-script
operations and algorithms for computing them~\cite{Bille2005,Bergroth2000,Paassen2018}. In this section we will review some of the important notions and
background work on edit distance. We start by looking at the string
edit distance (\Cref{sec:background:string-edit-distance}) and then
generalize this to untyped trees (\Cref{sec:background:tree-edit-distance}),
as it is classically portrayed in the literature, which
is reviewed in \Cref{sec:background:literature-review}.
Finally, we discuss some of the consequences of working with
typed trees in \Cref{sec:gp:well-typed-tree-diff}.

\subsection{String Edit Distance and \unixdiff{}}
\label{sec:background:string-edit-distance}

   In this section we look at two popular notions of edit distance.  The
\emph{Levenshtein Distance}~\cite{Levenshtein1966,Bergroth2000}, for
example, works well for detecting spelling mistakes\cite{Navarro2001}
or measuring how similar two languages are \cite{Thije2007}.
It considers insertions, deletions and substitutions of
characters as its edit operations. The \emph{Longest Common
Subsequence (LCS)}~\cite{Bergroth2000}, on the other hand, considers
insertions, deletions and copies as edit operations and is better
suited for identifying shared sequences between strings.

\paragraph{Levenshtein Distance}
The Levenshtein distance regards insertions, deletions and
substitutions of characters as edit operations, which can
be modeled in Haskell by the |EditOp| datatype below. Each of those
operations have a predefined \emph{cost} metric.

\begin{myhs}
\begin{code}
data EditOp = Ins Char | Del Char | Subst Char Char

cost :: EditOp -> Int
cost (Ins _)      = 1
cost (Del _)      = 1
cost (Subst c d)  = if c == d then 0 else 1
\end{code}
\end{myhs}

  These individual operations are then grouped into a list, usually
denoted an \emph{edit-script}. The |apply| function, below, gives
edit-scripts a denotational semantics by mapping them to partial
functions over |String|s.

\begin{myhs}
\begin{code}
apply :: [EditOp] -> String -> Maybe String
apply []                  []         = Just []
apply (Ins c      : ops)        ss   = (c :) <$$> apply ops ss
apply (Del c      : ops)  (s :  ss)  = guard (c == s) >> apply ops ss
apply (Subst c d  : ops)  (s :  ss)  = guard (c == s) >> (d :) <$$> apply ops ss
\end{code}
\end{myhs}

  The |cost| metric associated with these edit operations is defined
to force substitutions to cost less than insertions and deletions.
This ensures that the algorithm looking for the list of edit operations
with the minimum cost will prefer substitutions over deletions
and insertions.

  We can compute the \emph{edit-script}, i.e. a
list of edit operations, with the minimum cost quite easily with a
brute-force and inefficient implementation.
\Cref{fig:background:string-leveshtein} shows the
implementation of the edit-script with the minimum Levenshtein
distance.

\begin{figure}
\begin{myhs}
\begin{code}
lev :: String -> String -> [EditOp]
lev []      []      = []
lev (x:xs)  []      = Del x : lev xs []
lev []      (y:ys)  = Ins y : lev [] ys
lev (x:xs)  (y:ys)  =  let  i = Ins y      : lev (x:  xs)      ys
                            d = Del x      : lev      xs  (y:  ys)
                            s = Subst x y  : lev      xs       ys
                       in minimumBy cost [i , d , s]
\end{code}
\end{myhs}
\caption{Definition of the function that returns the
edit-script with the minimum Levenshtein Distance between two strings.}
\label{fig:background:string-leveshtein}
\end{figure}

\begin{myhs}
\begin{code}
levenshteinDist :: String -> String -> Int
levenshteinDist s d = cost (head (lev s d))
\end{code}
\end{myhs}

  Note that although the Levenshtein distance is unique, the edit-scripts
witnessing it is \emph{not}. Consider the case of |lev "ab" "ba"|
for instance. All of the edit-scripts below have cost 2, which is the
minimum possible cost.

\begin{myhs}
\begin{code}
lev "ab" "ba" `elem` [ [ Del 'a' , Subst 'b' 'b' , Ins 'a']
                     , [ Ins 'b' , Subst 'a' 'a' , Del 'b']
                     , [ Subst 'a' 'b' , Subst 'b' 'a' ]]
\end{code}
\end{myhs}

  From a edit distance point of view, there is not an issue. The Levenshtein
distance between |"ab"| and |"ba"| is 2, regardless of the edit-script.
But from an operational point of view,
, \ie, transforming one string into another, this ambiguity
poses a problem. The lack of criteria to favor one edit-script over another
means that the result of the differencing algorithm is hard to predict.
Consequently, developing a predictable diff and merging algorithm
becomes a difficult task.

\subsubsection*{Longest Common Subsequence}

  Given our context of source-code version-control,
we are rather interested in the \emph{Longest Common Subsequence (LCS)},
which is a restriction of the Levenshtein distance and forms
the specification of the \unixdiff{}~\cite{McIlroy1976} utility.

  If we take the |lev| function and modify it in such a way that it only
considers identity substitutions, that is, |Subst x y| with |x == y|,
we end up with a function that computes the classic longest common
subsequence. Note that this is different from the longest common
substring problem, as subsequences need not be contiguous.

  \unixdiff{}~\cite{McIlroy1976} performs a slight generalization
of the LCS problem by considering the distance between two
\emph{files}, seen as a list of \emph{strings}, opposed to a list of
\emph{characters}. Hence, the edit operations become:

\begin{myhs}
\begin{code}
data EditOp = Ins String | Del String | Cpy

cost :: EditOp -> Int
cost (Ins _)  = 1
cost (Del _)  = 1
cost Cpy      = 0
\end{code}
\end{myhs}

  The application function is analogous to the |apply| for the Levenshtein
distance. The computation of the minimum cost edit-script, however,
is not. We must ensure to issue a |Cpy| only when both elements
are the same, as illustrated in \Cref{fig:background:string-lcs}.

\begin{figure}
\begin{myhs}
\begin{code}
lcs :: [String] -> [String] -> [EditOp]
lcs []      []      = []
lcs (x:xs)  []      = Del x : lcs xs []
lcs []      (y:ys)  = Ins y : lcs [] ys
lcs (x:xs)  (y:ys)  =  let  i  = Ins y      : lcs (x:  xs)      ys
                            d  = Del x      : lcs      xs  (y:  ys)
                            s  = if x == y then [Cpy : lcs xs ys] else []
                       in minimumBy cost (s ++ [i , d])
\end{code}
\end{myhs}
\caption{Specification of the \unixdiff{}.}
\label{fig:background:string-lcs}
\end{figure}

  Running the |lcs x y| function, \Cref{fig:background:string-lcs}, will
yield an \emph{edit-script} that enables us to read out one longest
common subsequence of |x| and |y|. Note that the ambiguity problem is
still present, however to a lesser degree than with
the Levenshtein distance. For example, there are only two edit-scripts
with minimum cost on |lcs ["a", "b"] ["b" , "a"]|. This, in fact,
is a general problem with any \emph{edit-script} based approaches.

  The \unixdiff{} implementation uses a number of
algorithmic techniques that make it performant. First, it is
essential to use a memoized |lcs| function to avoid recomputing
sub-problems. It is also common to hash the data being compared to have
amortized constant time comparison. More complicated, however, is the
adoption of a number of heuristics that tend to perform well in practice.
One example is the \texttt{diff --patience} algorithm~\cite{patienceDiff},
that will emphasize the matching of lines that appear only once in the
source and destination files.

\subsection{Classic Tree Edit Distance}
\label{sec:background:tree-edit-distance}

  \unixdiff{} can be generalized to compute an edit-script
between lists containing data of arbitrary types.
The only requirement being that we must be able to
compare this data for equality. Generalizing over the shape of the data
-- trees instead of lists -- gives rise to the notion of (untyped) tree edit
distance~\cite{Akutsu2010,Demaine2007,Klein1998,%
Bille2005,Autexier2015,Chawathe1997}.
It considers \emph{arbitrary} trees as the objects under
scrutiny. This added degree of freedom carries over to the choice of
edit operations. Suddenly, there are more edit operations one
could use to create edit-scripts. To name a few, we can have
flattening insertions and deletions, where the children of the deleted
node are inserted or removed in-place in the parent node. Another
operation that only exists in the untyped world is node relabeling.
This degree of variation is responsible for the high
number of different approaches and techniques we see in
practice~\cite{Farinier2015,Hashimoto2008,Falleri2014,Paassen2018,Finis2013},
\Cref{sec:background:literature-review}.

\begin{figure}
\centering
\begin{tikzpicture}
\node (f1) at (0, 0) {\begin{forest}
    [, s sep=0mm
     [a , no edge , l = 0mm [b] [c]]
     [|::|, no edge , l = 0mm]
     [d , no edge , l = 0mm]
     [|::|, no edge , l = 0mm]
     [e , no edge , l = 0mm [f]]
     [|::|, no edge , l = 0mm]
     [|...|, no edge, l = 0mm]
    ]
  \end{forest}};
\node (f2) at (6, 0) {\begin{forest}
    [, s sep=0mm
     [x , no edge , l = 0mm [a [b] [c]] [d]]
     [|::|, no edge , l = 0mm]
     [e , no edge , l = 0mm [f]]
     [|...|, no edge, l = 0mm]
    ]
  \end{forest}};
\draw[->] ($ (f1.east) + (0,0.15) $)
          to[out=45,in=135] node[midway,above] {|ins x|}
          ($ (f2.west) + (0,0.15) $);
\draw[->] ($ (f2.west) - (0,0.15) $)
          to[out=225,in=315] node[midway,below] {|del x|}
          ($ (f1.east) - (0,0.15) $);
\end{tikzpicture}
\caption{Insertion and Deletion of node |x|, with arity 2
on a forest}
\label{fig:background:tree-es-operations}
\end{figure}

  Basic tree edit distance~\cite{Demaine2007}, however, considers only
node insertions, deletions and copies. The cost function is borrowed
entirely from string edit distance together with the longest common
subsequence function, that instead of working with |[a]| will now work
with |[Tree]|. \Cref{fig:background:tree-es-operations} illustrates
insertions and deletions of (untyped) labels on a forest.
The interpretation of these edit operations as actions
on forests is shown in \Cref{fig:background:apply-tree-edit}.

\begin{figure}
\begin{myhs}
\begin{code}
data EOp  = Ins Label | Del Label | Cpy
data Tree = Node Label [Tree]

arity :: Label -> Int

apply :: [EOp] -> [Tree] -> Maybe [Tree]
apply []                           []   = Just []
apply (Cpy    : ops)               ts   = apply (Ins l : Del l : ops) ts
apply (Del l  : ops) (Node l' xs:  ts)  = guard (l == l') >> apply ops (xs ++ ts)
apply (Ins l  : ops) ts
  = (\(args , rs) -> Node l args : rs) . takeDrop (arity l) <$$> apply ops ts
\end{code}
\end{myhs}
\caption{Definition of |apply| for tree edit operations}
\label{fig:background:apply-tree-edit}
\end{figure}

  We label these approaches as \emph{untyped} because there exists edit-scripts
that yield non-well formed trees. For example, imagine |l| is
a label with arity 2 -- supposed to receive two
arguments. Now consider the edit-script |Ins l : []|, which will yield
the tree |Node l []| once applied to the empty forest. If the objects
under differencing are required to abide by a certain schema, such as
abstract syntax trees for example, this becomes an issue.  This is
particularly important when one wants the ability to manipulate
patches independently of the objects they have been created from.
Imagine a merge function that needs to construct a patch
based on two other patches. A wrong implementation of said merge function
can yield invalid trees for some given schema. In the context of
abstract-syntax, this could be unparseable programs.

  It is possible to use the Haskell type system to our advantage and
write |EOp| in a way that it is guaranteed to return well-typed
results. Labels will be the different constructors of the family of
types in question and their arity comes from how many fields each
constructor expects. edit-scripts will then be indexes by two lists of
types: the types of the trees it consumes and the types of the trees
it produces. We will come back to this in more detail in
\Cref{sec:gp:well-typed-tree-diff}, where we review the approach of
Lempsink and L\"{o}h~\cite{Lempsink2009} at adapting this untyped framework
to be type-safe by construction.

  Although edit-scripts provide a very intuitive notion of local
transformations over a tree, there are many different edit-scripts
that perform the same transformation: the order of
insertions and deletions do no matter. This makes it hard to
develop algorithms based solely on edit-scripts.
The notion of \emph{tree mapping} often comes in handy. It works as
a \emph{normal form} version of edit-scripts and represents only the
nodes that are either relabeled or copied. We must impose a series of
restrictions on these mappings to maintain the ability to
produce edit-scripts out of it. \Cref{fig:background:tree-mapping}
illustrates four invalid and one valid such mappings.

\begin{definition}[Tree Mapping] \label{def:background:tree-mapping}
Let |t| and |u| be two trees, a tree mapping
between |t| and |u| is an order preserving partial bijection between the
nodes of a flattened representation of |t| and |u| according
to their preorder traversal. Moreover, it preserves the
ancestral order of nodes. That is, given two subtrees |x| and |y| in
the domain of the mapping |m|, then |x| is an ancestor of |y| if and only if
|m x| is an ancestor of |m y|.
\end{definition}

\begin{figure}
\centering
\subfloat[non order preserving]{%
\begin{forest}
[, change={white}{} , s sep=8mm
  [b,name=sb [c [d] [e, name=se]] [f , name=sf]]
  [g,name=df [b , name=db] [e, name=de]]]
\draw [->,dashed,thick,black!20!white] (sb) -- (db);
\draw [->,dashed,thick,black!20!white] (sf) -- (df);
% this edge makes it non-acestry preserving too!
% \draw [->,dashed,thick,black!20!white] (se) -- (de);
\end{forest}%
\label{fig:background:tree-mapping-a}}%
\qquad%
\subfloat[non injective]{%
\raisebox{9mm}{
\begin{forest}
[, change={white}{} , s sep=8mm
  [b,name=sb [c] [d]]
  [b,name=db [b , name=dbb] [e]]]
\draw [->,dashed,thick,black!20!white] (sb) -- (db);
\draw [->,dashed,thick,black!20!white] (sb) -- (dbb);
\end{forest}%
\label{fig:background:tree-mapping-b}}}%
\qquad%
\subfloat[non surjective]{%
\begin{forest}
[, change={white}{} , s sep=8mm
  [b,name=sb [c] [d,name=sd]]
  [a [f,name=df [g] [h]] [e]]]
\draw [->,dashed,thick,black!20!white] (sb) -- (df);
\draw [->,dashed,thick,black!20!white] (sd) -- (df);
\end{forest}%
\label{fig:background:tree-mapping-c}}%
\qquad%
\subfloat[non ancestral preserving]{%
\raisebox{9mm}{%
\begin{forest}
[, change={white}{} , s sep=8mm
  [a,name=sb [b [c] [d,name=sd]] [e,name=se]]
  [f,name=df [g, name=dg]]]
\draw [->,dashed,thick,black!20!white] (sd) -- (df);
\draw [->,dashed,thick,black!20!white] (se) -- (dg);
\end{forest}%
\label{fig:background:tree-mapping-d}}}%
\qquad\qquad\qquad\qquad\qquad%
\subfloat[valid tree mapping]{%
\begin{forest}
[, change={white}{}, s sep=8mm
  [a,name=sa [b,name=sb [c] [d]] [e,name=se]]
  [f [a, name=da [g [b,name=db]] [e,name=de]] [h]]]
\draw [->,dashed,thick,black!20!white] (sa) -- (da);
\draw [->,dashed,thick,black!20!white] (sb) -- (db);
\draw [->,dashed,thick,black!20!white] (se) to[out=290] (de);
\end{forest}%
\label{fig:background:tree-mapping-e}}%
\caption{A number of invalid invalid tree mappings with one valid
example.}
\label{fig:background:tree-mapping}
\end{figure}

   The tree mapping determines the nodes where either a copy or substitution
must be performed. Everything else must be deleted or inserted and the
order of deletions and insertions is irrelevant, which removes the redundancy
of edit-scripts. Nevertheless, the definition of tree mapping is still very restrictive:
(i) the ``bijective mapping'' does not enable trees to be duplicated or contracted;
(ii) the ``order preserving'' does not enable trees to be permuted or moved
across ancestor boundaries. These restrictions are there to ensure that
one can always compute an edit-script from a tree mapping.

  Most tree differencing algorithms start by producing a tree mapping and
then extracting an edit-script from this. There are a plethora of design
decisions on how to produce a mapping and often the domain of application
of the tool will enable one to impose extra restrictions to attempt to squeeze
maximum performance out of the algorithm. The \texttt{LaDiff}~\cite{Chawathe1996} tool,
for example, works for hierarchically structured trees -- used primarily for
\LaTeX source files -- and uses a variant of the LCS to compute matchings of elements
appearing in the same order, starting at the leaves of the document.
Tools such as \texttt{XyDiff}~\cite{Marian2002}, used to identify changes in XML documents,
use hashes to produce matchings efficiently.

\subsection{Shortcomings of Edit-Script Based Approaches}

  We argue that regardless of the process by which an edit-script is obtained,
edit-scripts have inherent shortcomings when they
are used to compare tree structured data. The first and most striking
is that the use of heuristics to compute optimal solutions is unavoidable.
Consider the tree-edit-scripts between the following two trees:
\nopagebreak[4]
\begin{center}
\begin{forest}
[, change={white}{} , s sep=12mm
  [|Bin| [|T|] [|U|]]
  [|Bin| [|U|] [|T|]]]
\end{forest}
\end{center}

  From an \emph{edit distance} point of view, their distance is
2. This fact can be witnessed by two distinct edit-scripts: either
|[Cpy Bin , Del T , Cpy U , Ins T]| or |[Cpy Bin , Ins U , Cpy T , Del
U]| transform the target into the destination correctly. Yet, from
a \emph{differencing} point of view, these two edit-scripts are fairly different.
Do we care more about |U| or |T|? What if |U| and |T| are also
trees, but happen to have the same size (so that inserting one or the
other yields edit-scripts with equal costs)? Ultimately,
differencing algorithms that support no \emph{swap} operation
must choose to copy |T| or |U| arbitrarily. This decision is often
guided by heuristics, which makes the result of different algorithms
hard to predict. Moreover, the existence of this type of choice point inherently
slows algorithms down since the algorithm \emph{must decide} which
tree to copy.

  Another issue when dealing with edit-script is
that they are type unsafe. It is quite easy to write an edit-script
that produces an \emph{ill-formed} tree, according to some
arbitrary schema. Even when writing the edit operations in a
type-safe way~\cite{Lempsink2009} the synchronization of said changes
is not guaranteed to be type-safe~\cite{Vassena2016}.

  Finally, we must mention the lack of expressivity that comes from edit-scripts,
from the \emph{differencing} point of view. Consider the trees below,
\nopagebreak[4]
\begin{center}
\begin{forest}
[, change={white}{} , s sep=12mm
  [|A|]
  [|Bin| [|A|] [|A|]]]
\end{forest}
\end{center}

  Optimal edit-scripts oblige us to chose between copying |A|
as the left or the right subtree. There is no possibility to represent
duplications, permutations or contractions of subtrees. This means
that a number of common changes, such as refactorings, yield
edit-scripts with a very high cost even though a good part of the information
being deleted or inserted should really have been copied.

\subsection{Synchronizing Changes}
\label{sec:background:synchronizing-changes}

  When managing local copies of replicated data such as in software
version control systems, one is inevitably faced with the problem of
\emph{synchronizing}~\cite{Balasubramaniam1998} or \emph{merging}
changes -- when an offline machine goes online with new versions,
when two changes happened simultaneously, etc. The \emph{synchronizer}
is responsible to identify what has changed and reconcile these
changes when possible.  Most modern synchronizers operate over the
diverging replicas and last common version, without knowledge of the
history of the last common version -- these are often denoted
\emph{state-based} synchronizers, as opposed to \emph{operation-based}
synchronizers, which access the whole history of modifications.

   The \texttt{diff3}~\cite{Smith1988} tool, for example, is the
most widely used synchronizer for textual data.
It is a \emph{state-based} that calls the \unixdiff{} to compute
the differences between the common ancestor and each diverging replica,
then tries to produce an edit-script that when applied to the common
ancestor produces a new file, containing the union of changes introduced
in each individual replica. The algorithm itself has been studied
formally~\cite{Khanna2007} and there are proposals to extend
it to tree-shaped data~\cite{Lindholm2004,Vassena2016}.

\begin{figure}
\centering
\subfloat[Three-way based merge operation]{%
\qquad $$
\xymatrix{ & O \ar[dl]_{p} \ar[dr]^{q} \ar[dd]^(0.8){|merge p q|} & \\
          A & & B \\
            & M &}
$$ \qquad
\label{fig:background:mergesquare-threeway}}
\qquad%
\subfloat[Residual based merge operation]{%
\qquad $$
\xymatrix{ & O \ar[dl]_{p} \ar[dr]^{q} & \\
          A \ar[dr]_{|merge q p|} & & B \ar[dl]^{|merge p q|} \\
            & M &}
$$ \qquad
\label{fig:background:mergesquare-resid}}%
\caption{Two different ways to look at the merge problem.}
\label{fig:background:mergesquare}
\end{figure}

  Generally speaking, synchronization of changes $p$ and $q$ can be
modeled in one of two ways. Either we produce one change that works
on the common ancestor of $p$ and $q$, as in
\Cref{fig:background:mergesquare-threeway}, or we produce two changes
that act directly on the images of $p$ and $q$,
\Cref{fig:background:mergesquare-resid}.  We often call the former
a \emph{three-way merge} and the later a \emph{residual} merge.

  Residual merges, specially if based on actual residual
systems~\cite{Terese2003} pose a few technical challenges --- proving
the that the laws required for establishing an actual residual system
is non-trivial. Moreover, they tend to be harder to generalize
to $n$-ary inputs. They do have the advantage of enabling one to
model merges as pushouts~\cite{Mimram2013}, which could provide a desirable
metatheoretical foundation.

\begin{figure}
\footnotesize \centering
\subfloat[Replica \texttt{A}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
  sum := 0;
  for (i in is) {
    sum := sum + i;
  }
\end{verbatim}
\end{minipage}}
\qquad%
\subfloat[Common ancestor, \texttt{O}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
  res := 0;
  for (i in is) {
    res := res + i;
  }
\end{verbatim}
\end{minipage}}
\qquad%
\subfloat[Replica \texttt{B}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
  res := 0;
  sum := 0;
  for (i in is) {
    res := res + i;
    sum := sum + i;
  }
\end{verbatim}
\end{minipage}}
\qquad%

\subfloat[\texttt{diff O A}]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
- res := 0;
+ sum := 0;
  for (i in is) {
-   res := res + i;
+   sum := sum + i;
  }
\end{verbatim}
\end{minipage}}
\qquad\qquad\qquad%
\subfloat[\texttt{diff O B}]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
  res := 0;
+ prod := 1;
  for (i in is) {
    res := res + i;
+   prod := prod * i;
  }
\end{verbatim}
\end{minipage}}
\caption{Two \unixdiff{} patches that diverge from a common ancestor.}
\label{fig:background:diff3-example}
\end{figure}

  Regardless of whether we choose a \emph{three-way} or \emph{residual} based
approach, any state-based synchronizer will invariably have to deal
with the problem of \emph{aligning} the changes. That is, deciding
which parts of the replicas are copies from the same piece of
information in the common ancestor. For example, successfully
synchronizing the replicas in \Cref{fig:background:diff3-example}
depends in recognizing that the insertion of {\small \verb!prod := 1;!}
comes after modifying {\small \verb!res := 0;!}
to {\small \verb!sum := 0;!}. This fact only becomes evident after
we look at the result of calling the \unixdiff{} on each diverging
replica -- the copies in each patch identify which parts of the
replicas are 'the same'.

\begin{figure}
\subfloat[][inputs]{%
\begin{myhs}[.45\textwidth]
\begin{code}
a = [1,4,5,2,3,6]
o = [1,2,3,4,5,6]
b = [1,2,4,5,3,6]
\end{code}
\end{myhs}
\label{fig:background:example-diff3:inputs}}%
\hfill%
\subfloat[][Running \texttt{diff} to produce alignments]{%
\begin{myhs}[.5\textwidth]
\begin{code}
diff o a =  [ Cpy 1 , Ins 4 , Ins 5 ,  Cpy 2
            , Cpy 3 , Del 4 , Del 5 , Cpy 5]

diff o b =  [ Cpy 1 , Cpy 2 , Del 3 , Cpy 4
            , Cpy 5 , Ins 3 , Cpy 6]
\end{code}
\end{myhs}
\label{fig:background:example-diff3:align}}%

\subfloat[][\texttt{diff3} parse of alignments]{%
\begin{tabular}{c||c||c||c||c||c}
a & 1 & 4,5 & 2 & 3 & 6 \\
o & 1 &     & 2 & 3,4,5 & 6 \\
b & 1 &     & 2 & 4,5,3 & 6 \\
\end{tabular}
\label{fig:background:example-diff3:parse}}%
\hfill%
\subfloat[][\texttt{diff3} propagate]{%
\begin{tabular}{c||c||c||c||c||c}
a & 1 & 4,5 & 2 & 3 & 6 \\
o & 1 & 4,5 & 2 & 3,4,5 & 6 \\
b & 1 & 4,5 & 2 & 4,5,3 & 6 \\
\end{tabular}
\label{fig:background:example-diff3:propagate}}%
\caption{A simple \texttt{diff3} run}
\label{fig:background:example-diff3}
\end{figure}

  \Cref{fig:background:example-diff3} illustrates a run of \texttt{diff3}
in a simple example, borrowed from Khanna et al.~\cite{Khanna2007}, where
Alice swaps $2,3$ for $4,5$ in the original file but Bob moves $3$ before $6$.
In a very simplified way, the first thing that happens if we run \texttt{diff3} in the inputs
(\Cref{fig:background:example-diff3:inputs}) is that \texttt{diff3}
will compute the longest common subsequences between the objects, essentialy
yielding the alignments it needs (\Cref{fig:background:example-diff3:align}).
The next step is to put the copies side by side and understand which regions
are \emph{stable} or \emph{unstable}. The stable regions are those where
no replicas changed. In our case, its on $1$, $2$ and $6$ (\Cref{fig:background:example-diff3:parse}).
Finally, \texttt{diff3} can decide which changes to propagate and which
changes are a conflict. In our case, the $4,5$ was only changed in one replica,
so it is safe to propagate (\Cref{fig:background:example-diff3:propagate}).

  Different synchronization algorithms will naturally offer
slightly different properties, yet, one that seems to be central to
synchronization is locality~\cite{Khanna2007} -- which is enjoyed by
\texttt{diff3}~\cite{Khanna2007}.  Locality states that changes to
distinct locations of a given object can always be synchronized
without conflicts. In fact, we argue this is the only property we can
expect out of a general purpose generic synchronizer.  The reason
being that said synchronizer can rely solely on propositional
equality of trees and structural disjointness as the criteria to
estabilish changes as synchronizable.  Other criteria will invariantly
require knowledge of the semantics of the data under
synchronization. It is worth noting that although ``distinct locations''
is difficult to define for an underlying list, tree shaped data has
the advantage of possessing simpler such notions.

\subsection{Literature Review}
\label{sec:background:literature-review}

  With some basic knowledge of differencing and edit-distances under
our belt, we briefly look over some of the relevant literature on the
topic. Zhang and Sasha~\cite{Zhang1989} where perhaps the first to
provide a number of algorithms which were later improved on by Klein
et al.~\cite{Klein1998} and Dulucq et al.~\cite{Dulucq2003}. Finally,
Demaine et al.~\cite{Demaine2007} presents an algorithm of cubic
complexity and proves this is the best possible worst case. Zhang and
Sasha's algorithm is still preferred in many pratical scenarios,
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
\cite{Akutsu2010b,Henikoff1992,McKenna2010}, all the way to intelligent
tutoring systems where we must provide good hints to students'
solutions to exercises by understanding how far they are from the
correct solutions \cite{Paassen2017,Rohan2016}.  In fact, from the
\emph{tree edit distance} point of view, we are only concerned with a
number, the \emph{distance} between objects, quantifying how similar
they are.

  From the perspective of \emph{tree differencing}, on the other hand,
we actually care about the edit operations and might want to perform
computations such as composition and merging of
differences. Naturally, however, the choice of edit operations heavily
influences the complexity of the |diff| algorithm. Allowing a
\emph{move} operation already renders string differencing
NP-complete~\cite{Shapira2002}. Tree differencing algorithms,
therefore, tend to run approximations of the best edit distance. Most
of then still suffer from at least quadratic time complexity, which is
prohibitive for most pratical applications or are defined for domain
specific data, such as the \texttt{latexdiff}~\cite{LatexDiff} tool.
A number of algorithms specific for XML and imposing different
requirements on the schemas have been developped~\cite{Peters2005}.
\texttt{LaDiff}~\cite{Chawathe1996}, for example, imposes restrictions on the
hierarchy between labels, it is implemented into the
\texttt{DiffXML}~\cite{Mouat2002} and
\texttt{GumTree}~\cite{Falleri2014} tools and is responsible
from deducing an edit-script given tree matchings, the tree matching
phase differs in each tool. A notable mention is the
\texttt{XyDiff}~\cite{Marian2002}, which uses hashes to compute
matchings and, therefore, supports \emph{move} operations maintaining
almost linear complexity.  This is perhaps the closest to our approach
in \Cref{chap:pattern-expression-patches}. The
\texttt{RWS-Diff}~\cite{Finis2013} uses approximate matchings by
finding trees that are not necessarily equal but \emph{similar}. This
yields a robust algorithm, which is applicable in practice.
Most of these techniques recycle list differencing and can be seen
as some form of string differencing over the preorder (or postorder)
traversal of trees, which has quadratic upper bound~\cite{Guha2002}.
A careful encoding of the edit operations enables one to have edit-scripts
that are guaranteed to preserve the schema of the data under manipulation
\cite{Lempsink2009}.

  When it comes to synchronization of changes~\cite{Balasubramaniam1998},
the algorithms are
heavily dependent on the representation of objects and edit-scripts imposed
by the underlying differencing algorithm.
The \texttt{diff3}~\cite{Smith1988} tool, developed by Randy Smith in 1988, is still the
most widely used synchronizer. It has received a formal treatment
and specification \cite{Khanna2007} posterior to its development.
Algorithms for synchronizing changes over tree shaped data
include \texttt{3DM}~\cite{Lindholm2004} which merges
changes over XML documents, \texttt{Harmony}~\cite{Foster2007},
which works internally with unordered edge-labelled trees and is
focused primarily on unordered containers and, finally,
\texttt{FCDP}~\cite{Lanham2002}, which uses XML as its internal
representation.

   Also worth mentioning is the generalization of \texttt{diff3} to
tree structured data using well-typed approaches due to
Vassena~\cite{Vassena2016}, which shows that typed edit-scripts might
not be the best underlying framework for this, as one needs to
manually type-check the resulting edit-scripts.

  Besides source-code differencing there is patch inference and
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

\pagebreak
\section{Generic Programming}
\label{sec:background:generic-programming}

  We would like to consider richer datatypes than \emph{lines-of-text},
without having to define separate |diff| functions for each of them.
\emph{(Datatype-)generic programming}
provides a mechanism for writing functions by induction on
the \emph{structure} of algebraic datatypes~\cite{Gibbons2006}.
A widely used example is the |deriving| mechanism in Haskell, which
frees the programmer from writing repetitive functions such as
equality~\cite{haskell2010}. A
vast range of approaches are available as preprocessors, language
extensions, or libraries for Haskell~\cite{Rodriguez2008,Magalhaes2012}.

  The core idea behind generic programming is the fact that a number
of datatypes can be described in a uniform fashion.  Hence, if a
programmer were to write programs that work over this uniform
representation, these programs would immediately work over a variety
of datatypes. In this section we look into two modern approaches
to generic programming which are widely used, then discus their
design space and drawbacks.

\subsection{GHC Generics}
\label{sec:background:patternfunctors}

  The \texttt{GHC.Generics}~\cite{Magalhaes2010} library, which
comes bundled with GHC since version $7.2$ and
defines the representation of datatypes in terms of uniform
\emph{pattern functors}. Consider the following datatype of binary trees
with data stored in their leaves:

\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}

  A value of type |Bin a| consists of a choice between two
constructors.  For the first choice, it also contains a value of type
|a| whereas for the second it contains two subtrees as children. This
means that the |Bin a| type is isomorphic to |Either a (Bin a , Bin
a)|. Different libraries differ on how they define their underlying
representations. The representation of |Bin a| in
terms of \emph{pattern functors} is writen as:

\begin{myhs}
\begin{code}
Rep (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}

  The |Rep (Bin a)| above is a direct translation
of |Either a (Bin a , Bin a)|, but using
the combinators provided by \texttt{GHC.Generics}.
In addition, we also have two conversion functions |from :: a ->
Rep a| and |to :: Rep a -> a| which form an isomorphism between |Bin
a| and |Rep (Bin a)|.  The interface ties everything unser
a typeclass:

\begin{myhs}
\begin{code}
class Generic a where
  type Rep a :: Star
  from  :: a      -> Rep a
  to    :: Rep a  -> a
\end{code}
\end{myhs}

  Defining a generic function is done in two
steps. First, we define a class that exposes the function
for arbitrary types, in our case, |size|, which we implement
for any type via |gsize|:

\begin{myhs}
\begin{code}
class Size (a :: Star) where
  size :: a -> Int
instance (Size a) => Size (Bin a) where
  size = gsize . fromGen
\end{code}
\end{myhs}

  Next we define the |gsize| function that operates on the level of the
representation of datatypes. We have to use another class
and the instance mechanism to encode a definition by induction on
representations:

\begin{myhs}
\begin{code}
class GSize (rep :: Star -> Star) where
  gsize :: rep x -> Int
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}
\end{myhs}

  We still have to handle the cases where
we might have an arbitrary type in a position, modeled by the
constant functor |K1|. We require an instance of |Size|
so we can successfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size x) => GSize (K1 R x) where
  gsize (K1 x) = size x
\end{code}
\end{myhs}

\begin{figure}\centering
{\small
$\begin{array}{l}
  |size (Bin (Leaf 1) (Leaf 2))| \\
  \;  = |gsize (fromGen (Bin (Leaf 1) (Leaf 2)))| \\
  \;  = |gsize (R1 (K1 (Leaf 1) :*: K1 (Leaf 2)))| \\
  \;  = |gsize (K1 (Leaf 1)) + gsize (K1 (Leaf 2))| \\
  \;  \overset{\dagger}{=} |size (Leaf 1) + size (Leaf 2)| \\
  \;  = |gsize (fromGen (Leaf 1)) + gsize (fromGen (Leaf 2))|\\
  \;  = |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
  \;  = |size (1 :: Int) + size (2 :: Int)|
\end{array}$}
\caption{Reduction of |size (Bin (Leaf 1) (Leaf 2))|}
\label{fig:background:sizederiv}
\end{figure}

  To finish the description of the generic |size|,
we also need instances for the
\emph{unit}, \emph{void} and \emph{metadata} pattern functors,
called |U1|, |V1|, and |M1| respectively. Their |GSize| is
rather uninteresting, so we omit them for the sake of conciseness.

  This technique of \emph{mutually recursive classes} is quite
specific to the \texttt{GHC.Generics} flavor of generic programming.
\Cref{fig:background:sizederiv} illustrates how the compiler goes about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|.  In the end,
we just need an instance for |Size Int| to compute the final
result. Literals of type |Int| illustrate what we often call \emph{opaque
types}: those types that constitute the base of the universe
and are \emph{opaque} to the representation language.

\

\subsection{Explicit Sums of Products}
\label{sec:background:explicitsop}

  The other side of the coin is restricting
the shape of the generic values to follow a \emph{sums-of-products} format.
This was first done by L\"{o}h and de Vries\cite{deVries2014}
in the \texttt{generics-sop} library. The main difference is in the
introduction of \emph{Codes}, that limit the
structure of representations. If we had access to a representation of
the \emph{sum-of-products} structure of |Bin|, we could have defined
our |gsize| function following an informal description: sum up the
sizes of the fields inside a value, ignoring the constructor.

  Unlike \texttt{GHC.Generics}, the representation of values is
defined by induction on the \emph{code} of a datatype, this
\emph{code} is a type-level list of lists of kind |Star|, whose
semantics is consonant to a formula in disjunctive normal form.  The
outer list is interpreted as a sum and each of the inner lists as a
product.  This section provides an overview of \texttt{generic-sop} as
required to understand the techniques we use in
\Cref{chap:generic-programming}. We refer the reader to the original
paper~\cite{deVries2014} for a more comprehensive explanation.

  Using a \emph{sum-of-products} approach one could write the same |gsize|
function shown in \Cref{sec:background:patternfunctors} as easily as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of |gsize| for a moment, let us focus just on
its high level structure. Remembering that |from| now returns a
\emph{sum-of-products} view over the data, we are using an eliminator,
|elim|, to apply a function to the fields of the constructor used to
create a value of type |a|. This eliminator then applies |map size| to
the fields of the constructor, returning something akin to a
|[Int]|. We then |sum| them up to obtain the final size.

  Codes consist of a type-level list of lists. The outer
list represents the constructors of a type, and will be interpreted as
a sum, whereas the inner lists are interpreted as the fields of the
respective constructors, interpreted as products.
The $\HS{'}$ sign in the code below marks the list
as operating at the type-level, as opposed to term-level lists which
exist at run-time. This is an example of Haskell's \emph{datatype}
promotion~\cite{Yorgey2012}.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: Star) :: P ([ (P [Star]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  The \emph{representation} is then defined by induction on
|CodeSOP| by the means of generalized $n$-ary sums, |NS|, and $n$-ary products,
|NP|. With a slight abuse of notation, one can view |NS| and |NP|
through the lens of the following type isomorphisms:

\vspace{-0.4cm}
{\small
\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)|
\end{align*}}
\vspace{-0.4cm}

  If we define |RepSOP| to be |NS (NP (K1 R))|, where |data K1 R a = K1 a| is borrowed from
\texttt{GHC.Generics}, we get exactly the representation that \texttt{GHC.Generics}
issues for |Bin a|. Nevertheless, note how we already need the parameter |f| to
pass |NP| to |NS| here.

\vspace{-0.4cm}
{\small
\begin{align*}
  |RepSOP (Bin a)|
  &\equiv | NS (NP (K1 R)) (CodeSOP (Bin a))| \\
  &\equiv |K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))| \\
  &\equiv |RepGen (Bin a)|
\end{align*}
}
\vspace{-0.4cm}

  It makes no sense to go through the trouble of adding the
explicit \emph{sums-of-products} structure to forget this information
in the representation. Instead of piggybacking on \emph{pattern
functors}, we define |NS| and |NP| from scratch using
\emph{GADTs}~\cite{Xi2003}.  By pattern matching on the values of |NS|
and |NP| we inform the type checker of the structure of |CodeSOP|.

\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f k      -> NS f (k Pcons ks)
  There  :: NS f ks  -> NS f (k Pcons ks)

data NP :: (k -> Star) -> [k] -> Star where
  NP0   ::                    NP f (P [])
  (:*)  :: f x -> NP f xs ->  NP f (x Pcons xs)
\end{code}
\end{myhs}

  Finally, since our atoms are of kind |Star|, we can use the identity
functor, |I|, to interpret those and define the final representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: Star) = I { unI :: a }
\end{code}
\end{myhs}

  To support the claim that one can define general combinators for
working with these representations, let us look at |elim| and |map|,
used to implement the |gsize| function in the beginning of the section.
The |elim| function just drops the constructor index and applies |f|,
whereas the |map| applies |f| to all elements of a product.

\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x

map :: (forall k dot f k -> a) -> NP f ks -> [a]
map f  NP0        = []
map f  (x :* xs)  = f x : map f xs
\end{code}
\end{myhs}

  Reflecting on the current definition of |size| and
comparing it to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one fewer typeclass, |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  There are still downsides to this approach. A notable
one is the need to carry constraints around: the actual |gsize|
written with the \texttt{generics-sop} library and no sugar
reads as follows.

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a , All2 Size (CodeSOP a)) => a -> Int
gsize  =  sum  .  hcollapse
       .  hcmap (Proxy :: Proxy Size) (mapIK size) .  fromSOP
\end{code}
\end{myhs}

  Where |hcollapse| and |hcmap| are analogous to the |elim| and |map|
combinators defined above. The |All2 Size (CodeSOP a)| constraint
tells the compiler that all of the types serving as atoms for |CodeSOP
a| are an instance of |Size|.  Here, |All2 Size (CodeSOP (Bin
a))| expands to |(Size a , Size (Bin a))|.  The |Size| constraint also
has to be passed around with a |Proxy| for the eliminator of the
$n$-ary sum. This is a direct consequence of a \emph{shallow}
encoding: since we only unfold one layer of recursion at a time, we
have to carry proofs that the recursive arguments can also be
translated to a generic representation. We can relieve this burden by
recording, explicitly, which fields of a constructor are recursive or
not, which is exactly how we start to shape \texttt{generics-mrsop}
in \Cref{chap:generic-programming}.

\subsection{Discussion}

  Most other generic programming libraries follow a similar pattern of
defining the \emph{description} of a datatype in the provided uniform
language by some type-level information, and two functions witnessing
an isomorphism. The most important feature of such library is how this
description is encoded and which are the primitive operations for
constructing such encodings. Some libraries,
mainly deriving from the \texttt{SYB}
approach~\cite{Lammel2003,Mitchell2007}, use the |Data| and |Typeable|
typeclasses instead of static type-level information to provide
generic functionality -- these are a completely different strand of
work from what we seek. The main approaches that rely on type-level
representations of datatypes are shown in
\Cref{fig:background:gplibraries}.
These can be compared in their
treatment of recursion and on their choice of type-level combinators
used to represent generic values.

\begin{figure}\centering
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
\caption{Spectrum of static generic programming libraries}
\label{fig:background:gplibraries}
\end{figure}

\paragraph{Recursion Style.}

  There are two ways to define the representation of values. Either
we place explicit information about which fields of the constructors of
the datatype in question are recursive or we do not.

If we do not mark recursion explicitly, \emph{shallow}
encodings are the easier option, where only one
layer of the value is turned into a generic form by a call to |from|.
This is the kind of representation we get from \texttt{GHC.Generics}.
The other side of the spectrum would be the \emph{deep}
representation, in which the entire value is turned
into the representation that the generic library provides in one go.

Marking the recursion explicitly, like in
\texttt{regular}~\cite{Noort2008}, allows one to choose between
\emph{shallow} and \emph{deep} encodings at will. These
representations are usually more involved as they need an extra
mechanism to represent recursion.  In the |Bin| example, the
description of the |Bin| constructor changes from ``this constructor
has two fields of the |Bin a| type'' to ``this constructor has two
fields in which you recurse''. Therefore, a \emph{deep} encoding
requires some explicit \emph{least fixpoint} combinator -- usually
called |Fix| in Haskell.

Depending on the use case, a shallow representation might be more
efficient if only part of the value needs to be inspected. On the
other hand, deep representations are sometimes easier to use, since
the conversion is performed in one go, and afterwards one only has to
work with the constructs from the generic library.

The fact that we mark explicitly when recursion takes place in a
datatype gives some additional insight into the description.
Some functions really need the information
about which fields of a constructor are recursive and which are not,
like the generic |map| and the generic |Zipper|.
This additional power has also been used to define regular
expressions over Haskell datatypes~\cite{Serrano2016}, for example.

\paragraph{Pattern Functors versus Codes.}

Most generic programming libraries build their type-level descriptions
out of three basic combinators: (1) \emph{constants}, which indicate a
type is atomic and should not be expanded further; (2) \emph{products}
(usually written as |:*:|) which are used to build tuples; and (3)
\emph{sums} (usually written as |:+:|) which encode the choice between
constructors. The |Rep (Bin a)| shown before is expressed in this
form. Note, however, that there is no restriction on \emph{how} these
can be combined. These combinators are usually referred to as
\emph{pattern functors} The \emph{pattern
functor}-based libraries are too permissive though, for instance, |K1
R Int :*: Maybe| is a perfectly valid \texttt{GHC.Generics}
\emph{pattern functor} but will break generic functions, i.e., |Maybe|
is not a combinator.

 In practice, one can always use a sum of products to represent a
datatype -- a sum to express the choice of constructor, and within
each constructor a product to declare which fields you have. The
\texttt{generic-sop} library~\cite{deVries2014} explicitly uses a list
of lists of types, the outer one representing the sum and each inner
one thought of as products.

\begin{myhs}
\begin{code}
CodeSOP (Bin a) = P [ P [a], P [Bin a, Bin a] ]
\end{code}
\end{myhs}

  The shape of this description follows more closely the shape of
Haskell datatypes, and make it easier to implement generic
functionality.

  Note how the \emph{codes} are different than the
\emph{representation}.  The latter being defined by induction on the
former.  This is quite a subtle point and it is common to see both
terms being used interchangeably.  Here, the \emph{representation} is
mapping the \emph{codes}, of kind |P [ P [ Star ] ]|, into |Star|. The
\emph{code} can be seen as the format that the \emph{representation}
must adhere to. Previously, in the pattern functor approach, the
\emph{representation} was not guaranteed to have a certain
structure. The expressivity of the language of \emph{codes} is
proportional to the expressivity of the combinators the library can
provide.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
