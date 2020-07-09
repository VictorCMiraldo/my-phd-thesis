  The \unixdiff{} tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used in
software version control. The fixed \emph{lines-of-code} granularity,
however, is sometimes too coarse and obscures simple changes, \ie{}, renaming
a single parameter triggers the whole line to be seen as \emph{changed}. This may
lead to unnecessary conflicts when unrelated changes occur on the same line.
Consequently, it is difficult to merge such changes automatically.

  Tradidional methods for computing differences 
\cite{Bille2005,Bergroth2000,Paassen2018,McIlroy1976,Myers1986,Hirschberg1975}
mostly rely on the computation of an \emph{edit-script} that transforms
the source into the destination. An edit-script consists in
a list of edit-operations, which in turn, usually consist in insertions, deletions
and copies. Take the two files below as an example:

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
\unixdiff{} would show deletions prefixed with a minus sign
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

  Although there exists many generalizations of \emph{edit-scripts} to work over trees
\cite{Zhang1989,Demaine2007,Dulucq2003,Pawlik2012,Augsten2008,Augsten2010},
these approaches suffer from significant drawbacks. For one, edit-scripts
do not have the expressivity to encode arbitrary permutations, duplications
or contractions (inverse of a duplication). Secondly, there is a big performance
cost to be paid for computing edit-scripts for trees.
Finally, most of the previous work on the topic considers only \emph{untyped} trees.
That is, the transformations are not guaranteed to respect some \emph{schema}.
It is possible to design edit-scripts in a typed fashion \cite{Lempsink2009} but
this does not solve the issues we just mentioned.

  In this thesis we discuss two novel approaches to structural
differencing that aim at detaching from edit-script. 
The first approach defines a type-indexed representation of
patches and provides a clear merging algorithm, but it is
computationally expensive to produce patches with this approach.
The second approach addresses the efficiency problem by choosing an
extensional representation for patches. This enables us to represent
transformations involving insertions, deletions, duplication,
contractions and permutations which are computable in linear time.

  Suppose we want to describe a change that modifies the left element
of a binary tree. If we had the full Haskell programming language
available as the patch language, we could write something similar to
function |c|, in \Cref{fig:sammenvatting:example-01:A}. Observing the
function |c| we see it has a clear domain -- a set of |Tree|s that
when applied to |c| yields a |Just| -- which is specified by the
pattern and guards. Then, for each tree in the domain we compute a
corresponding tree in the codomain.  The new tree is obtained from the
old tree by replacing the |10| by |42| in-place.  Closely inspecting
this definition, we can interpret the matching of the
pattern as a \emph{deletion} phase and the construction of the
resulting tree as a \emph{insertion} phase.  The \texttt{hdiff}
approach represents the change in |c| exactly as that: a pattern and a
expression. Essentially, we write |c| as |Chg (Bin (Leaf 10) y) (Bin
(Leaf 42) y)| -- represented graphically as in
\Cref{fig:sammenvatting:example-01:B}.


\begin{figure}
\centering
\subfloat[Haskell function |c|]{%
\begin{myhsFig}[0.4\textwidth]
\begin{code}
c :: Tree -> Maybe Tree
c (Bin (Leaf x) y)
  | x == 10    = Just (Bin (Leaf 42) y)
  | otherwise  = Nothing
c _            = Nothing
\end{code}
\end{myhsFig}\label{fig:sammenvatting:example-01:A}}\qquad\qquad
\subfloat[|c| represented as a \emph{change}]{%
\begin{myforest}
[,change
[|Bin|
  [|Leaf| [|10|]]
  [y,metavar]]
[|Bin|
  [|Leaf| [|42|]]
  [y,metavar]]
]
\end{myforest}\label{fig:sammenvatting:example-01:B}}
\caption{Haskell function and its graphical representation as a change.
The change here modifies the left child of a binary node. Notation |metavar y| is used to indicate |y| is
a metavariable.}
\label{fig:sammenvatting:example-01}
\end{figure}

  With the added expressivity, however, comes added
complexity. Consequently, the merging algorithm is more intricate and
the patches can be harder to reason about.

  Both of our approaches can be instantiated to mutually recursive
datatypes and, consequently, can be used to compare
elements of most programming languages.  Writing the software that
does so, however, comes with additional challenges.  To address this we
have developed two new libraries for generic programming in Haskell.

  Finally, we empirically evaluate our algorithms by a number of
experiments over real conflicts gathered from \texttt{GitHub}. Our
evaluation reveals that at least \qSolvedPerc{} of the conflicts
that developers face on a day-to-day basis could have been
automatically merged. This suggests there is a benefit in using
structural differencing tools as the basis for software version
control.
