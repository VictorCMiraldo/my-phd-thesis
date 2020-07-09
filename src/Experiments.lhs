  Throughout this thesis we have presented two approaches to
structural differencing. In \Cref{chap:structural-patches} we saw
\texttt{stdiff}, which although unpractical, provided us with important
insights into the representation of patches. These
insights and experience led us to develop \texttt{hdiff}, in
\Cref{chap:pattern-expression-patches}, which improved upon the
previous approach with a more efficient |diff| function at
the expense of the simplicity of the merge algorithm: the
|merge| function from \texttt{hdiff} is much more involved
than that of \texttt{stdiff}.

  In this chapter we evaluate our algorithms on real-world
conflicts extracted from \texttt{GitHub} and analyze
the results. We are interested in performance measurements
and synchronization success rates, which are central
factors to the applicability of structural differencing
in the context of software version control.

  To conduct the aforementioned evaluation we have extracted a total
of \qTotalUsableConf{} usable datapoints from \texttt{GitHub}. They have been
obtained from large public repositories storing code written in Java,
JavaScript, Python, Lua and Clojure. The choice of programming languages
was motivated by the availability of parsers, with the exception
of Clojure, where we borrowed a parser from a MSc
thesis~\cite{Garuffi2018}. More detailed information about the data
collection is given in \Cref{sec:eval:collection}.

   The evaluation of \texttt{stdiff} has fewer
datapoints than \texttt{hdiff} for the sole reason that \texttt{stdiff}
requires the \texttt{generics-mrsop} library, which triggers a memory
leak in GHC\footnote{\url{https://gitlab.haskell.org/ghc/ghc/issues/17223} and
\url{https://gitlab.haskell.org/ghc/ghc/issues/14987}} when used with
larger abstract syntax trees. Consequently, we could only evaluate
\texttt{stdiff} over the Clojure and Lua subset of our dataset.

\section{Data Collection}
\label{sec:eval:collection}

  Collecting files from \texttt{GitHub} can
be done with the help of some bash scripting. The overall idea is to
extract the merge conflicts from a given repository by listing all
commits $c$ with more than two parents, recreating the repository at
the state immediately previous to $c$ and attempting to call
\texttt{git merge} at that state.

  Our script improves upon the script written
by Garuffi~\cite{Garuffi2018} by making sure to collect
the file that a human committed as the resolution of the conflict,
denoted \texttt{M.lang}. To collect conflicts from a repository, then,
all we have to do is run the following commands at its root.

\begin{itemize}
  \item List each commit $c$ with at least two parents with
\texttt{git rev-list --merges}.

  \item For each commit $c$ as above, let its parents be $p_0$ and $ps$;
checkout the repository at $p_0$ and attempt to \texttt{git merge
--no-commit ps}.  The \texttt{--no-commit} switch is important since
it gives us a chance to inspect the result of the merge.

  \item Next we parse the output of \texttt{git ls-files --unmerged},
which provides us with the three \emph{object-ids} for each file that
could not be automatically merged: one identifier for the common ancestor
and one identifier for each of the two diverging replicas.

  \item Then we use \texttt{git cat-file} to get the files corresponding
to each of the \emph{object-ids} gathered on the previous step. This yields
three files, \texttt{O.lang}, \texttt{A.lang} and \texttt{B.lang}.
Lastly, we use \texttt{git show} to save the file \texttt{M.lang} that
was committed by a human resolving the conflict.
\end{itemize}

  After running the steps above for a number of repositories, we end
up with a list of folders containing a merge conflict that was solved
manually. Each of these folders contain a span $A \leftarrow O
\rightarrow B$ and a file $M$ which is the human-produced result of
synchronizing $A$ and $B$.  We refer the reader to the full code for
more details (\Cref{chap:where-is-the-code}). Overall, we acquired
\qTotalUsableConf{} usable conflicts -- that is, we were able to parse
the four files with the parsers available to us -- and
\qTotalParseErrorConf{} conflicts where at least one file yielded a
parse error. \Cref{tbl:eval:summary-data} provides the distribution of
datapoints per programming language and displays the number of
conflicts that yielded a parse error. These parse errors are an
inevitable consequence of using off-the-shelf parsers on an existing dataset.
The parseable conflicts have been compiled into a publicly available
dataset~\cite{Miraldo2020_Dataset}.

\begin{table}
\centering
\begin{tabular}{@@{}llll@@{}} \toprule
Language & Repositories & Parseable Conflicts & Non-parseable Conflicts \\ \midrule
Clojure    & 31 & 1\,213 & 16  \\
Java       & 19 & 2\,901 & 851 \\
JavaScript & 28 & 3\,392 & 965 \\
Lua        & 27 & 748  & 91 \\
Python     & 27 & 4\,298 & 848 \\  \midrule
\emph{Totals} & 132 & \qTotalUsableConf & \qTotalParseErrorConf \\
\bottomrule
\end{tabular}
\caption{Distribution of datapoints within our dataset~\cite{Miraldo2020_Dataset}.
The repositories were chosen manually by searching each respective language in GitHub.
Our criteria for selecting repositories to mine was based on number of forks
and commits, in an attempt to maximize pull requests.}
\label{tbl:eval:summary-data}
\end{table}

\section{Performance}
\label{sec:eval:performance}

\begin{figure}
\centering
\subfloat[Runtimes from \texttt{stdiff} shown in
a log-log plot. The lines illustrate the behavior of \texttt{stdiff}
being between linear and quadratic]{%
\includegraphics[width=0.45\textwidth]{src/img/runtimes-stdiff.pdf}
\label{fig:eval:perf:stdiff}}
\quad
\subfloat[Runtimes from \texttt{hdiff} shown in a linear plot.]{%
\includegraphics[width=0.45\textwidth]{src/img/runtimes-hdiff.pdf}
\label{fig:eval:perf:hdiff}}
\caption{Performance measurements of \texttt{stdiff} and \texttt{hdiff}
differencing functions. The vertical axis represents seconds and the horizontal
axis has the sum of the number of constructors in the source and destination trees.}
\label{fig:eval:perf}
\end{figure}

  To measure the performance of the |diff| functions in both
approaches we computed four patches per datapoint, namely:
\texttt{diff O A},$\,$ \texttt{diff O B},$\,$ \texttt{diff O M}$\,$ and
\texttt{diff A B}.

  Whilst computing patches we limited the memory
usage to 8GB and runtime to 30s. If a call to |diff| used more than
the available temporal and spatial resources it was automatically
killed. We ran both \texttt{stdiff} and \texttt{hdiff} on the same
machine, yet, we stress that the absolute values are of little
interest.  The real take away from this experiment is the empirical
validation of the complexity class of each algorithm. The results
are shown in \Cref{fig:eval:perf} and plot the measured runtime against
the sum of the number of constructors in the source and destination trees.

  \Cref{fig:eval:perf:stdiff} illustrates the measured performance of
the differencing algorithm in \texttt{stdiff}, our first structural
differencing tool, discussed in \Cref{sec:stdiff:oraclesenum}.  For
|fa| and |fb| be the files being differenced, we have only timed the call to
|diff fa fb| -- which excludes parsing. Note that most of the time,
\texttt{stdiff} exhibits a runtime proportional to the square of the
input size. That was expected since it relies on a quadratic algorithm
to annotate the trees and then translate the annotated trees into
|PatchST| over a single pass.  Out of the 8428 datapoints where we
attempted to time \texttt{stdiff} in order to produce
\Cref{fig:eval:perf:stdiff}, 913 took longer than thirty seconds and
929 used more than 8GB of memory. The rest are plotted in
\Cref{fig:eval:perf:stdiff}. The high memory usage for particularly
large examples is unsurprising. Computing a \texttt{stdiff} patch 
requires us to maintain and manipulate a number of singleton types 
and constraints.

  \Cref{fig:eval:perf:hdiff} illustrates the measured performance of
the differencing algorithm underlying \texttt{hdiff}, discussed in
\Cref{sec:pepatches:diff}. We have plotted each of the
context extraction techniques described in \ref{sec:pepatches:extract}.
The linear behavior is evident and in general, an order of magnitude better
than \texttt{stdiff}. We do see, however, that the \texttt{proper} context
extraction is slightly slower than \texttt{nonest} or \texttt{patience}.
Finally, only 14 calls timed-out and none used more than 8GB of memory.

  Measuring performance of pure Haskell code is subtle due to its lazy
evaluation semantics. We have used the |time| auxiliary function
below.  We based ourselves on the \texttt{timeit} package, but adapted it
to fully force the evaluation of the result of the action, with the
|deepseq| method and force its execution with the bang pattern in
|res|, ensuring the thunk is fully evaluated.

\begin{myhs}
\begin{code}
time :: (NFData a) => IO a -> IO (Double, a)
time act = do  t1 <- getCPUTime
               result <- act
               let !res = result `deepseq` result
               t2 <- getCPUTime
               return (fromIntegral (t2-t1) * 1e-12 , res)
\end{code}
\end{myhs}

\section{Synchronization}
\label{sec:eval:merging}

  While the performance measurements provide some empirical evidence
that \texttt{hdiff} is indeed linear, the
synchronization experiment, discussed in this section, aims at
establishing a lower bound on the number of conflicts that could be
solved in practice.

  The synchronization experiment consists of attempting to
merge the $A \leftarrow O \rightarrow B$ span for every datapoint.
If \texttt{hdiff} produces a patch with no conflicts,
we apply it to $O$ and compare the result against $M$,
which was produced by a human. There are four possible outcomes,
three of which we expect to see and one that would indicate
a more substantial problem. The three outcomes we expect to see are:
\emph{success}, which indicates the merge was
successful and was equal to that produced by a human;
\emph{mdif} which indicates that the merge was
successful but different from the manual merge;
and finally \emph{conf} which means that the merge was
unsuccessful. The other possible outcome comes from
producing a patch that \emph{cannot} be applied to \texttt{O},
which is referred to as \emph{apply-fail}.
Naturally, timeout or out-of-memory exceptions can still occur
and fall under \emph{other}. The merge experiment was capped
at 45 seconds of runtime and 8GB of virtual memory.

  The distinction between \emph{success} and \emph{mdif} is important.
Being able to merge a conflict but obtaining a different result from
what was committed by a human does not necessarily imply that either result
is wrong. Developers can perform \emph{more or fewer} modifications when
committing \texttt{M}. For example, \Cref{fig:eval:mdif-suc-01} illustrates
an example distilled from our dataset which the human performed an extra
operation when merging, namely adapting the \emph{sheet} field of one replica.
It can also be the case that the developer made a mistake
which was fixed in a later commit. Therefore, a result of \emph{mdif}
in a datapoint does not immediately indicate the wrong behavior
of our merging algorithm. The success rate, however, provides us
with a reasonable lower bound on the number of conflicts that can be solved
automatically, in practice.

\begin{figure}
\small \centering
\subfloat[Replica \texttt{A}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
d={name='A', sheet='a'
  ,name='B', sheet='b'
  ,name='C', sheet='c'}
\end{verbatim}
\vspace{.01em}
\end{minipage}}
\quad%
\subfloat[Replica \texttt{B}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
d={name='A', sheet='path/a'
  ,name='B', sheet='path/b'
  ,name='X', sheet='path/x'
  ,name='C', sheet='path/c'}
\end{verbatim}
\end{minipage}}
\quad%
\subfloat[Common ancestor, \texttt{O}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
d={name='A', sheet='path/a'
  ,name='B', sheet='path/b'
  ,name='C', sheet='path/c'}
\end{verbatim}
\end{minipage}}
\qquad%

\subfloat[Merge produced by a human]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
d={name='A', sheet='a'
  ,name='B', sheet='b'
  ,name='X', sheet='x'
  ,name='C', sheet='c'}
\end{verbatim}
\end{minipage}}
\qquad\qquad\qquad%
\subfloat[Merge produced by \texttt{hdiff}]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
d={name='A', sheet='a'
  ,name='B', sheet='b'
  ,name='X', sheet='path/x'
  ,name='C', sheet='c'}
\end{verbatim}
\end{minipage}}
\caption{Example distilled from \texttt{hawkthorne-server-lua},
commit \texttt{60eba8}. One replica
introduced entries in a dictionary where another transformed a system
path. The \texttt{hdiff} tool did produce a correct merge given, but this got
classified as \texttt{mdif}.}
\label{fig:eval:mdif-suc-01}
\end{figure}

\begin{table}
\centering
\begin{tabular}{@@{}lrl@@{\qquad}rl@@{\qquad}lll@@{}} \toprule
Language & \emph{success} & (ratio) & \emph{mdif} & (ratio) & total ratio & \emph{conf} & \emph{t/o} \\
\midrule
 Clojure    & 184    & (0.15) & 211 & (0.17) & 0.32 & 818 & 0 \\
 Java       & 978    & (0.34) & 479 & (0.16) & 0.5  & 1\,443 & 1 \\
 JavaScript & 1\,046 & (0.30) & 274 & (0.08) & 0.38 & 2\,062 & 10 \\
 Lua        & 185    & (0.25) & 101 & (0.14) & 0.39 & 462 & 0 \\
 Python     & 907    & (0.21) & 561 & (0.13) & 0.34 & 2\,829 & 1 \\
\midrule
\emph{Total}& \qSolvedConf{} & (0.26) & 1626 & (0.13) & 0.39 & 7\,614 & 12 \\
\bottomrule
\end{tabular}
\caption{Best synchronization success rate per language. No \emph{apply-fail}
was encountered in the entire dataset and the number of timeouts was negligible.}
\label{tbl:eval:merge-hdiff-aggr}
\end{table}

\begin{table}
\centering
\begin{tabular}{@@{}llcrl@@{\quad}rl@@{\quad}ll@@{}} \toprule
Language & Mode & Height & \emph{success} & (ratio) & \emph{mdif} & (ratio) & \emph{conf} & \emph{t/o} \\ \midrule
\multirow{3}{*}{Clojure} % sums: 1213
  & |Patience|     & 1 & 184    & (0.15) & 211 & (0.17) & 818    & 0 \\
  & |NoNested|     & 3 & 149    & (0.12) & 190 & (0.16) & 874    & 0 \\
  & |ProperShare|  & 9 & 92     & (0.08) & 84  & (0.07) & 1\,037 & 0 \\
\midrule
\multirow{3}{*}{Java} % sums: 2901
  & |Patience|     & 1 & 978    & (0.34) & 479 & (0.16) & 1\,443 & 1 \\
  & |NoNested|     & 3 & 924    & (0.32) & 509 & (0.18) & 1\,467 & 1 \\
  & |ProperShare|  & 9 & 548    & (0.19) & 197 & (0.07) & 2\,155 & 1 \\
\midrule
\multirow{3}{*}{JavaScript} % sums: 3392
  & |Patience|     & 1 & 1\,046 & (0.30) & 274 & (0.08) & 2\,062 & 10 \\
  & |NoNested|     & 3 & 991    & (0.29) & 273 & (0.08) & 2\,124 & 4  \\
  & |ProperShare|  & 9 & 748    & (0.22) & 116 & (0.03) & 2\,508 & 20 \\
\midrule
\multirow{3}{*}{Lua} % sums: 748
  & |Patience|     & 3 & 185    & (0.25) & 101 & (0.14) & 462 & 0 \\
  & |NoNested|     & 3 & 171    & (0.23) & 110 & (0.15) & 467 & 0 \\
  & |ProperShare|  & 9 & 86     & (0.11) & 29  & (0.04) & 633 & 0 \\
\midrule
\multirow{3}{*}{Python} % sums 4298
  & |Patience|     & 1 & 907    & (0.21) & 561 & (0.13) & 2\,829 & 1 \\
  & |NoNested|     & 3 & 830    & (0.19) & 602 & (0.14) & 2\,865 & 1 \\
  & |ProperShare|  & 9 & 446    & (0.10) & 223 & (0.05) & 3\,627 & 2 \\
\bottomrule
\end{tabular}
\caption{Best results for each extraction mode. The \emph{height} column
indicates the minimum height a subtree must have to qualify for sharing,
configured with the \texttt{--min-height} option. All of the above results
were obtained with \emph{locally-scoped} patches, \emph{globally-scoped}
success rates were consistently lower than their \emph{locally-scoped} counterpart.}
\label{tbl:eval:merge-hdiff}
\end{table}


  Given the multitude of dials we can adjust in \texttt{hdiff}, we
have run the experiment with each combination of extraction method
(|Patience, NoNested, ProperShare|), local or global metavariable
scoping and minimum sharing height of $1, 3$ and $9$.
\Cref{tbl:eval:merge-hdiff} shows the combination of parameters that
yielded more successes per extraction method. The column for
scoping is omitted because local scope outperformed global scoping in
all instances. \Cref{tbl:eval:merge-hdiff-aggr} shows only the highest
success rate per language.

  The varying true success rates seen in \Cref{tbl:eval:merge-hdiff}
are to be expected.  Different parameters used with \texttt{hdiff}
yield different patches, which might be easier or harder to merge. Out
of the datapoints that resulted in \emph{mdif} we have manually
analyzed \qManualMDiffAnal{} randomly selected cases. We witnessed
that in \qManualMDiffOk{} of those \texttt{hdiff} behaved as we expect,
and the \emph{mdif} result was attributed to the human performing more
operations than a structural merge would have performed, as
exemplified in \Cref{fig:eval:mdif-suc-01}, which was distilled from
the manually analyzed cases. We will shortly discuss two cases,
illustrated in \Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02}, where
\texttt{hdiff} behaved unexpectedly.

  It is worth noting that even though 100\% success
rate is unachievable -- some conflicts really come from a subtree being
modified in two distinct ways and inevitably require human
intervention -- the results we have seen are very encouraging.
In \Cref{tbl:eval:merge-hdiff-aggr} we see that \texttt{hdiff} produces
a merge in at least 39\% of datapoints and most often
matches the handmade merge.

  The cases where \emph{the same} datapoint yields a true success and
a \emph{mdif}, depending on which extraction method was used, are
interesting. Let us look at two complementary examples
(\Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02}) that were distilled from
these contradicting cases.

\begin{figure}
\centering
\scriptsize
\subfloat[\texttt{A.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  public int f(int x)
    { F(x*y); }
  public int g(int x)
    { G(x+2); }}
\end{verbatim}
\end{minipage}}\qquad%
\subfloat[\texttt{O.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  public int f(int x)
    { F(x); }
  public int g(int x)
    { G(x+1); }}
\end{verbatim}
\end{minipage}}\qquad%
\subfloat[\texttt{B.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  public int f(int x)
    { F(x); }
  public static int g(int x)
    { G(x+1); }}
\end{verbatim}
\end{minipage}}

\subfloat[Expected merge, computed with |Patience|]{%
\qquad\quad
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  public int f(int x)
    { F(x*y); }
  public static int g(int x)
    { G(x+2); }}
\end{verbatim}
\end{minipage}\qquad\quad}\quad%
\subfloat[Incorrect merge, computed with |NoNest|]{%
\qquad
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  public static int f(int x)
    { F(x*y); }
  public static int g(int x)
    { G(x+2); }}
\end{verbatim}
\end{minipage}\qquad}

\subfloat[Simplified illustration of patch computed with
\texttt{hdiff -d nonest \{O,A\}.java}; The sharing of |metavar p|
reflects the sharing of the list of method modifiers.]%
{%
\begin{myforest}
[\texttt{class Class}
  [|(:)| , alignmentSmall , s sep=3mm
    [\texttt{Method f} , s sep=3mm
      [,change [p,metavar] [p,metavar]]
      [,change [i,metavar] [i,metavar]]
      [|dots|
        [,change [x,metavar] [\texttt{*} [x,metavar] [\texttt{y}]]]]
    ]
    [|(:)|
      [\texttt{Method g} , s sep=3mm
        [,change [p,metavar] [p,metavar]]
        [,change [i,metavar] [i,metavar]]
        [|dots| [,change [|1|] [|2|]]]
      ]
      [|[]|]
    ]
  ]
]
\end{myforest}}

\subfloat[Simplified illustration of patch computed with
\texttt{hdiff -d nonest \{O,B\}.java}, note how each copy happens inside
its own scope]%
{%
\begin{myforest}
[\texttt{class Class}
  [|(:)| , s sep=5mm
    [|Cpy (metavar f)| , alignmentSmall]
    [|(:)|
      [\texttt{Method g} , s sep=10mm
        [,change [|(:)| [p,metavar] [|[]|]]
                 [|(:)| [p,metavar] [|(:)| [\texttt{static}] [|[]|]]]]
        [|Cpy (metavar typ)| , alignmentSmall]
        [|Cpy (metavar bdy)| , alignmentSmall]
      ]
      [|[]|]
    ]
  ]
]
\end{myforest}}
\caption{Example distilled from \texttt{cas}, commit \texttt{035eae3},
where |Patience| merges with a true success but |NoNest| merges
with \emph{mdif}, and, in fact, replicates the \texttt{static}
modifier incorrectly.}
\label{fig:eval:nn-pt-01}
\end{figure}


  \Cref{fig:eval:nn-pt-01} shows an example where merging patches
extracted with |Patience| returns the correct result, but
merging patches extracted with |NoNest| does not. Because
replica \texttt{A} modified the definition of \texttt{f},
the entire declaration of \texttt{f} cannot be copied, and
it is placed inside the same scope (alignment) as the definition
of \texttt{g} since they share a name, \texttt{x}. They also share,
however, the list of method modifiers, which in this case is \texttt{public}.
When \texttt{B} modifies the list of modifiers of method \texttt{g}
by appending \texttt{static}, the merge algorithm replicates this
change to the list of modifiers of \texttt{f}, since the patch
wrongly believes both lists represent \emph{the same list}.
Merging with |Patience| does not witness the problem since it will
not share \texttt{x} not the modifier list, as these occur
more than once in the deletion and insertion context of both
\texttt{hdiff O A} and \texttt{hdiff O B}.

\begin{figure}
\centering
\scriptsize
\subfloat[\texttt{A.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  String S = C.g();
  void m ()
    { return; }
  void o (int l);
  void p ();
}
\end{verbatim}
\end{minipage}}\qquad%
\subfloat[\texttt{O.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  void m ()
    { C.q.g(); return;	}
  void n ();
  void o ();
  void p ();
}
\end{verbatim}
\end{minipage}}\qquad%
\subfloat[\texttt{B.java}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  void m ()
    { C.q.g(); return;	}
  void n ();
  void o ();
  void X ();
  void p ();
}
\end{verbatim}
\end{minipage}}

\subfloat[Expected merge, computed with |NoNested|]{%
\qquad\quad
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  String S = C.g();
  void m ()
    { return; }
  void o (int l);
  void X ();
  void p ();
}
\end{verbatim}
\end{minipage}\qquad\quad}\quad%
\subfloat[Incorrect merge, computed with |Patience|]{%
\qquad
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
class Class {
  String S = C.g();
  void X ();
  void m ()
    { return; }
  void o (int l);
  void p ();
}
\end{verbatim}
\end{minipage}\qquad}
\caption{Example distilled from \texttt{spring-boot}, commit \texttt{0074e9},
where |NoNested| merges with a true success but |Patience| merges
with \emph{mdif} since it inserts the declaration of \texttt{X} in
the wrong place.}
\label{fig:eval:nn-pt-02}
\end{figure}

  \Cref{fig:eval:nn-pt-02}, on the other hand, shows an example where
merging patches extracted with |NoNested| succeeds, but |Patience|
inserts a declaration in an unexpected location. Upon further
inspection, however, the reason for the diverging behavior becomes
clear.  When differencing \texttt{A} and \texttt{O} under |Patience|
context extraction, the empty bodies (which are represented in the
Java AST by |MethodBody Nothing|) of the declarations of \texttt{n}
and \texttt{o} are not shared. Hence, the alignment mechanism
wrongly identifies that \emph{both} \texttt{n} and \texttt{o} were deleted.
Moreover, because \texttt{C.g()} is uniquely shared between
the definition of \texttt{m} and \texttt{S}, the patch identifies that
\texttt{void m...} became \texttt{String S...}. Finally, the merge
algorithm then transforms \texttt{void m} into \texttt{String S},
but then sees two deletions, which trigger the deletion of \texttt{n}
and \texttt{o} from the spine. The next instruction is the
insertion of \texttt{X}, resulting in the non-intuitive placement
of \texttt{X} in the merge produced with |Patience|.
When using |NoNested|, however, the empty bodies get all shared through
the code and prevent the detection of a deletion by the alignment
algorithm. It is worth noting that just because Java does not care
about the order of declarations, this is not acceptable behavior since
it could produce invalid source files in a language like Agda, where
the order of declarations matters, for example.

  The examples in \Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02} illustrate
an inherent difficulty of using naive structured differencing over
structures with complex semantics, such as source-code. On the one hand
sharing method modifiers triggers undesired replication
of a change. On the other, the lack of sharing of empty method bodies makes
it difficult to place an insertion in its correct position.

  When \texttt{hdiff} returned a patch with conflicts,
that is, we could \emph{not} successfully solve the merge, we recorded
the class of conflicts we observed. \Cref{tbl:eval:hdiff-conflict-distr}
shows the distribution of each conflict type throughout the
dataset. Note that a patch resulting from a merge can have multiple
conflicts. This information is useful for deciding which aspects of
the merge algorithm can yield better results.

\begin{table}
\centering
\begin{tabular}{@@{}lllllllll@@{}}
 & \rotatebox{50}{\small \texttt{not-eq}}  &
   \rotatebox{50}{\small \texttt{inst-mod}} &
   \rotatebox{50}{\small \texttt{del-spn}} &
   \rotatebox{50}{\small \texttt{ins-ins}} &
   \rotatebox{50}{\small \texttt{inst-ins}} &
   \rotatebox{50}{\small \texttt{inst-del}} &
   Others \\ \midrule
Amount & 7904 & 5052 & 2144 & 1892 & 868 & 357 & 506 \\
Ratio  & 0.42 & 0.27 & 0.11 & 0.1 & 0.05 & 0.02 & 0.03 \\
\bottomrule
\end{tabular}
\caption{Distribution of conflicts observed by running \texttt{hdiff}
over our dataset~\cite{Miraldo2020_Dataset}.  The first row displays
the number of times that |throwConf| was called with which label.}
\label{tbl:eval:hdiff-conflict-distr}
\end{table}


\subsection{Threats to Validity}

  The synchronization experiment is encouraging, but before
drawing conclusions however, we must analyze our assumptions
and setting and preemptively understand which factors
could also be influencing the numbers.

  We are differencing and comparing objects \emph{after} parsing.
This means that comments and formatting data were completely ignored. In fact,
preliminary evaluations showed that a vastly inferior success rate
results from incorporating and considering source-location tokens in
the abstract syntax tree. This is expected since the insertion of a
single empty line, for example, will change the hashes that identify
all subsequent elements of the abstract syntax and stop them from
being shared. The source-location tokens essentially prevent the
transformations that happen further down the file to be detected
by \texttt{hdiff}. Although \texttt{stdiff} would not suffer from
this problem, it is already impractical by itself.

  Our decision to ignore formatting, comments and
source-location tokens is twofold. First, the majority of the
available parsers does not include said information. Secondly, if we
had considered all that information in our merging process, the final
numbers would not inform us about how many code transformations are
\emph{disjoint} and could be automatically merged.

  Another case worth noting is that although we have not found many cases
where \texttt{hdiff} performed a wrong merge, \Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02}
shows two such cases, hence, it is important to take the aggregate success
rate with a grain of salt. There exists a probability that some of the
\emph{mdif} cases are false positives, that is, \texttt{hdiff} produced a merge
but it performed the wrong operation.

  Finally, one can also argue we have not considered conflicts that
arise from rebasing, as these are not observed in the git history.
This does not necessarily make a threat to validity, but indeed would have
given us more data. That being said, we would only be able to recreate rebases
done through the \texttt{GitHub} web interface. The rebases done on the command line are
impossible to recreate.

\section{Discussion}

  This chapter provided an empirical evaluation of our methods and
techniques. We observed how \texttt{stdiff} is at least one order of
magnitude slower than \texttt{hdiff}, confirming our suspicion of it being
unusable in practice.  Preliminary synchronization experiments done with
\texttt{stdiff} over the same data revealed a comparatively small success
rate. Around 15\% of the conflicts could be solved, out of which 60\%
did match what a human did.

  The measurements for \texttt{hdiff}, on the other hand, gave
impressive results. Even with all the overhead introduced by generic
programming and an unoptimized algorithm, we can still compute patches
almost instantaneously. Moreover, it confirms our intuition that the
differencing algorithm underlying \texttt{hdiff} is in fact linear.
Moreover, the synchronization results for \texttt{hdiff} are
encouraging. We have observed that 39\% of the conflicts in our
dataset could be solved by \texttt{hdiff} and 66\% of these solutions
did match what a human performed.

  An interesting observation that comes from the
synchronization experiment, \Cref{tbl:eval:merge-hdiff}, is that the
best merging success rate for all languages used the |Patience|
context extraction -- only copying subtrees that occur uniquely.  This
suggests that it might be worthwhile to forbid duplication and
contractions on the representation level and work on a merging
algorithm that enjoys the precondition that each metavariable occurs
only twice. This simplification could enable us to write a simpler
merging algorithm and an Agda model, which can then be used to prove
important properties about our algorithms.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
