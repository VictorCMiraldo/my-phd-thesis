  Throughout this thesis we have presented two
approaches to structural differencing. In \Cref{chap:structural-patches}
we saw \texttt{stdiff}, which served as a stepping stone
by providing important insights into the representation and computation
of patches. Next, we seen \texttt{hdiff}
in \Cref{chap:pattern-expression-patches}, which
intuitively improved upon the previous aproach with a
more efficient algorithm and a better overall merge algorithm.
On this section we would like to quantify how much
\texttt{hdiff} improved over \texttt{stdiff}, and also
understand the relationship of between the
multitude of parameters that can be tweaked in \texttt{hdiff}: shall we
share constants? If so, how? Should we prioritize small
subtrees shared many times or bigger subtrees shared less often? etc.
Finally, we would like to better understand
the viability of structural differencing in source-code
version control, and that can only be done by running algorithms
over real data.

  The evaluation of our algorithms is divided in two separate
experiments. First we look at performance of the |diff| function for
the different approaches. Then we look at synchronization success rate,
that is, how often can we solve conflicts that \texttt{git merge} failed to
resolve. The data for this experiments have been taken from public
\texttt{GitHub} repositories. Each datapoint consists in four files
representing a merge conflict that was resolved by a human:
\texttt{O.lang} is the common ancestor of a \texttt{git merge},
\texttt{A.lang} and \texttt{B.lang} are the diverging replicas, which
\texttt{git merge} could not automatically reconcile, and
\texttt{M.lang} is the file that was produced by a human and
commited as the resolved merge.

  We have extracted a total of 12687 usable datapoints from \texttt{GitHub}. They
have been obtained from large public repositories in Java, JavaScript, Python,
Lua and Clojure. The choice of programming languages was motivated
by the parsers that were readily available in Hackage,
with the exception of Clojure, where we borrowed a parser from
a MSc thesis~\cite{Garufi2018}. More detailed information about data
collection is given in \Cref{sec:eval:collection}; \Cref{tbl:eval:summary-data}
provides an overview of the gathered conflicts per programming language.

%   In \Cref{sec:eval:performance} we look at plots of the time it took
% to compute patches with each approach. This strenghtens our analytical
% intution about the temporal complexity of each algorithm and provides
% empirical evidence for the scalability of \texttt{hdiff} and lack
% there of from \texttt{stdiff}. \Cref{sec:eval:merging} looks at how many
% conflicts could be correctly solved by each algorith. A correct solution
% is when we can automatically produce a merge that equals to what a human has
% done to reconcile the conflict, modulo parsing.

  Unfortunately, the performance study for \texttt{stdiff} enjoys less datapoints than
\texttt{hdiff}. The reason being that \texttt{stdiff} requires
the \texttt{generics-mrsop} library, which triggers a memory leak
in GHC\footnote{\victor{get mem leak info}} when instantiated
for large abstract syntax trees. Consequently, we have only evaluated
\texttt{stdiff} over the Clojure and Lua conflicts.
Nevertheless, we reiterate that \texttt{stdiff} was abandoned
due to its poor performance, which can be clearly observed in its performance 
measurements, therefore, we ommit a detailed discussion of its
synchronization experiment.

\victor{Do we have ``research questions''? IF so, we should mention
them in the intro.}

\begin{table}
\centering
\begin{tabular}{@@{}llll@@{}} \toprule
Language & Repositories & Parseable Conflicts & Non-parseable Conflicts \\ \midrule
Clojure    & 31 & 1215 & 14  \\
Java       & 19 & 2903 & 849 \\
JavaScript & 28 & 3395 & 965 \\
Lua        & 27 & 750 & 91 \\
Python     & 27 & 4387 & 848 \\  \midrule
\multicolumn{2}{r}{Totals:} & 12650 & 2767 \\
\bottomrule
\end{tabular}
\caption{Summary of collected data}
\label{tbl:eval:summary-data}
\end{table}

  Next we look into two experiments aimed at studying the performance
and applicability of the different merge algorithms. Recall each
datapoint consists in four files for a specific language,
a span $A \leftarrow O \rightarrow B$, which could not be resolved
by \texttt{git merge} alone, and a file $M$ which was created
by a human to resolve the conflict.

\section{Performance}
\label{sec:eval:performance}

\begin{figure}
\centering
\subfloat[Runtimes from \texttt{stdiff} over 7000 datapoints.
Both axis are in a log-scale and the displayed lines are for reference]{%
\includegraphics[width=0.4\textwidth]{src/img/runtimes-stdiff.pdf}
\label{fig:eval:perf:stdiff}}
\quad
\subfloat[Runtimes from \texttt{hdiff} over 14000 datapoints.]{%
\includegraphics[width=0.4\textwidth]{src/img/runtimes-hdiff.pdf}
\label{fig:eval:perf:hdiff}}
\caption{Performance evaluation of \texttt{stdiff} and \texttt{hdiff}.}
\label{fig:eval:perf}
\end{figure}

  To measure the performance of the |diff| function in both approaches
we computed four patches per datapoint, namelly \texttt{diff O A},
\texttt{diff O B}, \texttt{diff O M} and \texttt{diff A B}.

  Whilst computing patches we limited the memory usage
to 8GB and overal time to 30s. If a call to |diff| used more than the
enabled temporal and spacial resources it was automatically
killed. We ran both \texttt{stdiff} and \texttt{hdiff} on the
same machine, yet, we stress that the absolute values are of little
interest.  The real take away from this experiment, plotted in \Cref{fig:eval:perf},
is the empirical validation of the complexity class of each algorithm.

  \Cref{fig:eval:perf:stdiff} illustrated the measured performance of
the differencing algorithm underlying \texttt{stdiff}, our first
structural differencing tool, discussed in
\Cref{sec:stdiff:oraclesenum}.  Let |fa,fb| be the files being
differenced, we have only timed the call to |diff fa fb| -- which
excludes parsing. Note that most of the time, \texttt{stdiff} exhibits
a runtime proportional to the square of the input size. That was expected
since it relies on a quadratic algorithm to annotate the trees and then
translate the annotated trees into |PatchST| over a single pass.
Out of the 8428 datapoints where we attempted to time \texttt{stdiff}
in order to produce \Cref{fig:eval:perf:stdiff}, 913 took longer than thirty seconds
and 929 used more than 8GB of memory. The rest have been plotted in
\Cref{fig:eval:perf:stdiff}.

  \Cref{fig:eval:perf:hdiff} illustrates the measured performance of
the differencing algorithm underlying \texttt{hdiff}, discussed in
\Cref{sec:pepatches:diff}. We have plotted each of the
context extraction techniques described in \ref{sec:pepatches:extract}.
The linear behavior is evident and in general, an order of magnitude better
than \texttt{stdiff}. We do see, however, that the \texttt{proper} context
extraction is slightly slower than \texttt{nonest} or \texttt{patience}.
Finally, only 14 calls timed-out and none used more than 8GB of memory.

  Measuring performance of pure Haskell code is always nuanced
and need some attention. We have used the |time| auxiliary function below, which is
based on the \texttt{timeit} package but adapted to fully force the
evaluation of the result of the action, with the |deepseq| method.

\begin{myhs}
\begin{code}
time :: (NFData a) => IO a -> IO (Double, a)
time act = do
    t1 <- getCPUTime
    result <- act
    let !res = result `deepseq` result
    t2 <- getCPUTime
    return (fromIntegral (t2-t1) * 1e-12 , res)
\end{code}
\end{myhs}

\section{Synchronization}
\label{sec:eval:merging}

  While the performance measurements provide evidence
for the practical applicability of our algorithms,
the merge experiment aims at estabilishing
a lower bound on the amount of conflicts that
could be solved in practice. On this section we discuss
the the results we observed when resolving conflicts
with \texttt{hdiff}.

  The synchronization experiment consists in attempting to
merge \texttt{A}, \texttt{O} and \texttt{B}. When
this merging succeeds, we compare the result against \texttt{M},
which was produced by a human. There are three expected outcomes:
\emph{success} indicates the merge was
succesful and was equal to that produced by a human;
\emph{mdif} indicates that the merge was
successful but produced a different result than what the human did;
and finally \emph{conf} means that the merge was
unsuccessful. Lastly, a faulty merging algorithm could
produce a patch that \emph{cannot} be applied to \texttt{O},
which is refered to as \emph{apply-fail}.
Naturally, timeout or out-of-memory exceptions can still occur
and fall under \emph{other}. The merge experiment was capped
at 45 seconds of runtime and 8GB of virtual memory.

  A 100\% success rate is unachievable.
Some conflicts really come from the same subtree being modified in
two distinct ways and require human intervention. One of the objectives
of this experiment is to understand whether or not there
is a place for structural merging within software development.
Another note is due on the distinction between \emph{success} and \emph{mdif}.
Being able to merge a conflict but obtaining a different result from
what was committed by a human does not necessarily imply that either result
is wrong. Developers can perform \emph{more or less} modifications merging
when committing \texttt{M}. For example, \Cref{fig:eval:mdif-suc-01} illustrates
a distilled example from our dataset which the human performed an extra
operation when merging, namelly adapting the \emph{sheet} field of one replica.
It can also be the case that the developer made a mistake
which was fixed in a later commit. Therefore, a result of \emph{mdif}
in a datapoint does not immediatly indicate the wrong behavior
of our merging algorithm. The success rate, however, provides us
with a believable lower bound to how many conflicts can be solved
automatically, in practice.

%%% No one cares about stdiff; moreover, I need to run it
%%% on the same dataset.
%%%
%%% \subsection{\texttt{stdiff}}
%%%
%%% \begin{table}
%%% \small
%%% \centering
%%% \begin{tabular}{@@{}lrlrlll@@{}} \toprule
%%% Language & \emph{success} & \% & \emph{merge-diff} & \% & \emph{conf} & Other \\ \midrule
%%% Clojure       & 68 & 0.07 & 69 & 0.07 & 850 & 227 \\
%%% Lua           & 75 & 0.13 & 26 & 0.04 & 486 & 163 \\ \midrule
%%% \emph{totals} & 143 & 0.09 & 95 & 0.06 & 1336 & \\ \bottomrule
%%% \end{tabular}
%%% \caption{Conflicts solved by \texttt{stdiff}.}
%%% \label{tbl:eval:merge-stdiff}
%%% \end{table}
%%%
%%%   \Cref{tbl:eval:merge-stdiff} shows the classify the results of
%%% attempting to solve each conflict in our dataset using \texttt{stdiff}'s merge function
%%% (\Cref{sec:stdiff:merging}). The \emph{Other} column shows the amound
%%% of conflicts that either timedout or raised an out-of-memory exception.
%%%
%%%   From \Cref{tbl:eval:merge-stdiff}, we observe that 15\% of the collected conflicts could be
%%% solved and, in 60\% of these cases, the automatic solution did correspond with
%%% what a human would have done.
%%%
%%% \victor{The results are slightly differnt than what Arian reported; thats because
%%% Arian's implementation had a bug and considered more merges than it should}
%%%
%%% \subsection{\texttt{hdiff}}

\begin{table}
\renewcommand{\arraystretch}{1.2}
\small
\centering
\begin{tabular}{@@{}lllllll@@{}} \toprule
Language & Mode &  Local/Global & \emph{success} & \emph{mdif} & \emph{conf} \\ \midrule
\multirow{3}{*}{Clojure}
  & |Patience| & local & ? & ? & ? \\
  & |Patience| & global & ? & ? & ? \\
  & |NoNested| & local & ? & ? & ? \\
\midrule
\multirow{3}{*}{Lua}
  & |Patience| & local & ? & ? & ? \\
  & |Patience| & global & ? & ? & ? \\
  & |NoNested| & local & ? & ? & ? \\
\midrule
\bottomrule
\end{tabular}
\caption{Conflicts solved by \texttt{hdiff} with different parameters.}
\label{tbl:eval:merge-hdiff}
\renewcommand{\arraystretch}{1.3}

\victor{Should we show the combination of parms or just the one with
the most success?}
\end{table}

  For the synchronization experiment we have run \texttt{hdiff}'s merge
function over our dataset with various parameters. All combinations of
extraction methods, local and global scope and minimum sharing height
of $1, 3$ and $9$ where executed. \victor{TODO: actually run it, again! lol}
\Cref{tbl:eval:merge-hdiff} shows the three runs of
\texttt{hdiff}'s merge function (\Cref{sec:pepatches:merging})
with most true successes with their respective combination of parameters.

  When \texttt{hdiff} returned a patch with conflicts,
that is, we could \emph{not} successfully solve the merge, we recorded
which conflicts we saw. \Cref{tbl:eval:hdiff-conflict-distr}
shows the distribution of each conflict type throughout the
dataset. Note that a patch resulting from a merge can have multiple
conflicts. This information is useful for deciding which aspects of
the merge algorithm can yield better rewards.  \victor{so what? Do I even want this
informantion?}

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
Percentile & 0.42 & 0.27 & 0.11 & 0.1 & 0.05 & 0.02 & 0.03 \\
\bottomrule
\end{tabular}
\caption{Distribution of conflicts observed by \texttt{hdiff}.}
\label{tbl:eval:hdiff-conflict-distr}
\end{table}

  The varying true success rates seen in \Cref{tbl:eval:merge-hdiff} are expected.
Different parameters used with \texttt{hdiff} yield different patches, which
might be easier or harder to merge. Out of the datapoints that resulted in \emph{mdif}
we have manually analyzed ??? randomly selected cases. We
witnessed that ??? of those \texttt{hdiff} behaved as we expect, and
the \emph{mdif} result was attributed to the human performing more operations
than a structural merge would have performed. \Cref{fig:eval:mdif-suc-01},
illustrates one example, distilled from the manually analyzed cases.
\victor{I've seen 13 so far, and 11 of them \texttt{hdiff} behaved
expectedly. The other two are discussed in \Cref{sec:eval:diff-extr-methods}}
\victor{Anyway... So what? What do we do with this info?}
\victor{Should I list the cases I looked into?}

\begin{figure}
\footnotesize \centering
\subfloat[Replica \texttt{A}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
dict={name='A', sheet='a'
     ,name='B', sheet='b'
     ,name='C', sheet='c'}
\end{verbatim}
\end{minipage}}
\qquad%
\subfloat[Replica \texttt{B}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
dict={name='A', sheet='path/a'
     ,name='B', sheet='path/b'
     ,name='X', sheet='path/x'
     ,name='C', sheet='path/c'}
\end{verbatim}
\end{minipage}}
\qquad%
\subfloat[Common ancestor, \texttt{O}]{%
\begin{minipage}[t]{\textwidth}
\begin{verbatim}
dict={name='A', sheet='path/a'
     ,name='B', sheet='path/b'
     ,name='C', sheet='path/c'}
\end{verbatim}
\end{minipage}}
\qquad%

\subfloat[Merge produced by a human]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
dict={name='A', sheet='a'
     ,name='B', sheet='b'
     ,name='X', sheet='x'
     ,name='C', sheet='c'}
\end{verbatim}
\end{minipage}}
\qquad\qquad\qquad%
\subfloat[Merge produced by \texttt{hdiff}]{%
\begin{minipage}{\textwidth}
\begin{verbatim}
dict={name='A', sheet='a'
     ,name='B', sheet='b'
     ,name='X', sheet='path/x'
     ,name='C', sheet='c'}
\end{verbatim}
\end{minipage}}
\caption{Example distiled from commit \texttt{60eba8} from \texttt{hawkthorne-server-lua}, from
GitHub. One replica inroduced entries in a dictionary where another
transformed a system path. The human merge transformed the system path in the newly
inserted entry, which is more than just merging changes. The \texttt{hdiff} tool did
produce a correct merge, but this got classified as \texttt{mdif}.}
\label{fig:eval:mdif-suc-01}
\end{figure}

  The cases where \emph{the same} datapoint yeilds a true success
and a \emph{mdif}, depending on which extraction method was used,
are interesting. Let us look at two complimentary examples (\Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02}) that were distilled from these contradicting
cases.

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
Merging with |Patience| does not witnes the problem since it will
not share \texttt{x} not the modifier list, since these occur
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
wrongly identifies that \emph{both} \texttt{n} and \texttt{o}.
Moreover, because \texttt{C.g()} is uniquely shared between
the definition of \texttt{m} and \texttt{S}, the patch identifies that
\texttt{void m...} became \texttt{String S...}. Finally, the merge
algorithm then transforms \texttt{void m} into \texttt{String S},
but then sees two deletions, which trigger the deletion of \texttt{n}
and \texttt{o} from the spine. The next instruction is the
insertion of \texttt{X}, resulting in the non-intuitive placement
of \texttt{X} in the merge produced with |Patience|.
When using |NoNested|, however, the empty bodies get all shared through
the code and prevend the detection of a deletion by the alignment
algorihm. It is worth noting that just because Java does not order
its declarations, this is not acceptable behavior since
it could produce uncompilable code in a language like Agda, where
the order of declarations matter.

  The examples in \Cref{fig:eval:nn-pt-01,fig:eval:nn-pt-02} illustrate
an inherent difficulty of using naive structured differencing over
structures with complex semantics, such as source-code. On the one hand
we have that sharing method modifiers triggers unwanted replication
of a change. On the other, the lack of sharing of empty method bodies makes
it difficult to place an insertion in its correct position.


\subsection{Threats to Validity}

  The synchronization experiment is encouraging. Before
drawing conclusions however, we must analyze our assumptions
and setting and pre-emptively undertand which factors
could also be influencing the numbers.

  We are differencing and comparing objects \emph{after} parsing.
This means that comments and formatting data was completely ignored. In fact,
preliminary evaluations showed that a vastly inferior success rate
results from incorporating and considering source-location tokens in
the abstract syntax tree. This is expected since the insertion of a
single empty line, for example, will change the hashes that identify
all subsequent elements of the abstract syntax and stop them from
being shared. The source-location tokens essentially make the
transformations that happen further down the file to be undetected
using \texttt{hdiff}. Although \texttt{stdiff} would not suffer from
this problem, it is already impratical by itself.

  Our decision of disconsidering formating, comments and source-location
is twofold. First, the majority of the available parsers does not include
said information. Secondly, if we had considered all that information in
our merging process, the final numbers would not inform us about how
many code transformations are \emph{disjoint} and could be automatically
merged.

\section{Data Collection}
\label{sec:eval:collection}

  Collecting files from \texttt{GitHub} is not too difficult and can be done with
moderate amounds of bash scripting. Our method is a variation of the
script used by Giovani Garufi~\cite{Garufi2018}, summarized below.

\begin{itemize}
  \item For each commit $c$ in a given repository such that $c$ has
two or more parents $p_0, \cdots, p_n$; checkout the repository at $c$
and attempt to \texttt{git merge}.

  \item For each file that git could not merge automatically --
obtainable through \texttt{git}'s \texttt{ls-files --unmerged} command
-- collect the common ancestor as \texttt{O.lang}, the diverging
versions as \texttt{A.lang} and \texttt{B.lang} and the merged file that
was commited in $c$ by a human, as \texttt{M.lang}.

  \item Each of these components is stored in a folder named
after the repository, commit and internal id of \texttt{O.lang}.
\end{itemize}

  The full script is not much more involved but out of
the scope of this thesis, we refer the reader to the full code
for more details \victor{WHERE IS THE CODE?}.
Overall, we acquired 12687 usable conflicts -- that is, we were able
to parse the four files parse with the parsers available to us -- and
2770 conflicts where at least one file yielded a parse error.


\section{Discussion}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
