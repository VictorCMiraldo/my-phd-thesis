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
the merge algorithm can yield better rewards.  \victor{so what? ...}

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

  Varying true success rates are expected. Different
parameters used with \texttt{hdiff} yield vastly different patches.


  The cases where \texttt{hdiff} did produce a merge patch
with \emph{no} conflicts, but it was different from what a human
produced, are interesting.

 we have manually analyzed ??? randomly selected \emph{mdif} cases and
seen that ??? of those \texttt{hdiff} behaved expectedtly.
These, in fact, corresponds to cases analogous to \Cref{fig:eval:mdif-suc-01},
where the human performed additional operations, or ignored certain
changes from one replica.
\victor{I've seen 13 so far, and 11 of them \texttt{hdiff} behaved
expectedly. The other two are discussed in \Cref{sec:eval:diff-extr-methods}}
\victor{Anyway... So what? What do we do with this info?}


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


\subsubsection{Notes on Different Extraction Methods}
\label{sec:eval:diff-extr-methods}

  Manual inspection of randomly selected cases where we have
observed a \emph{mdif} result -- where \texttt{hdiff} produced a different result from
the human -- concluded \texttt{hdiff} behaved expectedly and the human
performed additional operations. But we also observed that certain
datatpoints resulted in \emph{mdif} if merged with extraction mode |NoNested|
but \emph{success} when merged with |Patience|. Those were particularly interesting
and deserve special attention.

  
  

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

  The full process is not much more involved but out of
the scope of this thesis. \victor{Do we refer the reader somewhere? I wouldn't mind
pasting the entire shell script somewhere}
Overall, we acquired 12687 usable conflicts -- that is, we were able
to parse the four files parse with the parsers available to us -- and
2770 conflicts where at least one file yielded a parse error.


\section{Discussion}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
