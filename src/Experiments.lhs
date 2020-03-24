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
experiments. First, we look at performance -- how fast can patches be
computed. Secondly, we look at synchronization success rate -- how
often can we solve conflicts that \texttt{git merge} failed to
resolve. The data for this experiments have been taken from public
\texttt{GitHub} repositories. Each datapoint consists in four files
representing a merge conflict that was resolved by a human:
\texttt{O.lang} is the common ancestor of a \texttt{git merge},
\texttt{A.lang} and \texttt{B.lang} are the diverging replicas, which
\texttt{git merge} could not automatically reconcile, and
\texttt{M.lang} being the file that was produced by a human and
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

  Unfortunately, the study for \texttt{stdiff} enjoys less datapoints than
\texttt{hdiff}. The reason being that \texttt{stdiff} requires 
the \texttt{generics-mrsop} library, which triggers a memory leak
in GHC\footnote{\victor{get mem leak info}} when instantiated
for large abstract syntax trees. For this reason, we have only evaluated
\texttt{stdiff} over the Clojure and Lua conflicts.


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

\section{The Experiments}

  Next we look into two experiments aimed at studying the performance
and applicability of the different merge algorithms. Recall each
datapoint consists in four files for a specific language,
a span $A \leftarrow O \rightarrow B$, which could not be resolved
by \texttt{git merge} alone, and a file $M$ which was created
by a human to resolve the conflict.

\subsection{Performance}
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

\subsection{Synchronization}
\label{sec:eval:merging}

  While the performance tests provide evidence
for the practical applicability of our algorithms, 
the merge experiment aims at estabilishing
a lower bound on the amount of conflicts that 
could be solved in practice.

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

  The distinction between \emph{success} and \emph{mdif} is important
but needs to be taken with a grain of salt. It can be that
a developer performed \emph{more} modifications than just merging
when committing \texttt{M}. Or, it can be that \texttt{M} contains a mistake
which was fixed in a later commit. Therefore, a result of \emph{mdif}
in a datapoint does not immediatly indicate the wrong behavior
of our merging algorithm. The success rate, however, provides us
with a believable lower bound to how many conflicts can be solved
automatically, in practice.

\victor{explain why did we distingish success from mergediff?}

\victor{This might be more complicated and I think I need Bayes rule}

\subsubsection{\texttt{stdiff}}

\begin{table}
\small
\centering
\begin{tabular}{@@{}lllllll@@{}} \toprule
Language & \emph{success} (s) & \emph{mdif} (md) & \emph{conf} (c) 
  & $\frac{s}{s + \mathit{md} + c}$ 
  & $\frac{s + \mathit{md}}{s + \mathit{md} + c}$ 
  & Other \\ \midrule
Clojure       & 68 & 69 & 850 & 0.07 & 0.14 & 227 \\
Lua           & 75 & 26 & 486 & 0.12 & 0.17 & 163 \\ \midrule
\emph{totals} & 143 & 95 & 1336 & 0.9 & 0.15 & \\ \bottomrule
\end{tabular}
\caption{Conflicts solved by \texttt{stdiff}.}
\label{tbl:eval:merge-stdiff}
\end{table}

  \Cref{tbl:eval:merge-stdiff} shows the results for \texttt{stdiff},
where we observed that 15\% of the collected conflicts could be solved and, 
in 60\% of these cases the automatic solution did correspond with
what a human would have done. 

\subsubsection{\texttt{hdiff}}

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
Distribution & 0.42 & 0.27 & 0.11 & 0.1 & 0.05 & 0.02 & 0.03 \\
\bottomrule
\end{tabular}
\caption{Distribution of conflicts observed by \texttt{hdiff}.}
\label{tbl:eval:hdiff-conflict-distr}
\end{table}

\Cref{tbl:eval:hdiff-conflict-distr} shows the distribution of each conflict type
throughout the dataset. Note that a patch resulting from a merge can have
multiple conflicts. This information is useful for deciding which aspects
of the merge algorithm can yield better rewards. 

\subsection{Threats to Validity}

  The main threat to the validity of our experiments comes from
differencing and comparing objects \emph{after} parsing. This means
that comments and formatting data was completely ignored. In fact,
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
