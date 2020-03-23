  Throughout this thesis we have presented two 
approaches to structural differencing. \Cref{chap:structural-patches}
gave us \texttt{stdiff} and served as a stepping stone --
it taught us valuable lessons on representation and computation
of patches -- which in turn, led to a more refined
framework in \Cref{chap:pattern-expression-patches}, \texttt{hdiff}.
On this section we would like to quantify how
\texttt{hdiff} improved over \texttt{hdiff}, and also
understand the relationship of between the
multitude of parameters that can be tweaked in \texttt{hdiff}: shall we
share constants? If so, how? Should we prioritize small
subtrees shared many times or bigger subtrees shared less often? etc.
Finally, we would like to better understand
the viability of structural differencing in source-code
version control, and that can only be done by running algorithms 
over real data.

  The evaluation of our algorithms is divided in two separate
experiments. First, we look at performance -- how fast
can patches be computed. Secondly, we look at
synchronization success rate -- how often can we solve conflicts that
\texttt{git merge} failed to resolve. The data for this experiments have been
taken from public \texttt{GitHub} repositories. Each datapoint
consists in four files representing a merge conflict: \texttt{O.lang}
is the common ancestor of a \texttt{git merge}, \texttt{A.lang} and
\texttt{B.lang} are the diverging replicas, which \texttt{git merge}
could not automatically reconcile, and \texttt{M.lang} being the file
that was produced by a human and commited as the resolved merge.

\victor{Update ??? below}

  We have extracted a total of ??? conflicts from \texttt{GitHub}. They
have been obtained from large public repositories in Java, JavaScript, Python,
Lua and Clojure. The choice of programming languages was motivated
by the parsers that were readily available in Hackage,
with the exception of Clojure, where we borrowed the parser from 
Garufi~\cite{Garufi2018}. More detailed information about data 
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
\victor{REMOVE BASH}

\begin{tabular}{@@{}llll@@{}} \toprule
Language & Repositories & Parseable Conflicts & Non-parseable Conflicts \\ \midrule
Clojure    & 31 & 1215 & 14  \\
Java       & 19 & 2903 & 849 \\
JavaScript & 28 & 3395 & 965 \\
Lua        & 27 & 750 & 91 \\ 
Python     & 27 & 4387 & 848 \\
Bash       & 10 & 37 & 3 \\ \midrule
\multicolumn{2}{r}{Totals:} & 12687 & 2770 \\
\bottomrule
\end{tabular}
\caption{Summary of collected data}
\label{tbl:eval:summary-data}
\end{table}

\section{The Experiments}

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

  In order to measure the performance we made a number of calls to the
differencing algorihm per datapoint. Namelly, \texttt{diff O A},
\texttt{diff O B}, \texttt{diff O M} and \texttt{diff A B}, which
produced four individual datapoints.  We limited the memory usage
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
a runtime proportional to the input size squared. That was expected
since we rely on a quadratic algorithm to annotate the trees and then
translate the annotated trees into |PatchST| over a single pass.
Out of the 8428 datapoints where we attempted to time \texttt{stdiff}
in order to produce \Cref{fig:eval:perf:stdiff}, 913 took longer than thirty seconds
and 929 used more than 8GB of memory.

  \Cref{fig:eval:perf:hdiff} illustrates the measured performance of
the differencing algorithm underlying \texttt{hdiff}, discussed in
\Cref{sec:pepatches:diff}, with different extraction techniques. The timed
function as |diff fa fb|, hence it also excludes parsing. Nevertheless,
the linear behavior is evident and in general, an order of magnitude better
than \texttt{stdiff}. We do see, however, that the \texttt{proper} context
extraction is slightly slower than \texttt{nonest} or \texttt{patience}.
Moreover, only 14 calls timed-out and none used more than 8GB of memory.

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

  The synchronization experiment consists in attempting to
run \texttt{merge A.lang O.lang B.lang}, and, upon successful
synchronization, comparing it against that which was
produced by a human \texttt{M.lang}. It is important to distinguish
three outomces: A \emph{success} indicates the merge was
succesful and was equal to that produced by a human;
aa \emph{merge-differs} indicates that the merge was
successful but produced a different result than the human;
and finally \emph{conflicting} means that the merge was
unsuccessful. The other outcomes can either be a timeout
or out-of-memory. The merge experiment was run with similar
resource bounds as the performance experiment: 45 seconds of
runtime and 8GB of virtual memory.

\victor{explain why did we distingish success from mergediff?}

\victor{This might be more complicated and I think I need Bayes rule}

\subsubsection{\texttt{stdiff}}

\begin{table}
\victor{properly format and display}

\centering
\begin{tabular}{@@{}lllll@@{}} \toprule
Language & Success & Merge Differs & Conflicts & Other \\ \midrule
Clojure    & 68 & 69 & 850 & 227 \\
Lua        & 75 & 26 & 486 & 163 \\ \midrule
\multicolumn{2}{r}{\emph{Total Success}} & 238 & & \\
\multicolumn{3}{r}{\emph{Success Rate}} & 15\% & \\ 
\bottomrule
\end{tabular}
\caption{Conflicts solved by \texttt{stdiff}.}
\label{tbl:eval:merge-stdiff}
\end{table}

  \Cref{tbl:eval:merge-stdiff} shows the results for \texttt{stdiff},
where we see that overall, 15\% of the conflicts could be solved and, 60\%
of the conflicts that were solved correspond to what a human would
have done. 

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


\section{Data Collection}
\label{sec:eval:collection}

  Collecting files from \texttt{GitHub} is not too difficult and can be done with 
moderate amounds of bash scripting. Our method is a variation of the
script used by Garufi~\cite{Garufi2018} and can is summarized as follows:

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
