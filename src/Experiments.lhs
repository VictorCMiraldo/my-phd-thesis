  Throughout this thesis we have presented two 
approaches to structural differencing. \Cref{chap:structural-patches}
gave us \texttt{stdiff} and served as a stepping stone --
it taught us valuable lessons on representation and computation
of patches -- which in turn, led to a more refined
framework in \Cref{chap:pattern-expression-patches}, \texttt{hdiff}.
On this section we would like to quantify how
\texttt{hdiff} improved over \texttt{hdiff}. 
Moreover, what is the relationship of between the
multitude of parameters that \texttt{hdiff} can tweak: shall we
share constants? If so, how? Should we prioritize small
subtrees shared many times or bigger subtrees shared less often? etc.

  The evaluation of our algorithms consists in running experiments
over the numerous conflicts extracted from \texttt{GitHub}. There are
two important factors we would like to compare: differencing
performance and synchronization success rate.

  Each extracted conflict from \texttt{GitHub} gives rise to
four files, named \texttt{O.lang}, \texttt{A.lang}, 
\texttt{B.lang} and \texttt{M.lang}. These represent the original file,
two diverging verions and the merged result produced by a human.

\victor{add them numbers over here!}
  We have extracted a total of ??? conflicts from \texttt{GitHub}. They
have been obtained from large public repositories in Java, JavaScript, Python,
Lua, Clojure and Bash. We have used parsers readily available in Hackage
to parse the source code with the exception of Clojure, where we
borrowed the parser from Garufi~\cite{Garufi2018}. More detailed
information about data collection is given in \Cref{sec:eval:collection}.

  In \Cref{sec:eval:performance} we look at plots of the time it took
to compute patches with each approach. This strenghtens our analytical
intution about the temporal complexity of each algorithm and provides
empirical evidence for the scalability of \texttt{hdiff} and lack
there of from \texttt{stdiff}. \Cref{sec:eval:merging} looks at how many
conflicts could be correctly solved by each algorith. A correct solution
is when we can automatically produce a merge that equals to what a human has 
done to reconcile the conflict, modulo parsing.

  Unfortunately, the study for \texttt{stdiff} enjoys less datapoints than
\texttt{hdiff}. The reason being that \texttt{stdiff} requires 
the \texttt{generics-mrsop} library, which can trigger a memory leak
on the compiler\footnote{\victor{get mem leak info}} when instantiated
for large abstract syntax trees. For this reason, we have only evaluated
\texttt{stdiff} on the Clojure, Lua and Bash subset of our dataset.


\victor{Do we have ``research questions''? IF so, we should mention
them in the intro.}
 

to gather real world data
\victor{Prototype research questions:

\begin{itemize}
  \item Can struct. differencing tools improve the
    quality of software synchronization?
  \item Can these tools scale?
\end{itemize}
}

\section{Performance}
\label{sec:eval:performance}

\begin{figure}
\centering
\subfloat[Runtimes from \texttt{stdiff --with-stats} over 7000 datapoints. 
Both axis are in a log-scale and the displayed lines are for reference]{%
\includegraphics[width=0.4\textwidth]{src/img/runtimes-stdiff.pdf}
\label{fig:eval:perf:stdiff}}
\quad
\subfloat[Runtimes from \texttt{hdiff --with-stats} over 14000 datapoints.]{%
\includegraphics[width=0.4\textwidth]{src/img/runtimes-hdiff.pdf}
\label{fig:eval:perf:hdiff}}
\caption{Performance evaluation of \texttt{stdiff} and \texttt{hdiff}.}
\label{fig:eval:perf}
\end{figure}
\end{figure}

  The measurements displayed in \Cref{fig:eval:perf} were obtained from computing
the differences between a number of files from our dataset, which come from real-world
examples extracted from github. We timed the relevant differencing functions with
the |time| auxiliary function, which is based on the \texttt{timeit} package but
adapted to fully force the evaluation of the result of the action, with the |deepseq| method.

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

  For each conflict in our dataset, we attempted to compute: |diff O A|,
|diff O B|, |diff O M| and |diff A B|, which produced four individual datapoints.
We also limited the memory usage to 8GB and overal time to 30s. If a call
to |diff| used more than the enabled temporal and spacial resources
it was automatically killed. Albeit we timed both \texttt{stdiff} and
\texttt{hdiff} on the same computer, the absolute values are of little interest.
The real take away from the graphs in \Cref{fig:eval:perf} is the empirical
validation of the complexity class of each algorithm.

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
than \texttt{stdiff}.

\section{Synchronization}
\label{sec:eval:merging}



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
the scope of this thesis. \victor{Do we refer the reader somewhere?}

\begin{table}
\centering
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

  \Cref{tbl:eval:summary-data} provides a summary of the collected data.
Overall, we acquired 12687 usable conflicts -- that is, we were able
to parse the four files parse with the parsers available to us -- and
2770 conflicts where at least one file yielded a parse error.


\section{Discussion}



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
