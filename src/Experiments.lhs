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

  The evaluation of our algorithms consists in
packaging them into executable and running our merge
algorithms with different parameters over the numerous 
conflicts extracted from \texttt{GitHub}. There are two
important factors we would like to compare: performance
and synchronization success rate. 

  In \Cref{sec:eval:performance} we look at plots of the time it took
to compute patches with each approach. This strenghtens our analytical
intution about the temporal complexity of each algorithm and provides
empirical evidence for their scalability of \texttt{hdiff} and lack
there of from \texttt{stdiff}. \Cref{sec:eval:merging} looks at how many
conflicts could be correctly solved by each algorith. A correct solution
is when we can automatically produce a merge that equals to what a human has 
done to reconcile the conflict, modulo parsing.

\victor{add them numbers over here!}
  We have extracted a total of ??? conflicts from \texttt{GitHub}. They
have been obtained from large public repositories in Java, JavaScript, Python,
Lua, Clojure and Bash. We have used parsers readily available in Hackage
to parse the source code with the exception of Clojure, where we
borrowed the parser from Garufi~\cite{Garufi2018}. More detailed
information about how the data was collected and versions of the packages
can be found in \Cref{sec:eval:collection}.

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

\subsection*{\texttt{stdiff}}

\begin{figure}
\end{figure}

\begin{figure}
\centering
\includegraphics[width=0.4\textwidth]{src/img/runtimes-stdiff.pdf}
\caption{Points represent runtime from \texttt{stdiff --with-stats}, which was
ran on over 7000 datapoints. Both axis are in a log-scale and the displayed lines
are for reference. It is clear \texttt{stdiff} displays a quadratic performance
for most of the time.}
\label{fig:eval:stdiff-performance}
\end{figure}


\victor{Performance does not include parsing; it has been measured with 
the help of cpu time and the deepseq package.}

\section{Synchronization}
\label{sec:eval:merging}


\section{Data Collection and Reproducibility Steps}
\label{sec:eval:collection}

  In this section we will detail how we collected our datapoints\footnote{%
\victor{which can be found online at: ???; I mean; do we even 
want to make it availble? Does the uni have servers? It's about 4Gb}}.
Each datapoint consist in four files named \texttt{O.lang}, \texttt{A.lang}, 
\texttt{B.lang} and \texttt{M.lang}, which represent the original file,
two diverging verions and the merged result produced by a human.

  Collecting these files is not too difficult and can be done with 
moderate amounds of bash scripting. Our methos is a variation of the
script used by Garufi~\cite{Garufi2018} and can be described as follows;

\begin{itemize}
  \item For each commit $c$ in a given repository such that $c$ has
two or more parents $p_0, \cdots, p_n$; checkout the repository at $c$
and attempt to \texttt{git merge}.

  \item For each file that git could not merge automatically --
obtainable through \texttt{git}'s \texttt{ls-files --unmerged} command
-- and collect the common ancestor as \texttt{O.lang}, the diverging
versions as \texttt{A.lang} and \texttt{B.lang} and the merged that
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
Overall, we acquired more 12687 conflicts diagrams which we can parse with
the parsers available to us.

\section{Discussion}

