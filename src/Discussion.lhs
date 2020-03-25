
\victor{Summarize contributions:

\begin{itemize}
\item Two libraries for generic prog; 
\item two approaches for structural diffing;
\item empirical validation
\end{itemize} 

}

  This thesis explored two preliminary approaches to structural
differencing, coupled with the respective generic programming
libraries necessary to implement them. The first method,
\texttt{stdiff}, was presented in \Cref{chap:structural-patches} and
reveled itself to be unpratical due to poor performance.  The second
method, \texttt{hdiff}, was discussed in
\Cref{chap:pattern-expression-patches} and experimented with in
\Cref{chap:eval}. Moreover, it has shown better potential to be used
in practical applications. 


\section{The Future of Structural Differencing}

\victor{What does structural differencing still needs, as a field?}

\victor{Why is structural differencing not so suitable for source code?
\begin{itemize}
  \item Parsers; formating; comments; scope; sharing...
  \item Conflict resolution: how to even do it?
\end{itemize}
}

\victor{Ok... then what else could use it? From a differencing perspective,
tools that provide human-readable description of how patches, and
eventually how the whole code, evolved can really benefit from structdiffs.
Perhaps github could run \texttt{hdiff} under the hood and indicate when a pull request
is ``structurally disjoin'', hence requiring less attention. It could even list
what was done by each party: alice refactored function f; John renamed variable x to y inside f.
It could ultimately leave the final result to the human, but this would already provide valuable information.
I'd call this change classification.

Differencing of xml-based things such as Word and Excel might benefit, where the
formating of the contents is independent of the formating of the file.
Yet, XML as unordered trees would require some adaptations of our methods, at least.

From an edit-distance perspective its unclear.
}

\section{Concluding Remarks}

  This dissertation is a scratch on the surface of the problems surrounding
structural differencing for source-code. 


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
