  This thesis explored two preliminary approaches to structural
differencing and the respective generic programming
libraries necessary to implement them. The first method,
\texttt{stdiff}, was presented in \Cref{chap:structural-patches} and
revealed itself to be unpratical due to poor performance.  The second
method, \texttt{hdiff}, was discussed in
\Cref{chap:pattern-expression-patches} and experimented with in
\Cref{chap:eval}.

\section{The Future of Structural Differencing}

  Applying structural differncing tools to version control of source
code comes with many challanges. This dissertation addresses just a
few of them, namelly, those around representing and computing patches
efficiently. There are a number of other difficulties that would need
to be addressed if we ever want an industrial structural differncing
tool. In the remainder of this section we take a look at some of the
most pressing challenges and discuss a little about the future of
structural differencing.

  There are three main difficulties in applying structural differencing
with the objective of writing better merge algorithms:
\begin{enumerate}
\item How to properly handle formatting and comments of source code:
should the AST keep this information? If so, the tree matching must
be adapted to cope with this. Two equal trees must be matched regardless of whether
or not they appeared with a different formatting in their respective source files.
\item How to ensure that subtrees are only being shared wihin their
respective scope and, equally importantly, how to specify which datatypes
of the AST are affected by scopes.
\item When merging fails, returning a patch with conflicts, a human
must interact with the tool and solve the conflicts. What kind of interface
would be suitable for that? Further ahead, comes que question of
automatic conflict solving domain-specific languages. Could we configure
the merge algorithm to always chose higher version numbers, for example,
whenever it finds a conflict in, say, a cabal file?
\end{enumerate}

  Fixing the obstacles above in a generic way would be a significant
effort.  So much so that it makes me question the applicability of
structural differencing for the exclusive purpose of merging
source-code.  From a broader perspective, however, there are many
interesting applications that could benefit from structural
differencing techniques.  In particular, we can probably use
structural differencing to aid any task where a human does not
directly edits the files being analyzed or when the result of the
analisys does not need to be interacted with.  For example, it should
be possible to deploy \texttt{hdiff} to provide a human readable
summary of a patch, something that looks at the working directory,
computes the structural diffs between the various files, just like
\texttt{git diff}, but displays information in the lines of:
%
\begin{alltt}
some/project/dir \$ hsummary
function fact refactored;
definition of fact changed;
import statements added;
\end{alltt}

  In combination with the powerful web interfaces of services like GitHub or
GitLab, we could also use such tools to study the evolution of code or to
inform the assignee of a pull request wether or not it detected the
changes to be \emph{structurally disjoint}. If nothing else, we could
at least direct the attention of the developers to the locations where
actual conflicts are.

  Finally, differencing file formats that are based on \texttt{JSON} or
\texttt{XML}, such as word and spreadsheet processors, might be much
easier than source code. The formatting of a \texttt{.odf} file is automatically
generated and independent of the formatting of document inside the file.
Some care must be taken with the unordered trees, even though I conjecture
\texttt{hdiff} would behave mostly alright.

\section{Concluding Remarks}

  This dissertation is a scratch on the surface of the problems
surrounding structural differencing for source-code
versioning. Although the design space is large, we have studied some
of design options. We have found approaches that are easy to merge but
hard to compute and vice-versa.  In the process of developping our
prototypes we have also improved the Haskell ecosystem for generic
programming. Finally, we have seen that \texttt{hidff} has shown
promissing results, even if its merging algorithm is more intricate.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
