  This thesis explored two preliminary approaches to structural
differencing, coupled with the respective generic programming
libraries necessary to implement them. The first method,
\texttt{stdiff}, was presented in \Cref{chap:structural-patches} and
revealed itself to be unpratical due to poor performance.  The second
method, \texttt{hdiff}, was discussed in
\Cref{chap:pattern-expression-patches} and experimented with in
\Cref{chap:eval}. Moreover, it has shown better potential to be used
in practical applications.


\section{The Future of Structural Differencing}

  Applying structural differncing tools to version control of source
code comes with many challanges. This dissertation addresses some
of these challanges. Namelly, those around representing and
computing patches efficiently. There are a number of further challanges
that would need to be addressed if we ever want an industrial
structural differncing tool out there. The three most pressing
would be the following.

\begin{enumerate}
\item How to properly handle formatting and comments of source code:
should the AST keep this information ? If so, the tree matching must
be adapted to cope with this.
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

  From a broader perspective, however, there are interesting applications
closely related to version control that could benefit greatly from
structural differencing techniques, without bumping into the challenges above.
I conjecture that, with moderate effort, we could deploy \texttt{hdiff} to
provide a human readable summary of a patch, something that looks
at the working directory, computes the structural diffs between the various
files, just like \texttt{git diff}, but displays information in the lines of:
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

  This dissertation is a scratch on the surface of the problems surrounding
structural differencing for source-code.

 Design-space is very large; We found algortihms that are easy to merge
and hard to compute and vice-versa.



If \texttt{hdiff --patience} does show better merging capability even under
the more difficult merging algorithm, maybe we should disallow duplications
and contractions altogether. This does go hand in hand with sharing; with
better sharing control we could understand that local variable declarations
are not to be shared outside their scope.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
