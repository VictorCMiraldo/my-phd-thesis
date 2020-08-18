  Even though the main topic of this thesis is \emph{structural
differencing}, a significant part of the contribution lies in the field of
generic programming.  The two libraries we wrote make it possible to
use powerful generic programming techniques over larger classes of
datatypes than what was previously available.  In particular, defining
the generic interpretation as a cofree comonad and a free monad
combined in a single datatype is very powerful. Being able to annotate
and augment datatypes, for example, was paramount for scaling our
algorithms.

  On \emph{structural differencing}, we have explored two preliminary
approaches. A first method, \texttt{stdiff}, was presented in
\Cref{chap:structural-patches} and revealed itself to be inpractical
due to poor performance. The second method, \texttt{hdiff},
introduced in \Cref{chap:pattern-expression-patches}, has shown
much greater potential. Empirical results were discussed in 
\Cref{chap:experiments}.

\section{The Future of Structural Differencing}

  The larger picture of structural differencing is more subtle, though.
It is not because our preliminary prototype has shown good results
that we are ready to scale it to be the next \texttt{git merge}.
There are three main difficulties in applying structural differencing
to source-code with the objective of writing better merge algorithms:
\begin{enumerate}
\item How to properly handle formatting and comments of source code:
should the AST keep this information? If so, the tree matching must
be adapted to cope with this. Two equal trees must be matched regardless of whether
or not they appeared with a different formatting in their respective source files.
\item How to ensure that subtrees are only being shared within their
respective scope and, equally importantly, how to specify which datatypes
of the AST are affected by scopes.
\item When merging fails, returning a patch with conflicts, a human
must interact with the tool and solve the conflicts. What kind of interface
would be suitable for that? Further ahead, comes the question of
automatic conflict solving domain-specific languages. Could we configure
the merge algorithm to always chose higher version numbers, for example,
whenever it finds a conflict in, say, a config file?
\end{enumerate}

  Fixing the obstacles above in a generic way would require a significant
effort.  So much so that it makes me question the applicability of
structural differencing for the exclusive purpose of merging
source-code.  From a broader perspective, however, there are many
other interesting applications that could benefit from structural
differencing techniques.  In particular, we can probably use
structural differencing to aid any task where a human does not
directly edit the files being analyzed or when the result of the
analysis require no further interaction.  For example, it should
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
GitLab, we could also use tools like \texttt{hdiff} to study the evolution of
code or to inform the assignee of a pull request whether or not it detected the
changes to be \emph{structurally disjoint}. If nothing else, we could
at least direct the attention of the developers to the locations in the source-code
where there are actual conflicts and the developer has to make a choice.
That is where mistakes are more likely to be made. One way of circumventing
the formatting and comment issues above is to write a tool
that checks whether the developer included all changes in a sensible way
and warns them otherwise, but it is always a human performing the actual merge.

  Finally, differencing file formats that are based on \texttt{JSON}
or \texttt{XML}, such as document processors and spreadsheet processors, might be
much easier than source code. Take the formatting of a \texttt{.odf}
file for example.  It is automatically generated and independent of
the formatting of document inside the file and it has no scoping or
sharing inside, hence, it would be simpler to deploy a structural
merging tool over \texttt{.odf} files.  Some care must be taken with
the unordered trees, even though our conjecture is that \texttt{hdiff} would
behave mostly alright.

\section{Future Work}

  Although the long term future of structural differencing specifically
for source-code versioning is uncertain, there are numerous fronts to continue
working on many of the aspects developed and discussed in this dissertation,
in particular, \texttt{hdiff} (\Cref{chap:pattern-expression-patches}).
We refer the interested reader to \Cref{sec:pepatches:discussion} for
a more detailed discussion on these topics, but proceed with
a summary of interesting directions for future work.
  
  One clear option for further work is the improvement of the merge
algorithm, presented in \Cref{sec:pepatches:merging}.  A good way to
start could be restricting \texttt{hdiff} to produce only linear
patches (context extraction with |Patience| option) and use these
guarantees to study and develop a merge algorithm in a more
disciplined fashion. It is possible that the extra guarantees that are
provided by linear patches (metavariables are used only once) would
simplify the algorithm to the point where we can start thinking about
proving properties about it. We would hope that some simplifications
would remove the need for some of the more ad-hoc checks that are currently
present in the merge algorithm -- take the example from
\Cref{fig:pepatches:merge-03}, which feels overly complicated and with
no real good justification besides having found these situation in
practice. Finally, our experiments have shown us that the |Patience|
extraction method gives superior success rates anyway.

  Another interesting front would be to define the type of |Chg|
in a well-scoped manner, essentially using De Bruijn indicies. 
This would pottentially complicate some of the simpler parts of
\texttt{hdiff} but could provide important insight into how to
handle variables when merging in a very disciplined way.
Different representations for |Chg| could also shed some light
on how to better control which subtrees can be shared or not.

  The actual implementation of \texttt{hdiff} could also benefit
from further work. We could work on optimizing the generic programming 
libraries for performance, rewriting parts of the code to use
standard implementations well-known data structures instead,
or even better visualization of patches using pretty printers.

  Finally, the metatheory surrounding \texttt{hdiff}'s |Chg| and |Patch| 
should be worked on.  In \Cref{sec:pepatches:meta-theory} we have seen how |Chg|
forms a partial monoid with a simple composition operation, but we
also seen how the trivial inverse operaton does not give us a partial
group. It could give us an inverse semigroup, for it has a weaker
notion of \emph{inverse}. In fact, Darcs patch theory have been
formalised with inverse semigrougs~\cite{Jacobson2009}. 
Additionally, using the canonical extension order (i.e.,
comparing domains of application functions) is not a great option for
defining \emph{the best} patch. It would be interesting to see
whether a categorical approach, similar to Mimram's work \cite{Mimram2013}, 
could provide more educated insights in that direction. 

\section{Concluding Remarks}

  This dissertation explored a novel approach to structural
differencing and a successful prototype for computing
and merging patches for said approach. The main novelty
comes from relying on unrestricted tree-matchings, which are possible
because we never translate to an edit-script-like structure.
We have identified the challenges of employing such techniques
to merging of source-code but still achieved encouraging
empirical results. In the process of developing our
prototypes we have also improved the Haskell ecosystem for generic
programming.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "thesis.lhs"
%%% End:
