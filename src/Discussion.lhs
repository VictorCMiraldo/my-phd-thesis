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
much greater potential. Empirical results were discussed in \Cref{chap:experiments}.

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

\section{Digressions}


From the intro to simplistics:
  \digress{After realizing that the differencing algorithms presented in
\Cref{chap:pattern-expression-patches} did not explicitly require
sums of products to work, I was able to implement a workaround
using \texttt{GHC.Generics} to encode mutually recursive families. The
main idea is to take the dual approach from
\texttt{generics-mrsop}: instead of defining which types belong in the
family, we define which types \emph{do not} belong to the family.
Corresponding with A. Serrano we discussed how this approach could
be seen as an extension of his \genericssimpl{}
library, which lead me to write the layer that handles deep representations with
support for mutual recursion on top a the preliminary version of this library,
giving rise to the \genericssimpl{} library in its current form.}

From simplistic discussion on unification's existential on maps
\digress{we could write a custom heterogeneous key-value store, but I'm doubtful this
would be worth the trouble. |Data.Map| has excellent performance and has been
thoroughly tested.} 

From deciding what can and cannot be shared
 \digress{I would like to reiterate
the \emph{avoiding-the-issue} aspect of this decision. I did attempt
to overcome this with a few methods which will be discussed later
(\Cref{sec:pepatches:discussion}). None of my attempts at solving the
issue were successful, hence, the best option really became avoiding
the issue by making sure that we can easily exclude certain trees from
being shared.}

From the internals of my implementation
\digress{I would like to also implement this
algorithm with a big-endian Patricia Tree~\cite{Okasaki1998} and
compare the results. I think the difference would be small, but worth
considering when working on a production implementation}.

From wondering about handling names in |Chg|
\digress{I wonder how an
implementation using De Bruijn indexes would look like. I'm not
immediately sure it would be easier to enforce correct indices. Through
the bowels of the code we ensure two changes have disjoint sets of
names by adding the successor of the maximum variable of one over the
other.}

From hdiff's merge
\digress{Unfortunately, I never had time to come back and refine the
merging algorithm from its prototype phase into a more polished
version. The merging algorithm was the last aspect of the project I worked on.}

Checking that the set of subtrees that appear in a chg is disjoint from
the set of subtrees moved by spn in a |Spn-Chg|
\digress{I
dislike this aspect of this synchronization algorithm quite a lot, it
feels unnecessarily complex and with no really good justification
besides the example in \Cref{fig:pepatches:merge-03}, which was
distilled from real conflicts. I believe that further work would
uncover a more disciplined way of disallowing duplications to be
introduced.}

Onto the order of equivalenecs in |splitDelInsMap|
\digress{This is yet
another aspect I am unsatisfied with and would like to see a more
disciplined approach. Will have to be future work, nevertheless.}





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
