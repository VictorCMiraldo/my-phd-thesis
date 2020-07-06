  The \unixdiff{} tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used in
software version control. The fixed \emph{lines-of-code} granularity,
however, is sometimes too coarse and obscures simple changes, \ie{}, renaming
a single parameter triggers the whole line to be seen as \emph{changed}. This may
lead to unnecessary conflicts when unrelated changes occur on the same line.
Consequently, it is difficult to merge such changes automatically.

  In this thesis we discuss two novel approaches to structural
differencing, generically -- which work over a large class of
datatypes. The first approach defines a type-indexed representation of
patches and provides a clear merging algorithm, but it is
computationally expensive to produce patches with this approach. The
second approach addresses the efficiency problem by choosing an
extensional representation for patches.  This enables us to represent
transformations involving insertions, deletions, duplication,
contractions and permutations which are computable in linear time.
With the added expressivity, however, comes added
complexity. Consequently, the merging algorithm is more intricate and
the patches can be harder to reason about.

  Both of our approaches can be instantiated to mutually recursive
datatypes and, consequently, can be used to compare
elements of most programming languages.  Writing the software that
does so, however, comes with additional challenges.  To address this we
have developed two new libraries for generic programming in Haskell.

  Finally, we empirically evaluate our algorithms by a number of
experiments over real conflicts gathered from \texttt{GitHub}. Our
evaluation reveals that at least \qSolvedPerc{} of the conflicts
that developers face on a day-to-day basis could have been
automatically merged. This suggests there is a benefit in using
structural differencing tools as the basis for software version
control.
