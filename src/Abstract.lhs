  The \unixdiff{} tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used as
foundation for software version control. The granularity of the \emph{line-of-code},
however, is sometimes too coarse and shadows simple changes. This may
lead to unnecessary conflicts when unrelated changes occur on the same line.
Consequently, it is difficult to automatically merge such changes.

  In this thesis we discuss two novel approaches to structural
differencing, which are type safe by construction.   The first
approach defines a type-indexed representation of patches, which
provides a clear merging algorithm -- but is computationally expensive
to produce patches. The second approach addresses the efficiency
problem by choosing an extensional representation for patches.  This
enables us to represent insertions, deletions, duplication,
contractions and permutations and is computable in linear time. With
the added expressivity, however, comes added complexity. Consequently,
the merging algorithm is more intricate and the patches can be harder
to reason about.

  Both of our approaches can be instantiated to mutually recursive families and, 
consequently, can be used to compare elements of most practical languages.
Writing the software that does so, however, comes with additional challenges.
Namelly, in closing the existing gap for generic programming with mutually recursive
families in Haskell. We present two libraries for doing so, one more complete
which stumbled upon compiler bugs, rendering it unusubale for the time being 
and a second library, which works around the bugs enabling us to run
at least one of our differencing algorithms on a variety of real programming languages.

  Finally, we empirically evaluate our algorithms by a number of experiments
over real conflicts gathered from \texttt{GitHub}. Our evaluation reveals
that at least \TODOsuccessrate{} of the conflicts that developers face on an everyday
basis could have been automatically merged. This suggest there is can be a benefit
in using structural differencing tools as the basis for software version control.