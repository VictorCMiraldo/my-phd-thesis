  The \unixdiff{} tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used as
foundation for software version control. The granularity of the \emph{line-of-code},
however, is sometimes too coarse and shadows simple changes. This may
lead to unecessary conflicts when unrelated changes occur on the same line.
Consequently, it is difficult to automaticaly merge such changes.

  In this thesis we discuss two novel approaches to structural differencing,
which are type safe by construction. Both approaches can be instantiated
to mutually recursive families and, consequently, can be used to compare
elements of most practical languages. The first approach defines a type-indexed representation of
patches, which provides a clear merging algotihm -- but is computationally
expensive to produce patches. The second, more efficient, improves
on the computation of patches but suffers from its extensionality and is
complex to reason about and merge.

Finally, we empirically evaluate our algorithms by a number of experiments
over real conflicts gathered from \texttt{GitHub}. Our evaluation reveals
that at least 22\% of the conflicts that developers face on an everyday
basis could have been automatically merged. This suggest there is a real 
in using structural differencing tools as the basis for software version control.
  