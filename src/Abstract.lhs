  The \unixdiff{} tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used as
foundation for software version control. The granularity of the \emph{line-of-code},
however, is sometimes too coarse and shadows simple changes, like the addition
of a parameter to a function declaration. Consequently, it is difficult to 
automatically merge such changes, for example. 

  Creating tools that are able to understand differences between objects
at arbitrary granularity is challenging. The early approaches are either
not expressive enough or computationally expensive to be used at large.
In this thesis we discuss two novel approaches to structural differencing, 
which are type-safe by construction and can be used to compare 
elements of mutually recursive family. In order to write a prototype
we also had to improve on Haskell's generic programming, and ended up
developing a library for generic programming with mutually recursive types.
Our later approach benefits from a linear-time algorithm, which makes it
potentially applicable in practice.

  We evaluate our approaches using real data from \texttt{GitHub}, where
we see that at least 22\% of the conflicts that developers face on an everyday
basis could have been automatically merged. This suggest there is a real 
in using structural differencing tools as the basis for software version control.
  