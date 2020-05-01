# Type-Safe Generic Differencing of Mutually Recursive Families

## Abstract

The `UNIX diff` tool -- which computes the differences between two
files in terms of a set of copied lines -- is widely used in
software version control. The fixed _lines-of-code_ granularity,
however, is sometimes too coarse and obscures simple changes, i.e., renaming
a single parameter triggers the whole line to be seen as _changed_. This may
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
experiments over real conflicts gathered from `GitHub`. Our
evaluation reveals that at least 26% of the conflicts
that developers face on an everyday basis could have been
automatically merged. This suggests there is a benefit in using
structural differencing tools as the basis for software version
control.

## Compiling the PDF

There should be a `pdf` file already pre-compiled in the root of this repo;
if you want to compile one yourself, you might need to increase the memory 
limits of your latex distribution. To do that 
find your relevant config file; mine was in `/usr/share/texmf/web2c/texmf.cnf`
then go to where it says something like: `maim_memory = ...` and increase those
values. I have:

```
main_memory   = 15000000
extra_mem_top = 5000000
extra_mem_bot = 5000000
```

After that, run `sudo texhash` and you should be good. 

