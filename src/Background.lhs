\section{The \texttt{UNIX diff}}

\section{Edit Scripts and Edit Distance}
\label{sec:edit-scripts}

\section{Tree Edit Distance}

\section{Generic Programming}

  \emph{(Datatype-)generic programming}\index{Generic Programming}
provides a mechanism to write functions by induction on the structure
of algebraic datatypes~\cite{Gibbons2006}.  A well-known example is
the |deriving| mechanism in Haskell, which frees the programmer from
writing repetitive functions such as equality~\cite{haskell2010}. A
vast range of approaches were available as preprocessors, language
extensions, or libraries for Haskell~\cite{Rodriguez2008,Magalhaes2012}.  

  The core idea behind generic programming is the fact that a number
of datatypes can be described in a uniform fashion.  Hence, if a
programmer were to write programs that work over this uniform
representation, these programs would immediately work over a variety
of datatypes. We are interested in writing differencing algorithms for
abstract syntax trees, hence our datatypes will be mutually recursive
families.  Our programs must operate over \emph{any} such
family. Consequently, we must have a powerful generic programming
approach that is capable of (A) representing mutually recursive
datatypes and (B) easily operating over them by the means of
expressive combinators. One of the contributions of this thesis is the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, which provides a
combinator-based approach to generic programming with mutually
recursive types. We explore \texttt{generics-mrsop} later, in
\Cref{chap:generic-programming}. In the remainder of this section we
glance on the existing techniques and place them on the design space.

  Consider the following datatype representing binary trees
with data stored in their leaves:

\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}

  A value of type |Bin a| consists of a choice between two
constructors.  For the first choice, it also contains a value of type
|a| whereas for the second it contains two subtrees as children. This
means that the |Bin a| type is isomorphic to |Either a (Bin a , Bin
a)|. Different libraries differ on how they define their underlying
generic descriptions.  For example,
\texttt{GHC.Generics}~\cite{Magalhaes2010}\index{GHC.Generics}, which
comes bundled with GHC, defines the representation of |Bin| as the
following datatype:

\begin{myhs}
\begin{code}
Rep (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}

which is a direct translation of |Either a (Bin a , Bin a)|, but using
the combinators provided by \texttt{GHC.Generics}, namely |:+:| and
|:*:|. In addition, we require two conversion functions |from :: a ->
Rep a| and |to :: Rep a -> a| which form an isomorphism between |Bin
a| and |Rep (Bin a)|.  Finaly, all is tied to the original datatype
using a type class:

\begin{myhs}
\begin{code}
class Generic a where
  type Rep a :: Star
  from  :: a      -> Rep a 
  to    :: Rep a  -> a
\end{code}
\end{myhs}

  Most generic programming libraries follow a similar pattern of
defining the \emph{description} of a datatype in the provided uniform
language by some type level information, and two functions witnessing
an isomorphism. A important feature of such library is how this
description is encoded and which are the primitive operations for
constructing such encodings, as we shall explore in
\Cref{sec:designspace}. Some libraries, mainly deriving from the
\texttt{SYB} approach~\cite{Lammel2003,Mitchell2007}, use the |Data|
and |Typeable| type classes instead of static type level information
to provide generic functionality.  These are a completely different
strand of work from ours.

  \Cref{fig:gplibraries} shows the main libraries relying on type
level representations. In the \emph{pattern functor}\index{pattern
functor} approach we have \texttt{GHC.Generics}~\cite{Magalhaes2010},
being the most commonly used one, that effectively replaced
\texttt{regular}~\cite{Noort2008}.  The former does not account for
recursion explicitly, allowing only for a \emph{shallow}
representation, whereas the later allows for both \emph{deep} and
\emph{shallow} representations by maintaining information about the
recursive occurrences of a type. Maintaining this information is
central to some generic functions, such as the generic |map| and
|Zipper|, for instance.  Oftentimes though, one actually needs more
than just one recursive type, justifying the need to
\texttt{multirec}~\cite{Yakushev2009}.

\begin{figure}\centering
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \multirow{2}{*}{\textbf{\texttt{generics-mrsop}}} \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
\caption{Spectrum of static generic programming libraries}
\label{fig:gplibraries}
\end{figure}


  These libraries are too permissive though, for instance, |K1 R Int :*: Maybe|
is a perfectly valid \texttt{GHC.Generics} \emph{pattern functor} but
will break generic functions, i.e., |Maybe| is not a combinator. 
The way to fix this is to ensure that the
\emph{pattern functors} abide by a certain format, by defining them
by induction on some \emph{code}\index{generic programing:code} that can be
inspected and matched on. This is the approach of
\texttt{generics-sop}~\cite{deVries2014}. The more restrictive
code approach allows one to write concise, combinator-based,
generic programs. The novelty in our work is in the intersection of
both the expressivity of \texttt{multirec}, allowing the encoding of
mutually recursive families, with the convenience of the more modern
\texttt{generics-sop} style. In fact, it is worth noting that neither 
of the aforementioned libraries \emph{compete} with out work. We 
extend both in orthogonal directions, resulting in a new design altogether,
that takes advantage of some modern Haskell extensions that the authors of
the previous work could not enjoy.

