Firstly, let us briefly review the
\texttt{generics-mrsop}~\cite{Miraldo2018} library, that we will use
to define a generic version of our algorithm.  This library follows
the \emph{sums-of-products} school of generic
programming~\cite{deVries2014} and, additionally, enables us to work
with mutually recursive families. This is particularly important for
this algorithm, as the abstract syntax trees of many programming
languages consist of mutually recursive types for expressions,
statements, methods, classes and other language constructs.

  Take the |Tree23| type from \Cref{sec:concrete-changes}.  Its
structure can be seen in a \emph{sum-of-products} fashion through the
|Tree23SOP| type given below.  It represents the shape in which every
|Tree23| comes and consists in two nested lists of \emph{atoms}. The
outer list represents the choice of constructor, and packages the
\emph{sum} part of the datatype whereas the inner list represents the
\emph{product} of the fields of a given constructor. The |P| notation
represents a value that has been promoted to the type
level~\cite{Yorgey2012}.

\begin{myhs}
\begin{code}
type Tree23SOP = P  ([  P [] 
                    ,   P ([ I 0 , I 0 ]) 
                    ,   P ([ I 0 , I 0 , I 0 ]) ])
\end{code}
\end{myhs}

  The atoms, in this case only |I 0|, represent a recursive position
referencing the first type in the family. In fact, a mutually
recursive family is described by \emph{a list of sums-of-products}:
one for each element in the family. We overload the word ``code'' in
singular or plural to mean the representation of a datatype, or the
representation of a family, respectively.  The context should make
clear the distinction. For example, |Tree23SOP| is the code of type
|Tree23| and |Tree23Code| is the codes for the mutually recursive
family, which in this case, contains only one type.

\begin{myhs}
\begin{code}
type Tree23Code = P  [ Tree23SOP ]
\end{code}
\end{myhs}

 The \texttt{generics-mrsop} uses the type |Atom|
to distinguish whether a field is a recursive position referencing the
$n$-th type in the family, |I n|, or a opaque type, for example, |Int|
or |Bool|, which are represented by |K KInt|, |K KBool|.

  Let us now take a mutually recursive family with more than one
element and see how it is represented within the \texttt{generics-mrsop}
framework. The mutually recursive family containing types |Zig| and |Zag| has
its codes defined as a list of codes, one for each member of the family:

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data Zig  = Zig Int   | ZigZag Zag
data Zag  = Zag Bool  | ZagZig Zig
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
type ZigCodes = P  [ P [ P [ K KInt ]   , P [ I 1 ] ]
                   , P [ P [ K KBool ]  , P [ I 0 ] ]
                   ]
\end{code}
\end{myhs}
\end{minipage} %

  Note that the codes come in the same order as the elements of the
family. The code for |Zig| is the first element of the |ZigCodes| type
level list. It consists in two lists, since |Zig| has two
constructors. One receives a value of type |Int|, the other consists
in a recursive call to the second element of the family. The code acts
as a recipe that the \emph{representation} functor must follow in
order to interpret those into a type of kind |Star|.

  The representation is defined by the means of $n$-ary sums (|NS|)
and products (|NP|) that work by induction on the \emph{codes} and one
interpretation for atoms (|NA|). Their definition together with
their respective elimination principles can be found in \Cref{fig:nsnpna}.

\begin{figure}
\begin{minipage}[t]{.5\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f x      -> NS f (x PCons xs)
  There  :: NS f xs  -> NS f (x PCons xs)
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
data NP :: (k -> Star) -> [k] -> Star where
  Nil   :: NP f (P [])
  Cons  :: f x -> NP f xs -> NP f (x PCons xs)
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I :: phi i  -> NA phi (I i)
  NA_K :: Opq k  -> NA phi (K k)
\end{code}
\end{myhs}
\end{minipage} %
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
elimNS :: (forall at dot f at -> a) -> NS f s -> a
elimNS f (There s)  = elimNS f s
elimNS f (Here x)   = f x
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
elimNP :: (forall at dot f at -> a) -> NP f p -> [a]
elimNP f Nil          = []
elimNP f (Cons x xs)  = f x : elimNP f xs
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
elimNA  ::  (forall ix dot f x -> a) -> (forall k dot g k -> a) 
        ->  NA f g at -> a
elimNA f g (NA_I x)  = f x
elimNA f g (NA_K x)  = g x
\end{code}
\end{myhs}
\end{minipage}
\caption{Interpretation and elimination principles for each component of a sum-of-products code.}
\label{fig:nsnpna}
\end{figure}


  The |NS| type is responsible for determining the choice of
constructor whereas the |NP| applies a representation functor to all
the fields of the selected constructor.  Finally, |NA| distinguishes
between representation of a recursive position from an opaque
type. Although the \texttt{generics-mrsop} provides a way to customize
the set of opaque types used, this is not central do the developments
in this paper and hence we will assume a type |Opq| that interprets
the necessary atom types, i.e., |Int|, |Bool|, etc. We refer the
interested reader to the original paper~\cite{Miraldo2018} for more
information. Nevertheless, we define the representation functor |Rep|
as the composition of the interpretations of the different pieces:

\begin{myhs}
\begin{code}
type Rep phi = NS (NP (NA phi))
\end{code}
\end{myhs}

  Finally, we tie the recursive knot with a functor of kind |Nat ->
Star| that is passed as a parameter to |NA| in order to interpret the
recursive positions. The familiar reader might recognize it as the
indexed least fixpoint:

\begin{myhs}
\begin{code}
newtype Fix (codes :: P [ P [ P [ Atom ] ] ]) (ix :: Nat)
  = Fix { unFix :: Rep (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

  Here, |Lkup codes ix| denotes the type level lookup of the element
with index |ix| within the list |codes|. This type family throws a
type error if the index is out of bounds.  The generic versions of the
constructors of type |Zig| are given by:

\begin{myhs}
\begin{code}
gzig :: Int -> Fix ZigCodes 0
gzig n = Fix (Here (Cons (NA_K (OpqInt n)) Nil))
gzigzag :: Fix ZigCodes 1 -> Fix ZigCodes 0
gzigzag zag = Fix (There (Here (Cons (NA_I zag) Nil)))
\end{code}
\end{myhs}

  One of the main benefits of the \emph{sums-of-products} approach to
generic programming is that it enables us to pattern match
generically. In fact, we can state that a value of a type consists
precisely of a choice of constructor and a product of its fields by
defining a \emph{view} type. For example, we take the
\emph{constructor} of a generic type to be:

\begin{myhs}
\begin{code}
data Constr :: [[k]] -> Nat -> Star where
  CZ ::                 Constr (x PCons xs)  Z
  CS :: Constr xs c ->  Constr (x PCons xs)  (S c)
\end{code}
\end{myhs}

  The |Constr sum c| type represents a predicate indicating that |c|
is a valid constructor for |sum|, that is, it is a valid index into the
type level list |sum|. This enables us to define a |View| over a value
of a sum type to be a choice of constructor and corresponding
product. We can then unwrap a |Fix codes i| value into its topmost
constructor and a product of its fields with the |sop| function.

\begin{myhs}
\begin{code}
data View :: (Nat -> Star) -> P [ P [ Atom ] ] -> Star where
  Tag :: Constr sum c -> NP (NA phi) (Lkup sum c) -> View phi sum
sop :: Fix codes i -> View (Fix codes) (Lkup codes i)
\end{code}
\end{myhs}

This brief introduction covers the basics of generic programming in Haskell
that we will use in this paper. We refer the interested reader to the
literature~\cite{deVries2014,Miraldo2018} for a more thorough overview.