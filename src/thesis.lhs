\documentclass[10pt,b5paper,draft,noseaweed]{uustthesis}
%% Remove the 'noseaweed' option to draw the fractal
%% at the section headings. This slows compilation down, though.

%% The draft option disables microtype and displays overful hboxes
%% in the text, plus its faster to compile

\usepackage{hs-digems-forest}
\usepackage[all]{xy}

\title{Type-Safe Generic Differencing of Mutually Recursive Families}
\titleDUTCH{same title in dutch}

\author{Victor Cacciari Miraldo}

\promotor{Prof.dr. J.T. Jeuring}
\copromotor{Dr. W. Swierstra}

\NWOproject{Revision Control of Structured Data}
\NWOgrantnumber{612.001.401}

\defensedate{hopefuly, in the future!}
\authorbirthdate{october 16, 1991}
\authorbirthplace{S\~{a}o Paulo, Brasil}

% Include my definitions
% \input{src/my-tikz-defs}

%include lhs2TeX.fmt
%include src/definitions.lhs
%include src/notation.lhs

\newcommand{\lhsinclude}[1]{}

\begin{document}
\maketitle

%% Set up the front matter of our book
\frontmatter
\tableofcontents

\chapter{Declaration}
Thanks to family, supervisor, friends and hops!

\chapter{Abstract}
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.

\chapter{Sammenvatting}
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.
Sommige goed samenvatting in het Nederlands.

%% Starts the mainmatter
\mainmatter
\chapter{Introduction}
\label{chap:introduction}
\lhsinclude{Introduction.lhs}
%include src/Introduction.lhs

\chapter{Background}
\label{chap:background}
\lhsinclude{Background.lhs}
%include src/Background.lhs

\chapter{The \texttt{generics-mrsop} Library}
\label{chap:generic-programming}
\lhsinclude{GenericProgramming.lhs}
%include src/GenericProgramming.lhs

\chapter{Structural Patches}
\label{chap:structural-patches}
\lhsinclude{StructPatches.lhs}
%include src/StructPatches.lhs

% Show the code in Haskell, talk about the Agda model.
% Mention that Arian translated the Agda to Haskell and
% added mutual recursion to the model.

\chapter{Pattern-Expression Patches}
\label{chap:pattern-expression-patches}
\lhsinclude{PEPatches.lhs}
%include src/PEPatches.lhs

\chapter{Discussion}
\label{chap:discussion}
\lhsinclude{Discussion.lhs}
%include src/Discussion.lhs

% \appendix
% \chapter{Some Formulas}

\backmatter

% \listoffigures
% \listoftables

\bibliographystyle{abbrvnat}
\bibliography{references}

\printindex

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
