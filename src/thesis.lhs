\documentclass[10pt,b5paper,cmyk]{uustthesis}
%% Remove the 'noseaweed' option to draw the fractal
%% at the section headings. This slows compilation down, though.

%% The draft option disables microtype and displays overful hboxes
%% in the text, plus its faster to compile

%% My internal packages:
\usepackage[cmyk]{hdiff-forest}
\usepackage{squiggol}

\usepackage{longtable}
% \usepackage{supertabular}
% \usepackage{multicol}
\usepackage[all]{xy}

\title{Type-Safe Generic Differencing of Mutually Recursive Families}
\titleDUTCH{Getypeerde Generieke Differentiatie van Wederzijds Recursieve Datatypes}

\author{Victor Cacciari Miraldo}

\promotor{Prof.dr. G. Keller}
\copromotor{Dr. W. Swierstra}

\NWOproject{Revision Control of Structured Data}
\NWOgrantnumber{612.001.401}

\defensedate{October 5, 2020, te 11:00 uur}
\authorbirthdate{October 16, 1991}
\authorbirthplace{S\~{a}o Paulo, Brasil}

% Include my definitions
% \input{src/my-tikz-defs}

%include polycode.fmt
%include src/stylish.lhs
%include src/definitions.lhs
%include src/notation.lhs

\newcommand{\lhsinclude}[1]{}

%% quantities

%% How many conflicts have we seen, solved, etc...
\newcommand{\qTotalUsableConf}{$12\,552$}
\newcommand{\qTotalParseErrorConf}{$2\,771$}
\newcommand{\qSolvedConf}{$3\,300$}
\newcommand{\qSolvedPerc}{$26\%$}

%% How many merge-diff cases have I seen so far?
\newcommand{\qManualMDiffAnal}{16}
\newcommand{\qManualMDiffOk}{13}


%% \linenumbers

\begin{document}
\maketitle

%% Set up the front matter of our book
\frontmatter
\tableofcontents

% \chapter{Declaration}
% Thanks to family, supervisor, friends and hops!

\chapter{Abstract}
\lhsinclude{Abstract.lhs}
%include src/Abstract.lhs


%% Starts the mainmatter
\mainmatter

%% shows measurements when in draft-mode
\displaymeasurespage


%% The marker below is used by our mock-chapter
%% script to know where to crop the file.
%% when we want to build just a single chapter
%%
%% mock-chapter-marker
%%
%% It is also important that all chapter declarations
%% have the structure:
%%
%% > \chapter{lalala}
%% > \label{...}
%% > \lhsinclude{lalala.lhs} 
%% > %include src/lalala.lhs
%%

\chapter{Introduction}
\label{chap:introduction}
\lhsinclude{Introduction.lhs}
%include src/Introduction.lhs

\chapter{Background}
\label{chap:background}
\lhsinclude{Background.lhs}
%include src/Background.lhs

\chapter{Generic Programming with Mutually Recursive Types}
\label{chap:generic-programming}
\lhsinclude{GenericProgramming.lhs}
%include src/GenericProgramming.lhs

\chapter{Structural Patches}
\label{chap:structural-patches}
\lhsinclude{StructPatches.lhs}
%include src/StructPatches.lhs

\chapter{Pattern-Expression Patches}
\label{chap:pattern-expression-patches}
\lhsinclude{PEPatches.lhs}
%include src/PEPatches.lhs

\chapter{Experiments}
\label{chap:experiments}
\lhsinclude{Experiments.lhs}
%include src/Experiments.lhs

\chapter{Discussion}
\label{chap:discussion}
\lhsinclude{Discussion.lhs}
%include src/Discussion.lhs

\appendix
\chapter{Source-Code and Dataset}
\label{chap:where-is-the-code}
\lhsinclude{ObtainingTheCode.lhs}
%include src/ObtainingTheCode.lhs


\backmatter

% \listoffigures
% \listoftables

\bibliographystyle{acm}
\bibliography{references}

%\chapter{Curriculum Vitae}
%
%\chapter{Sammenvatting}
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.
%Sommige goed samenvatting in het Nederlands.

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
