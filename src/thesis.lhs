\documentclass[10pt,b5paper,noseaweed]{uustthesis}
%% Remove the 'noseaweed' option to draw the fractal
%% at the section headings. This slows compilation down, though.

\usepackage{hs-digems-forest}
\usepackage{lipsum}

\title{Testing A Large Title YAY}
\titleDUTCH{Same title in Dutch}

\author{Victor Cacciari Miraldo}

\promotor{Prof.dr. J.T. Jeuring}
\copromotor{Dr. W. Swierstra}

\NWOproject{Revision Control of Structured Data}
\NWOgrantnumber{111.111.111}

\defensedate{hopefuly, in the future!}
\authorbirthdate{october 16, 1991}
\authorbirthplace{S\~{a}o Paulo, Brasil}

% Include my definitions
% \input{src/my-tikz-defs}

%include lhs2TeX.fmt
%include src/definitions.lhs
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

%% Starts the mainmatter
\mainmatter

\chapter{Introduction}
\label{chap:introduction}
%include src/Introduction.lhs

\chapter{Generic Programming}
\label{chap:generic-programming}
%include src/GenericProgramming.lhs

\chapter{Structural Patches}
\label{chap:structural-patches}
%include src/StructPatches.lhs

\chapter{Pattern-Expression Patches}
\label{chap:pattern-expression-patches}
%include src/PEPatches.lhs

\chapter{Discussion}
\label{chap:discussion}
%include src/Discussion.lhs

% \appendix
% \chapter{Some Formulas}

\backmatter

% \listoffigures
% \listoftables

\bibliographystyle{alpha}
\bibliography{references}

\printindex

\end{document}


