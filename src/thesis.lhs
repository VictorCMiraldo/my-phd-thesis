\documentclass[10pt,b5paper]{uustthesis}

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
\input{src/my-tikz-defs}

%include lhs2TeX.fmt
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
%include src/chap01.lhs

\begin{forest}
  [A
    [B]
    [$\rightarrow$, change
     [Node2 [0 , metavar] [1 , metavar] ]
     [Node2 [1 , metavar] [2 , metavar] ]
    ]
  ]
\end{forest}

\chapter{Conclusion}
\input{src/chap02}

\chapter{Test 3}

\chapter{Test 4}

\appendix
\chapter{Some Formulas}

\backmatter
\listoffigures
\listoftables

\bibliographystyle{alpha}
\bibliography{references}

\end{document}


