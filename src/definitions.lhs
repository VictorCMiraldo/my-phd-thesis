%% Logistic Stuff

\usepackage{supertabular}

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{chapter}.\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
{\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\victor}[2][nolabel]{%
{\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}}
\newcommand{\todo}[2][nolabel]{%
{\color{C1} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) TODO: } #2 \textbf{$]$}}}


%% LaTeX stuff

\newenvironment{myhs*}[1][0.95\textwidth]{%
\begin{minipage}{#1}\small%
}{%
\end{minipage}%
}

\newenvironment{myhs}[1][0.95\textwidth]{%
\nopagebreak[3]%Denies latex to pagebreak on code blocks!
\begin{myhs*}[#1]  %\par\noindent\begin{minipage}{#1}\small%
}{%
\end{myhs*}%
}

\newenvironment{myforest}{%
\bgroup\footnotesize\forest%
}{%
\endforest\egroup%
}

%% Typography

\newcommand{\digress}[1]{$\lhd$ \textit{ #1 } $\rhd$}


%% Parenthetical sentences; a command makes it easy
%% to keep it homogeneous.
\newcommand{\parens}[1]{ -- #1 -- }


%% Denotations

\newcommand{\unixdiff}{\texttt{UNIX diff}}
\newcommand{\ie}{i.e.}
\newcommand{\genericssimpl}{\texttt{generics-simplistic}}

\newcommand{\TODOsuccessrate}{???\%}