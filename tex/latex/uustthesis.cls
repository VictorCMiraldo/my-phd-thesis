%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                            %%
%% Class ``UU Software Tech. Thesis Template''                                %%
%%                                                                            %%
%% A PhD thesis LaTeX template for Cambridge University Engineering Department%%
%%                                                                            %%
%% Version: v0.0.1                                                            %%
%% Authors: Victor Cacciari Miraldo                                           %%
%% License: MIT License (c) 2018 Victor Cacciari Miraldo                      %%
%% GitHub Repo: https://github.com/VictorCMiraldo/latex-uustthesis            %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand\fileversion{0.0.1}
\newcommand\filedate{2018/08/01}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{uustthesis}[\filedate\space Utrecht University Software Technology Thesis Template (v\fileversion)]
\typeout{https://github.com/VictorCMiraldo/latex-uustthesis}

%% This class file was heavily inspired by:
%%   - https://github.com/suchow/Dissertate commit 58b4f
%%   - https://github.com/kks32/phd-thesis-template/blob/master/Classes/PhDThesisPSnPDF.cls
%%

% Font Size
\DeclareOption{10pt}{\PassOptionsToClass{10pt}{book}}%
\DeclareOption{11pt}{\PassOptionsToClass{11pt}{book}}%
\DeclareOption{12pt}{\PassOptionsToClass{12pt}{book}}%

% Page Size
\newcommand\PHD@papersize{a4paper} % Set Default as a4paper
\DeclareOption{a4paper}{\renewcommand\PHD@papersize{a4paper}}
\DeclareOption{a5paper}{\renewcommand\PHD@papersize{a5paper}}
\DeclareOption{b5paper}{\renewcommand\PHD@papersize{b5paper}}
\DeclareOption{letterpaper}{
  \ClassWarning{uustthesis}{The University of Utrecht
    thesis guidelines recommend using A4 for MSc thesis
    and B5 for PhD thesis.}
  \renewcommand\PHD@papersize{letterpaper}
}
\PassOptionsToClass{\PHD@papersize}{book}%

% Column layout
\newcommand\PHD@numsides{twoside}
\newif\ifPHD@istwosides
\PHD@istwosidestrue
\DeclareOption{oneside}{\renewcommand\PHD@numsides{oneside} \PHD@istwosidesfalse}%
\DeclareOption{twoside}{\renewcommand\PHD@numsides{twoside}}%
\PassOptionsToClass{\CurrentOption}{\PHD@numsides}

\newif\ifPHD@ismsccover
\PHD@ismsccoverfalse
\DeclareOption{msc}{\PHD@ismsccovertrue}
\DeclareOption{phd}{\PHD@ismsccoverfalse}

\newif\ifPHD@isdrawseaweed
\PHD@isdrawseaweedtrue
\DeclareOption{noseaweed}{\PHD@isdrawseaweedfalse}

\newif\ifPHD@isdraft
\PHD@isdraftfalse
\DeclareOption{draft}{
\PHD@isdrafttrue
\PassOptionsToClass{draft}{book}
}

\DeclareOption{cmyk}{\PassOptionsToPackage{cmyk}{xcolor}}

%% Here we can pass undeclared options to some class
%% or package
\DeclareOption*{%
  \ClassWarning{uustthesis}{Unknown option '\CurrentOption'.
I'll pass it to 'book' just in case.}
  \PassOptionsToClass{\CurrentOption}{book}%
}
\ProcessOptions\relax
%% This finishes the 'options' section

%% We'll build on top of the 'book' class.
\LoadClass{book}

%% Necessary Packags
\RequirePackage{xcolor}
\RequirePackage{tikz}
\RequirePackage{ccaption}
\RequirePackage{graphicx}
\RequirePackage{setspace}
\RequirePackage{amsmath}
\RequirePackage{amssymb}

%%%%%%%%%%%%%%%%
%% Font setup %%
%%%%%%%%%%%%%%%%

%% Font Confiruation using unicode-math package
%% https://tex.stackexchange.com/questions/30049/how-to-select-math-font-in-document#30066
%%
\usepackage{unicode-math}
\defaultfontfeatures{Scale=MatchLowercase}
\setmainfont[
    Path           = ./tex/latex/fonts/,
    BoldFont       = STIXTwoText-Bold.otf,
    ItalicFont     = STIXTwoText-Italic.otf,
    BoldItalicFont = STIXTwoText-BoldItalic.otf,
]{STIXTwoText-Regular.otf}
\setmathfont{STIX Two Math}

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%% Our Commands %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

\newcommand{\HRule}{\rule{\linewidth}{0.5mm}} % Defines a new command for horizontal lines, change thickness here

\newcommand{\dnormalspacing}{1.2}
\newcommand{\dcompressedspacing}{1.0}

% Block quote with compressed spacing
\let\oldquote\quote
\let\endoldquote\endquote
\renewenvironment{quote}
    {\begin{spacing}{\dcompressedspacing}\oldquote}
    {\endoldquote\end{spacing}}

% Itemize with compressed spacing
\let\olditemize\itemize
\let\endolditemize\enditemize
\renewenvironment{itemize}
    {\begin{spacing}{\dcompressedspacing}\olditemize}
    {\endolditemize\end{spacing}}

% Enumerate with compressed spacing
\let\oldenumerate\enumerate
\let\endoldenumerate\endenumerate
\renewenvironment{enumerate}
    {\begin{spacing}{\dcompressedspacing}\oldenumerate}
    {\endoldenumerate\end{spacing}}

%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%
%% Text Layout %%
%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%

\RequirePackage{geometry}
%% Margins and Geomtry config
\geometry{\PHD@papersize}
% https://tex.stackexchange.com/questions/249190/recommended-margin-and-binding-offset
\geometry{textwidth=.666\paperwidth}
\geometry{textheight=.72\paperheight}
\geometry{vmarginratio=5:7}
\geometry{nofoot}
% \geometry{showframe}
\ifPHD@istwosides
  \geometry{hmarginratio=4:6}
  \geometry{\PHD@numsides}
  \geometry{bindingoffset=6mm}
\else
  \geometry{centering}
\fi

% Headings and headers.
\RequirePackage{fancyhdr}
\RequirePackage[md, sc]{titlesec}
\setlength{\headheight}{15pt}
\pagestyle{plain}
\RequirePackage{titling}

\RequirePackage{caption}
\captionsetup[table]{labelfont={sc},textfont={sl},justification=RaggedRight}
\captionsetup[figure]{labelfont={sc},textfont={sl},justification=RaggedRight}
% \captionsetup[table]{labelfont={sc},textfont={sl},justification=RaggedRight,singlelinecheck=false}
% \captionsetup[figure]{labelfont={sc},textfont={sl},justification=RaggedRight,singlelinecheck=false}

% Front matter.
\setcounter{tocdepth}{2} %% Show subsections in TOC
\usepackage[titles]{tocloft}
\usepackage[titletoc]{appendix}
\renewcommand{\cftsecleader}{\cftdotfill{\cftdotsep}}
\renewcommand{\cftchapfont}{\normalsize \scshape}
\renewcommand\listfigurename{Listing of figures}
\renewcommand\listtablename{Listing of tables}

%%%%%%%%%%%%%%%%
%% Page style %%
%%%%%%%%%%%%%%%%

%% Hacky way of bringing the latest git commit
%% into here; but hey, it works! makes it easy
%% to know which version of the thesis the feedback came from.
\ifPHD@isdraft
\input{dist/version.tex}
\fi
% \@ifundefined{\PHD@latestcommit}{\def\PHD@latestcommit{000000}}{}

% Commands like chapter/section/etc call \thispagestyle{plain}, effectively
% not using whatever page style is selected; we redefine plain to
% our likings, then.
\fancypagestyle{plain}{%
  \fancyhf{} % clear all header and footer fields
  \renewcommand{\headrulewidth}{0pt}
  \renewcommand{\footrulewidth}{0pt}
}

%% Adds the uppercase title of the current chapter to
%% the top of the page, centered. Numbers go alternating
%% left to right or centered, depending on oneside or twoside options.
\pagestyle{fancy}
\renewcommand{\chaptermark}[1]{\markboth{\MakeUppercase{#1}}{}}
\renewcommand{\sectionmark}[1]{\markright{\thesection\ \MakeUppercase{#1}}{}}
\renewcommand{\headrulewidth}{0pt}
\fancyhead{}
\fancyfoot{}
\fancyhead[RO, LE]{\thepage}
\fancyhead[CO]{\leftmark}
\fancyhead[CE]{\rightmark}

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%%  Title Page  %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

\let\@promotor\@empty
\newcommand{\promotor}[1]{\gdef\@promotor{#1}}

\let\@copromotor\@empty
\newcommand{\copromotor}[1]{\gdef\@copromotor{#1}}

\let\@NWOproject\@empty
\newcommand{\NWOproject}[1]{\gdef\@NWOproject{#1}}

\let\@NWOgrantnumber\@empty
\newcommand{\NWOgrantnumber}[1]{\gdef\@NWOgrantnumber{#1}}

\let\@defensedate\@empty
\newcommand{\defensedate}[1]{\gdef\@defensedate{#1}}

\let\@authorbirthdate\@empty
\newcommand{\authorbirthdate}[1]{\gdef\@authorbirthdate{#1}}

\let\@authorbirthplace\@empty
\newcommand{\authorbirthplace}[1]{\gdef\@authorbirthplace{#1}}

\let\@titleDUTCH\@empty
\newcommand{\titleDUTCH}[1]{\gdef\@titleDUTCH{#1}}

\ifPHD@ismsccover
\renewcommand{\maketitle}{
%%%%%%%%%%%%%
%% Custom page numbering to hack the crap out
%% of duplicate-destinations
%% seen in: https://tex.stackexchange.com/questions/18924/pdftex-warning-ext4-destination-with-the-same-identifier-nam-epage-1-has
\pagenumbering{Alph}
%% Custom title page geometry
\newgeometry{left=0.17\paperwidth,right=0.17\paperwidth,bindingoffset=6mm}
\thispagestyle{empty}
\begingroup
% \fontsize{9pt}{7pt}\selectfont
\begin{center}
%%%%%%%%%%%%%
%% Headings
  \includegraphics[width=.14\paperwidth]{img/logo.pdf}

  \vspace*{.5cm}

  \begin{Large}
  Utrecht University
  \end{Large}

  \begin{small}
  Department of Computing Sciences
  \end{small}

  \vfill

  \begin{LARGE}
  {\bf \@title}
  \end{LARGE}

  \vspace*{0.04\paperheight} % 1cm on b5
  Master Thesis defended on \@defensedate, by:

  \

  {\Large \@author}


  \vfill

  Supervised by:

  \@promotor

  \

  \ifx\@copromotor\empty
  \else
    Cosupervised by:

    \@copromotor
  \fi
\end{center}
\endgroup
%%%%%%%%%%%%
%% Restore our previous geometry
\restoregeometry
}
\else
\renewcommand{\maketitle}{
%%%%%%%%%%%%%
%% Custom page numbering to hack the crap out
%% of duplicate-destinations
%% seen in: https://tex.stackexchange.com/questions/18924/pdftex-warning-ext4-destination-with-the-same-identifier-nam-epage-1-has
\pagenumbering{Alph}
%% \hypersetup{pageanchor=false}
%% Custom title page geometry
\newgeometry{left=0.17\paperwidth,right=0.17\paperwidth,bindingoffset=6mm}
\thispagestyle{empty}
\begingroup
% \fontsize{9pt}{7pt}\selectfont
\begin{center}
%%%%%%%%%%%%%
%% Headings
  \vspace*{0.08\paperheight} %
  \begin{LARGE}
  {\bf \@title}
  \end{LARGE}
  \vspace*{0.08\paperheight} %

  \begin{Large}
  \@titleDUTCH
  \vspace{0.008\paperheight} %

  (met een samenvatting in het Nederlands)
  \end{Large}

  \vspace*{0.15\paperheight} %

  Proefschrift

  \

  \begin{tabular}{p{0.83\textwidth}}
  ter verkrijging van de graad van doctor aan de Universiteit Utrecht op
  gezag van de rector magnificus, prof. dr. H.R.B.M. Kummeling, ingevolge
  het besluit van het college voor promoties in het openbaar te verdedigen
  op \@defensedate
  % op maandag 23 april 2018 des ochtends te 10.30 uur
  \end{tabular}

  door

  \

  {\Large \@author}

  geboren op \@authorbirthdate \\
  te \@authorbirthplace
\end{center}
\newpage
\thispagestyle{empty}
\noindent
\begin{tabular}{ll}
Promotor: & \@promotor \\
Copromotor: & \@copromotor
\end{tabular}

\vspace{0.588\paperheight}

\noindent Dit proefschrift werd (mede) mogelijk gemaakt met financiële
steun van de \\
Nederlandse Organisatie voor Wetenschappelijk Onderzoek (NWO), \\
project \@NWOproject{} (\@NWOgrantnumber).
\endgroup
%%%%%%%%%%%%
%% Restore our previous geometry
\restoregeometry
}
\fi % PHD@ismsccover

%% End of title page

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%% sectsty conf %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

%% Latex L-System for drawing seaweeds
\usetikzlibrary{lindenmayersystems}
\pgfdeclarelindenmayersystem{FractalPlant}{
  \rule{X -> F-[[X]+X]+F[+FX]-X}
  \rule{F -> FF}}
% \usetikzlibrary{shadings}

%% necessary for the fancy text in white with black contour
\RequirePackage{contour}
\RequirePackage{calc}

% Draws a seaweed, receives the amound of iterations desired
\newcommand{\drawseaweed}[2]{
\resizebox{4cm}{4cm}{%
\ifPHD@isdrawseaweed
\begin{tikzpicture}
\draw [color=#1, rotate=65 ]
  [l-system={FractalPlant , axiom=X , order=#2 , step=7pt/#2 , angle=22.5 }]
  lindenmayer system;
\end{tikzpicture}
\else
\begin{tikzpicture}
  \draw [color = white] (0,0) rectangle (1,1);
\end{tikzpicture}
\fi
}
}


%% Our appendix has to stop the seaweed madness
\renewcommand\appendix{\par
\setcounter{chapter}{0}%
\setcounter{section}{0}%
\gdef\@chapapp{\appendixname}%
\gdef\thechapter{\@Alph\c@chapter}%
\PHD@isdrawseaweedfalse}

\usepackage[strict]{changepage}

\titleformat%
%Command to change
{\chapter}%
%Style to use
[block]%
% Format
{\bfseries\Large}%
% The chapter label
% {\Huge\color{gray}\thechapter}%
{
\begin{adjustwidth}{}{-5em}
\begin{flushright}
\begin{tikzpicture}
  \draw (1cm, 1cm) node { \drawseaweed{black}{\c@chapter} };
  \draw node {%
    \contourlength{.4mm}
    \fontsize{105}{130}\selectfont{\contour[64]{white}{%
       \protect\color{black}\thechapter}}
  };
\end{tikzpicture}
\end{flushright}
\end{adjustwidth}
}%
% Separation between label and title body
{0em}%
% Before command
{\Huge\scshape}%

\titlespacing*{\chapter}{0em}{-2em}{1em}

%%%%%%%%%%%%%%%%%%%%%%
%% General Packages %%
%%%%%%%%%%%%%%%%%%%%%%

%% Indexing
% \usepackage{imakeidx}
% \makeindex[options=-s tex/latex/index_style.ist]
% \newcommand{\withindex}[1]{#1\index{#1}}

\usepackage{alltt}
\usepackage{microtype}
\usepackage{booktabs}
\usepackage{multirow}
\usepackage{subfig}

%% Refine reference format to include parenthesis
%% Taken from: https://tex.stackexchange.com/questions/75014/is-it-possible-to-make-a-reference-to-a-subfigure-to-appear-figure-2a-with-cle
\captionsetup[subfigure]{ subrefformat=simple %
                        , labelformat=simple %
                        , listofformat=subsimple}
\renewcommand\thesubfigure{(\textsc{\alph{subfigure}})}


%% Hacks for preventing orphan lines
%% https://tex.stackexchange.com/questions/4152/how-do-i-prevent-widow-orphan-lines
\clubpenalty=10000
\widowpenalty=10000
\displaywidowpenalty=10000

% hyperref MUST be loaded first. Check section 14.1 of cleveref manual.
\usepackage[pdfpagelabels,plainpages=false]{hyperref}
\usepackage{cleveref}

%% Recommented to give more professionally-looking tables.
\renewcommand{\arraystretch}{1.3}

%% number up to subsubsections
\setcounter{secnumdepth}{3}

%% Theorems and Definitions
\usepackage{amsthm}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]

\theoremstyle{plain}
\newtheorem{lemma}{Lemma}[section]
\newtheorem{theorem}{Theorem}[section]


%% Paragraph formatting

\setlength{\parskip}{0.5em}
%% These values work; but we get VERY weird erros with other combinations
%% \linespread{1.05}
%% \setlength{\parskip}{1em}

\usepackage[numbers,square]{natbib}

\usepackage[shortlabels]{enumitem}
\setlist[enumerate]{label=\alph*)}

\ifPHD@isdraft
\usepackage{layouts}
\newcommand{\displaymeasurespage}{%
\newpage
\thispagestyle{empty}
\begin{center}
\begin{tabular}{rl}
  \texttt{\textbackslash{}textwitdh} & \printinunitsof{cm}\prntlen{\textwidth} \\
  \texttt{\textbackslash{}paperwidth} & \printinunitsof{cm}\prntlen{\paperwidth} \\
  \texttt{\textbackslash{}paperheigth} & \printinunitsof{cm}\prntlen{\paperheight} \\
\end{tabular}
\end{center}}
\usepackage[displaymath,mathlines]{lineno}
\linenumbers
\else
\newcommand{\displaymeasurespage}{}
\fi
