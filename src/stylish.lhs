%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%% Haskell Styling
%%
%% TODO: Figure out spacing!

%% Colors (from duo-tone light syntax)
\definecolor{hsblack}{RGB}{45,32,3}
\definecolor{hsgold1}{RGB}{179,169,149}
\definecolor{hsgold2}{RGB}{177,149,90}
\definecolor{hsgold3}{RGB}{190,106,13}%{192,96,4}%{132,97,19}
\definecolor{hsblue1}{RGB}{173,176,182}
\definecolor{hsblue2}{RGB}{113,142,205}
\definecolor{hsblue3}{RGB}{0,33,132}
\definecolor{hsblue4}{RGB}{97,108,132}
\definecolor{hsblue5}{RGB}{34,50,68}
\definecolor{hsred2}{RGB}{191,121,103}
\definecolor{hsred3}{RGB}{171,72,46}

%% LaTeX Kerning nastiness. By using curly braces to delimit color group,
%% it breaks spacing. The following seems to work:
%%
%% https://tex.stackexchange.com/questions/85033/colored-symbols/85035#85035
%%
\newcommand*{\mathcolor}{}
\def\mathcolor#1#{\mathcoloraux{#1}}
\newcommand*{\mathcoloraux}[3]{%
  \protect\leavevmode
  \begingroup
    \color#1{#2}#3%
  \endgroup
}

\newcommand{\HSKeyword}[1]{\mathcolor{hsgold3}{\textbf{#1}}}
\newcommand{\HSNumeral}[1]{\mathcolor{hsred3}{#1}}
\newcommand{\HSChar}[1]{\mathcolor{hsred2}{#1}}
\newcommand{\HSString}[1]{\mathcolor{hsred2}{#1}}
\newcommand{\HSSpecial}[1]{\mathcolor{hsblue4}{#1}}
\newcommand{\HSSym}[1]{\mathcolor{hsblue4}{\textit{\ensuremath{#1}}}}
\newcommand{\HSCon}[1]{\mathcolor{hsblue3}{\mathit{\ensuremath{#1}}}}
\newcommand{\HSVar}[1]{\mathcolor{hsblue5}{\mathit{\ensuremath{#1}}}}
\newcommand{\HSVarNI}[1]{\mathcolor{hsblue5}{\ensuremath{#1}}}
\newcommand{\HSConNI}[1]{\mathcolor{hsblue3}{\ensuremath{#1}}}
\newcommand{\HSComment}[1]{\mathcolor{hsgold2}{\textit{#1}}}


%subst keyword a = "\HSKeyword{" a "}"
%subst conid a   = "\HSCon{" a "}"
%subst varid a   = "\HSVar{" a "}"
%subst varsym a  = "\HSSym{" a "}" 
%subst consym a  = "\HSSym{" a "}"
%subst numeral a = "\HSNumeral{" a "}"
%subst char a    = "\HSChar{''" a "''}"
%subst string a  = "\HSString{``" a "\char34 }"
%subst special a = "\HSSpecial{" a "}"
%subst comment a = "\HSComment{ -\! -" a "}"

%%% lhs2TeX parser does not recognize '*' 
%%% in kind annotations, it thinks it is a multiplication.
%format Star       = "\HSCon{*}"

%format ::         = "\mathbin{\HSSym{:\!:}}"
%format :          = "\mathbin{\HSCon{:}}"
%format nil        = "\HSCon{[]}"

%format family     = "\HSKeyword{family}"
%format pattern    = "\HSKeyword{pattern}"
%format _          = "\mathbin{\HSSym{\anonymous}} "
%format ->         = "\mathbin{\HSSym{\to}} "
%format <-         = "\mathbin{\HSSym{\leftarrow}} "
%format =>         = "\mathbin{\HSSym{\Rightarrow}} "
%format \          = "\HSSym{\lambda} "
%format |          = "\mathbin{\HSSym{\mid}} "
%format {          = "\HSSym{\{\mskip1.5mu} "
%format }          = "\HSSym{\mskip1.5mu\}}"
%format [          = "\HSSym{[\mskip1.5mu} "
%format ]          = "\HSSym{\mskip1.5mu]}"
%format =          = "\mathrel{\HSSym{=}}"
%format ..         = "\HSSym{\mathinner{\ldotp\ldotp}}"
%format ~          = "\HSSym{\mathrel{\sim}}"
%format @          = "\HSSym{\mathord{@}}"
%format .          = "\mathbin{\HSSym{\circ}}"
%format !!         = "\mathbin{\HSSym{!!}}"
%format ^          = "\mathbin{\HSSym{\uparrow}}"
%format ^^         = "\mathbin{\HSSym{\uparrow\uparrow}}"
%format **         = "\mathbin{\HSSym{**}}"
%format /          = "\mathbin{\HSSym{/}}"
%format `quot`     = "\mathbin{\HSSym{`quot`}}"
%format `rem`      = "\mathbin{\HSSym{`rem`}}"
%format `div`      = "\mathbin{\HSSym{`div`}}"
%format `mod`      = "\mathbin{\HSSym{`mod`}}"
%format :%         = "\mathbin{\HSSym{:\%}}"
%format %          = "\mathbin{\HSSym{\%}}"
%format ++         = "\HSSym{\plus} "
%format ==         = "\HSSym{\equiv} "
%format /=         = "\HSSym{\not\equiv} "
%format <=         = "\HSSym{\leq} "
%format >=         = "\HSSym{\geq} "
%format `elem`     = "\HSSym{\in} "
%format `notElem`  = "\HSSym{\notin} "
%format &&         = "\HSSym{\mathrel{\wedge}}"
%format ||         = "\HSSym{\mathrel{\vee}}"
%format >>         = "\HSSym{\sequ} "
%format >>=        = "\HSSym{\bind} "
%format =<<        = "\HSSym{\rbind} "
%format $          = "\mathbin{\HSSym{\$}}"
%format `seq`      = "\mathbin{\HSSym{`seq`}}"
%format !          = "\mathbin{\HSSym{!}}"
%format //         = "\mathbin{\HSSym{//}}"
%format undefined  = "\HSSym{\bot} "
%format not	   = "\HSSym{\neg} "
%format >>>        = "\HSSym{\ggg}"
%format >=>        = "\HSSym{> \! = \! >}"

