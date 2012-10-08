%%
%% This is file `jfp.cls'
%%
%% CUP Journal of Functional Programming document class
%% Copyright 2001 Cambridge University Press
%%
%% by Mark A. Reed
%%   based on JFP.STY v1.24.
%%
%% Incorporating parts of authordate.sty
%%    by David Rhead, Cripps Computing Centre (Feb 1990).
%%
%% Bugs (in the case of unchanged files) should be reported to
%% texline@cambridge.org
%%
%% This software may only be used in the preparation of journal articles
%% or books or parts of books to be published by Cambridge University Press.
%% Any other use constitutes an infringement of copyright.
%%
%% \CharacterTable
%%  {Upper-case    \A\B\C\D\E\F\G\H\I\J\K\L\M\N\O\P\Q\R\S\T\U\V\W\X\Y\Z
%%   Lower-case    \a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z
%%   Digits        \0\1\2\3\4\5\6\7\8\9
%%   Exclamation   \!     Double quote  \"     Hash (number) \#
%%   Dollar        \$     Percent       \%     Ampersand     \&
%%   Acute accent  \'     Left paren    \(     Right paren   \)
%%   Asterisk      \*     Plus          \+     Comma         \,
%%   Minus         \-     Point         \.     Solidus       \/
%%   Colon         \:     Semicolon     \;     Less than     \<
%%   Equals        \=     Greater than  \>     Question mark \?
%%   Commercial at \@     Left bracket  \[     Backslash     \\
%%   Right bracket \]     Circumflex    \^     Underscore    \_
%%   Grave accent  \`     Left brace    \{     Vertical bar  \|
%%   Right brace   \}     Tilde         \~}
%%

\NeedsTeXFormat{LaTeX2e}[1997/12/01]
\ProvidesClass{jfp}[2001/09/27 v1.02 Journal of Functional Programming
  ^^Jdocument class]

\newif\ifprodtf
\newif\ifonepage\global\onepagefalse%
\newif\ifonline
\onlinefalse
%
\newif\ifcompmod\global\compmodfalse
%
\newif\ifincremental\incrementalfalse
%%
\newif\ifindex
\newif\ifdraft
\newif\ifnoquery
\newif\ifbookreview
\newif\ifsptitle
%
\newif\ifsplissue
\global\splissuefalse
%
\newif\ifprinter
\newdimen\draftrule
\newdimen\trimrule
\global\draftrule0pt
\trimrule.1pt
%
\newdimen\trimwidth
\newdimen\trimheight
\newdimen\typewidth
\newdimen\typeheight

\newdimen\tempdimen
\newdimen\normaltextheight
\newskip\normalbaselineskip
\newdimen\blindfoliodrop
\newif\ifprinter
\global\printerfalse
%%
\DeclareOption{compmod}{\compmodtrue}
%
\DeclareOption{splissue}{\splissuetrue}
%
%
\DeclareOption{incremental}{\incrementaltrue}
\DeclareOption{index}{\indextrue}
\DeclareOption{bookreview}{\bookreviewtrue}
\DeclareOption{noquery}{\noquerytrue}
\DeclareOption{oneside}{\relax}
\DeclareOption{twoside}{\@twosidetrue \@mparswitchtrue}
\DeclareOption{draft}{\draftrule.5pt\setlength\overfullrule{5\p@}}
\DeclareOption{final}{\setlength\overfullrule{\z@}}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{onepage}{\global\onepagetrue}
\DeclareOption{twocolumn}{\relax}
\DeclareOption{titlepage}{\relax}
\DeclareOption{notitlepage}{\relax}
\DeclareOption{leqno}{\relax}
\DeclareOption{fleqn}{\relax}
\DeclareOption{prodtf}{\prodtftrue}
\DeclareOption{sptitle}{\sptitletrue}
\DeclareOption{printer}{\printertrue}
\DeclareOption{online}{\onlinetrue}
%
\ExecuteOptions{twoside,final,onecolumn}
\ProcessOptions\relax

\newif\ifCUPmtlplainloaded
%% \ifprodtf
%%   \CUPmtlplainloadedtrue
%%   \RequirePackage{CUPTimes,jfp2esym}
%% %  \RequirePackage{Times,jfp2esym} %%% TB
%% \fi
%%%%%%%%%%%%%%%%
%
\def\trkdefault{trk}% All trk
\DeclareRobustCommand\trkshape
        {\not@math@alphabet\trkshape\mathrm
         \fontshape\trkdefault\selectfont}
%
\def\spchapterfont{\fontsize{18}{21}\selectfont}%\trkshape}
\def\subtitlefont{\normalfont\fontsize{12}{14}\selectfont\itshape}%
%
\def\splissuefont{\fontsize{12}{14}\itshape\selectfont}%\trkshape}
%
\DeclareFontFamily{OT1}{mtr}{}
\DeclareFontShape{OT1}{mtr}{m}{n}{<->mtr10}{}
\DeclareFontShape{OT1}{mtr}{m}{trk}{<->mtr10[track+140]}{}
\DeclareFontShape{OT1}{mtr}{m}{sl}{<->mtsl10}{}
\DeclareFontShape{OT1}{mtr}{m}{it}{<->mtti10}{}
\DeclareFontShape{OT1}{mtr}{m}{sc}{<->mtcsc10}{}
%
% Warning: please note that the upright shape below is
%          used for the \pounds symbol of LaTeX. So this
%          font definition shouldn't be removed.
%
\DeclareFontShape{OT1}{mtr}{m}{ui}{<->mtu10}{}
%
%%%%%%% bold series
\DeclareFontShape{OT1}{mtr}{b}{n}{<->sub * cmr/b/n}{}
%
%%%%%%%% bold extended series
\DeclareFontShape{OT1}{mtr}{bx}{n}{<->mtbx10}{}
\DeclareFontShape{OT1}{mtr}{bx}{sl}{<->mtbxsl10}{}
\DeclareFontShape{OT1}{mtr}{bx}{it}{<->mtbxti10}{}
%
% Again this is necessary for a correct \pounds symbol in
% the cmr fonts Hopefully the dc/ec font layout will take
% over soon.
%
\DeclareFontShape{OT1}{mtr}{bx}{ui}{<->ssub * mtr/m/ui}{}
%
%%%%% For mathfrak ... updated on 26th of April 2006
%
\DeclareFontFamily{U}{eufa}{}%
\DeclareFontShape{U}{eufa}{m}{n}{<-6>eufm5<6-8>eufm7<8->eufm10}{}%
\DeclareFontShape{U}{eufa}{b}{n}{<-6>eufb5<6-8>eufb7<8->eufb10}{}%
%
%%\newcommand{\mathfrak}[1]{{\protect\pmathfrak#1}}
%%\newcommand{\pmathfrak}{\@fontswitch{\relax}{\mfraknew}}
\DeclareMathAlphabet\mfraknew{U}{eufa}{m}{n}
\SetMathAlphabet\mfraknew{normal}{U}{eufa}{m}{n}
\SetMathAlphabet\mfraknew{bold}{U}{eufa}{b}{n}
%%%%

%%%%%%%%%%%%%%%%
\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}

\renewcommand\normalsize{%
\ifbookreview
\@setfontsize\small\@ixpt{11}%
\else
\@setfontsize\normalsize\@xpt{13}%
\fi
  \abovedisplayskip 6.5\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 3\p@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \let\@listi\@listI}

\normalsize

\newcommand\small{%
 \@setfontsize\small\@ixpt{11}%
  \abovedisplayskip 6\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 3\p@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \def\@listi{\leftmargin\leftmargini
    \topsep 6\p@ \@plus 1\p@ \@minus 1\p@
    \parsep \z@ \itemsep \parsep}%
}

\newcommand\footnotesize{%
  \@setfontsize\footnotesize\@ixpt\@xpt
  \abovedisplayskip 5\p@ \@plus 1\p@ \@minus 1\p@
  \belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip \z@ \@plus 1\p@
  \belowdisplayshortskip \abovedisplayshortskip
  \def\@listi{\leftmargin\leftmargini
    \topsep 4.5\p@ \@plus 1\p@ \@minus 1\p@
    \parsep \z@ \itemsep \parsep}%
}

\newcommand\scriptsize{\@setfontsize\scriptsize\@viiipt\@ixpt}
\newcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
\newcommand\large{\@setfontsize\large\@xiipt{14}}
\newcommand\Large{\@setfontsize\Large\@xvpt{18}}
\ifprodtf
  \newcommand\LARGE{\@setfontsize\LARGE{19}{21}}%
\else
  \newcommand\LARGE{\@setfontsize\LARGE{18}{21}}%
\fi
\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}
%
\def\sluglinefont{\fontsize{7.5}{10}\selectfont}
%
\newcommand\affilsize{\@setfontsize\affilsize\@viiipt\@xpt}
\newcommand\onlineaffilsize{\@setfontsize\affilsize\@viipt\@ixpt}
\let\authorsize\normalsize

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*\mit{\@fontswitch\relax\mathnormal}

  \setlength\topmargin{11mm}
\setlength\trimheight{247mm}
\setlength\trimwidth{174mm}
%
\setlength\typeheight{50.5pc}
\setlength\typewidth{30pc}

\setlength\marginparwidth{2.0cm}
\setlength\marginparsep{10\p@}

\setlength\headheight{6\p@}
\setlength\headsep{18\p@}
\setlength\topskip{6\p@}
\setlength\footskip{26\p@}

\setlength\textheight{48.5pc}
\addtolength\textheight{-8.8pt}
\addtolength\textheight{\topskip}
\setlength\normaltextheight{\textheight}

\setlength\textwidth{30pc}
\setlength\columnsep{10\p@}
\setlength\columnseprule{\z@}

\setlength\oddsidemargin{21mm}%5pc}
\setlength\evensidemargin\trimwidth
\addtolength\evensidemargin{-\textwidth}
\addtolength\evensidemargin{-\oddsidemargin}

\setlength\footnotesep{\z@}
\setlength{\skip\footins}{19.5\p@ \@plus 12\p@ \@minus 1\p@}

\setlength\floatsep{13\p@ \@plus 6.5\p@ \@minus 1\p@}
\setlength\textfloatsep{15\p@ \@plus 4.5\p@ \@minus 3\p@}
\setlength\intextsep{13\p@ \@plus 6.5\p@ \@minus 2\p@}
\setlength\dblfloatsep{13\p@ \@plus 6.5\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{15\p@ \@plus 4.5\p@ \@minus 3\p@}
\setlength\@fptop{\z@ \@plus 0fil}
\setlength\@fpsep{13\p@ \@plus 0fil}
\setlength\@fpbot{\z@ \@plus 3fil}
\setlength\@dblfptop{\z@ \@plus 0fil}
\setlength\@dblfpsep{13\p@ \@plus 0fil}
\setlength\@dblfpbot{\z@ \@plus 3fil}
\setlength\marginparpush{5\p@}

\setlength\parskip{\z@}% \@plus .3\p@}
\setlength\parindent{10pt}
\setlength\partopsep{\z@ \@plus 1\p@}
\@lowpenalty   51
\@medpenalty  151
\@highpenalty 301
\@beginparpenalty -\@lowpenalty
\@endparpenalty -\@lowpenalty
\@itempenalty -\@lowpenalty
\clubpenalty\@M%z@
\widowpenalty\@M
\hyphenpenalty8000

%
\def\cleardoublepage{\clearpage\if@twoside \ifodd\c@page\else
    \hbox{}\thispagestyle{empty}\newpage\if@twocolumn\hbox{}\newpage\fi\fi\fi}
%
\newcommand\partname{Part}
\newcommand\part{\par\addvspace{4ex}\@afterindentfalse \secdef\@part\@spart}

\def\@part[#1]#2{%
  \ifnum \c@secnumdepth >\m@ne
    \refstepcounter{part}%
    \addcontentsline{toc}{part}{\partname\ \thepart: #1}%
  \else
    \addcontentsline{toc}{part}{#1}%
  \fi
  {\parindent \z@ \centering
   \ifnum \c@secnumdepth >\m@ne
     \normalfont\large\rmfamily \MakeUppercase{\partname}\ %
     \ifcase\thepart \or ONE \or TWO \or THREE \or FOUR \or FIVE
     \or SIX \or SEVEN \or EIGHT \or NINE \or TEN \else \fi
     \par \nobreak
   \fi
   \normalfont\LARGE\rmfamily #2 \markboth{}{}\par}%
   \nobreak \vskip 3ex \@afterheading
}

\def\@spart#1{%
  {\parindent \z@ \centering\normalfont\LARGE\rmfamily #1\par}%
  \nobreak \vskip 3ex \@afterheading
}

\newcommand\section{%
  \@startsection {section}{1}{\z@}%
    {-19.5\p@ \@plus -6.5\p@ \@minus -3.25\p@}%
    {6.5\p@ \@plus \z@ \@minus 1\p@}
    {\normalfont\normalsize\bfseries\centering}%
}

\newcommand\subsection{%
  \@startsection{subsection}{2}{\z@}
    {-19.5\p@ \@plus -3.25\p@ \@minus -3.25\p@}
    {6.5\p@ \@plus \z@ \@minus 1\p@}
    {\normalfont\normalsize\bfseries\itshape\centering}%
}

\newcommand\subsubsection{%
  \@startsection{subsubsection}{3}{\z@}
    {-19.5\p@ \@plus -3.25\p@ \@minus -3.25\p@}
    {6.5\p@ \@plus \z@ \@minus 1\p@}
    {\normalfont\normalsize\itshape\centering}%
}

\newcommand\paragraph{%
  \@startsection{paragraph}{4}{\z@}
    {-13\p@ \@plus -1.5\p@ \@minus -1.5\p@}
    {-0.5em}
    {\normalfont\normalsize\bfseries\raggedright}%
}

\newcommand\subparagraph{%
  \@startsection{subparagraph}{4}{\parindent}
    {-13\p@ \@plus -3.25\p@ \@minus -3.25\p@}
    {-0.5em}
    {\normalfont\normalsize\rmfamily\raggedright}%
}

\def\@seccntformat#1{\csname the#1\endcsname\hskip5pt}% 

\newcommand\appendixname{Appendix}

\newcommand\appendix{\par
  \@addtoreset{equation}{section}%
  \@addtoreset{figure}{section}%
  \@addtoreset{table}{section}%
  \setcounter{section}\z@
  \renewcommand\thesection{\@Alph\c@section}%
  \renewcommand\theequation{\thesection\,\@arabic\c@equation}%
  \renewcommand\thefigure{\thesection\,\@arabic\c@figure}%
  \renewcommand\thetable{\thesection\,\@arabic\c@table}%
}

\setcounter{secnumdepth}{3}

\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]
\newcounter{subparagraph}[paragraph]
\renewcommand\thepart          {\@arabic\c@part}
\renewcommand\thesection       {\@arabic\c@section}
\renewcommand\thesubsection    {\thesection.\@arabic\c@subsection}
\renewcommand\thesubsubsection {\thesubsection.\@arabic\c@subsubsection}
\renewcommand\theparagraph     {\thesubsubsection.\@arabic\c@paragraph}
\renewcommand\thesubparagraph  {\theparagraph.\@arabic\c@subparagraph}

\newskip\@leftskip  \@leftskip=\z@

\setlength\leftmargini   {13pt}
\setlength\leftmarginii  {15.2pt}
\setlength\leftmarginiii {1.5em}
\setlength\leftmarginiv  {1.5em}
\setlength\leftmarginv   {1em}
\setlength\leftmarginvi  {1em}
\setlength\leftmargin    {\leftmargini}
\setlength\labelsep      {5\p@}
\setlength\labelwidth    {\leftmargini}
\addtolength\labelwidth  {-\labelsep}

\newcommand\makeRLlabel[1]{\rlap{#1}\hss}
\newcommand\makeRRlabel[1]{\hss\llap{#1}}

\def\@listI{\leftmargin\leftmargini\advance\leftmargin11.5pt
  \parsep \z@ \topsep 6.5\p@ \@plus 3\p@ \@minus 3\p@
  \itemsep \z@ \@plus 1\p@ \@minus 1\p@
  \let\makelabel\makeRLlabel}

\def\@listii{\leftmargin\leftmarginii
  \labelwidth\leftmarginii
  \advance\labelwidth-\labelsep
  \topsep 3\p@ \@plus 1\p@ \@minus 1\p@
  \parsep \z@ \itemsep \parsep
  \let\makelabel\makeRLlabel}

\def\@listiii{\leftmargin\leftmarginiii
  \labelwidth\leftmarginiii
  \advance\labelwidth-\labelsep
  \topsep 3\p@ \@plus 1\p@ \@minus 1\p@
  \parsep \z@ \partopsep \z@
  \itemsep \topsep
  \let\makelabel\makeRLlabel}

\def\@listiv{\leftmargin\leftmarginiv
  \labelwidth\leftmarginiv
  \advance\labelwidth-\labelsep
  \let\makelabel\makeRLlabel}

\def\@listv{\leftmargin\leftmarginv
  \labelwidth\leftmarginv
  \advance\labelwidth-\labelsep
  \let\makelabel\makeRLlabel}

\def\@listvi{\leftmargin\leftmarginvi
  \labelwidth\leftmarginvi
  \advance\labelwidth-\labelsep
  \let\makelabel\makeRLlabel}

\let\@listi\@listI
\@listi

\def\itemize{% FROM LATEX.LTX
  \ifnum \@itemdepth >\thr@@ \@toodeep\else
     \advance\@itemdepth \@ne
     \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
     \expandafter
     \list
       \csname\@itemitem\endcsname
       {\let\makelabel\makeRRlabel\advance\itemindent0pt\advance\leftmargin.5pt}%
  \fi
}

\newif\ifhyphen\global\hyphenfalse

\newcommand\labelitemi{\ifhyphen \normalfont\bfseries ---\else
$\m@th\bullet$\fi}

%\newcommand\labelitemi{$\m@th\bullet$}
\newcommand\labelitemii{\normalfont\bfseries ---}
\newcommand\labelitemiii{\normalfont\bfseries --}
\newcommand\labelitemiv{$\m@th\cdot$}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  unnumlist %%%%%%%%%%%%%%%%%%%%%%%%%%%%% TB
%
\def\unnumlistfont{\fontsize{10}{13}\selectfont}

\newenvironment{unnumlist}{\par%
    \unnumlistfont%
    \list{}{%
    \topsep6pt plus2pt
    \itemindent-10pt
    \leftmargin10pt
    \parsep0pt
    \itemsep0pt
    \partopsep0pt}
    \def\makelable##1{##1}%
}{%
    \endlist%
}%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  unnumlist %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\enumerate{% FROM LATEX.LTX
  \ifnum \@enumdepth >\thr@@ \@toodeep\else
    \advance\@enumdepth \@ne
    \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
  \fi
  \@ifnextchar [{\@enumeratetwo}{\@enumerateone}%
}

\def\@enumerateone{%
  \expandafter
   \list
     \csname label\@enumctr\endcsname
     {\usecounter{\@enumctr}%
      \let\makelabel\makeRRlabel}%
}

\def\@enumeratetwo[#1]{%
  \expandafter
  \list
    \csname label\@enumctr\endcsname
    {\usecounter{\@enumctr}%
     \settowidth\labelwidth{\normalfont\rmfamily #1}%
    \itemindent0pt\leftmargin\labelwidth\advance\leftmargin\labelsep\advance\leftmargin13pt
     \let\makelabel\makeRRlabel}%
}

\newcommand\labelenumi  {{\normalfont\rmfamily\theenumi.}}
\newcommand\labelenumii {{\normalfont\rmfamily(\theenumii)}}
\newcommand\labelenumiii{{\normalfont\rmfamily\theenumiii}}
\newcommand\labelenumiv {{\normalfont\rmfamily\theenumiv}}

\renewcommand\theenumi{\@arabic\c@enumi}
\renewcommand\theenumii{\@alph\c@enumii}
\renewcommand\theenumiii{\@roman\c@enumiii}
\renewcommand\theenumiv{\@Alph\c@enumiv}

\renewcommand\p@enumii{\theenumi}
\renewcommand\p@enumiii{\theenumi(\theenumii)}
\renewcommand\p@enumiv{\p@enumiii\theenumiii}

\newcommand*\descriptionlabel[1]{\hspace\labelsep \normalfont\bfseries #1}

\newenvironment{description}
  {\list{}{\leftmargin 1em \labelwidth\z@ \itemindent-\leftmargin
   \let\makelabel\descriptionlabel}}
  {\endlist}

\newenvironment{verse}
  {\let\\=\@centercr
   \list{}{\itemsep\z@
   \itemindent -2.5em%
   \listparindent \itemindent
   \rightmargin\leftmargin
   \advance\leftmargin 2.5em}\item[]}
  {\endlist}

\newenvironment{extract}  %quotation
  {\list{}{\vskip6pt\listparindent\parindent
   \topsep6pt\itemindent\listparindent
   \leftmargin\z@ \rightmargin\leftmargin
   \parsep \z@ \@plus 1\p@}\item[]%
   \normalfont\small\rmfamily}
  {\endlist}


\newenvironment{quote}  %quotation
  {\par\vskip5pt\itshape\leftskip0pt plus1fill\rightskip0pt plus 0fill}
  {\par}

\newenvironment{qtsource}  %quotation source
  {\par\leftskip0pt plus1fill\rightskip0pt plus 0fill}
  {\par}

\def\quotespace{\vspace*{6.5pt}}

\newenvironment{letter}  %quotation
  {\list{}{\listparindent\z@
   \topsep6pt\itemindent\listparindent
   \leftmargin24pt \rightmargin\z@
   \parsep \z@ \@plus 1\p@}\item[]%
   \normalfont\itshape}
  {\endlist}


\newif\ifrembrks
\newcommand\removebrackets{\rembrkstrue}

\def\@begintheorem#1#2{% FROM LATEX.LTX
  \normalfont\rmfamily
  \trivlist
    \item[\hskip \labelsep{\normalfont\itshape #1\ #2}]%
    \item[]%
}

\def\@opargbegintheorem#1#2#3{% FROM LATEX.LTX
  \normalfont\rmfamily
  \trivlist
    \item[\hskip \labelsep{\normalfont\itshape #1\ #2\ %
    \ifrembrks #3\/\global\rembrksfalse\else {\upshape(}#3\/{\upshape)}\fi}]%
    \item[]%
}

\newsavebox{\proofsavebox}


%% \newtheorem{lemma}{Lemma}[section]
%% \newtheorem{example}{Example}[section]
%% \newtheorem{theorem}{Theorem}[section]
%% \newtheorem{definition}{Definition}[section]
%% \newtheorem{corollary}{Corollary}[section]


  \sbox{\proofsavebox}
    {\unitlength 1pt\begin{picture}(6.5,6.5)%
     \put(0,0){\framebox(6.5,6.5){}}\end{picture}}
  \newcommand\proofbox{\usebox{\proofsavebox}\relax}

\newcommand\mathproofbox{\rlap{\quad\proofbox}}

\def\@nprf{\normalfont\rmfamily \trivlist
  \item[\hskip \labelsep {\normalfont\itshape Proof}]%
  \item[]}

\def\@oprf[#1]{\normalfont\rmfamily \trivlist
  \item[\hskip \labelsep {\normalfont\itshape #1\ }]%
  \item[]}

\newenvironment{proof}
  {\@ifnextchar[{\@oprf}{\@nprf}}
  {\hspace*{15pt}\hbox{\proofbox}\endtrivlist}

\newenvironment{proof*}
  {\proof}
  {\endtrivlist}

\renewcommand\theequation{\@arabic\c@equation}

\setlength\arraycolsep{5\p@}
\setlength\tabcolsep{0\p@}
\setlength\arrayrulewidth{.5\p@}
\setlength\doublerulesep{1.5\p@}
\setlength\tabbingsep{\labelsep}
\setlength{\skip\@mpfootins}{\skip\footins}
\setlength\fboxsep{3\p@}
\setlength\fboxrule{.5\p@}

\newcommand\maketitle{\@ifnextchar [{\m@ketitleone}{\m@ketitleone[n]}}

\def\m@ketitleone[#1]{\par
  \begingroup
    \newpage
    \global\@topnum\z@
    \titlefntrue
    \def\thefootnote{\@fnsymbol\c@footnote}%
    \def\@makefnmark{\hbox{$\@thefnmark$}}%
    \@maketitle{#1}%
    \thispagestyle{titlepage}\@thanks
  \endgroup
  \global\let\@maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@title\@empty
  \global\let\@author\@empty
  \global\let\maketitle\relax
  \global\let\thanks\relax
  \setcounter{footnote}\z@
}

\def\pe@rl#1{%
  \if t#1 {\tpe@rl}\else
    \if T#1 {\Tpe@rl}\else
      \if f#1 {\fpe@rl}\else
        \if F#1 {\Fpe@rl}\else
          \if e#1 {\edpe@rl}\else
            \if E#1 {\Edpe@rl}\else
              \if o#1 {\otherpearl}\else
                \vspace*{32\p@}%
              \fi
            \fi
          \fi
        \fi
      \fi
    \fi
  \fi
}
%
\newenvironment{bookrevauthor}{\par\vskip5pt\noindent\ignorespaces}{\par}

\def\bookreventryfont{\fontsize{10}{13}\selectfont}
\newenvironment{bookreventry}{\par\bookreventryfont\noindent\leftskip18pt\rightskip18pt\ignorespaces}{\vskip7pt\@endparenv\@ignoretrue}
\newenvironment{question}{\par\vskip6.5pt\tablefont\noindent\ignorespaces}{\vskip6.5pt\@endparenv\@ignoretrue}
%
\def\spe@rl{\vspace*{32\p@}\normalfont\LARGE\rmfamily}
\def\epe@rl#1{\par\vspace*{6.5\p@}\xdef\@shorttitle{#1}}

\def\tpe@rl{\spe@rl T\ls H\ls E\ls O\ls R\ls E\ls T\ls
  I\ls C\ls A\ls L\ns  P\ls E\ls A\ls R\ls L\ls S%
  \epe@rl{Theoretical pearls}%
}

\def\Tpe@rl{\spe@rl T\ls H\ls E\ls O\ls R\ls E\ls T\ls
  I\ls C\ls A\ls L\ns  P\ls E\ls A\ls R\ls L%
  \epe@rl{Theoretical pearl}%
}

\def\fpe@rl{\spe@rl F\ls U\ls N\ls C\ls T\ls I\ls O\ls
  N\ls A\ls L\ns  P\ls E\ls A\ls R\ls L\ls S%
  \epe@rl{Functional pearls}%
}

\def\Fpe@rl{\spe@rl F\ls U\ls N\ls C\ls T\ls I\ls O\ls
  N\ls A\ls L\ns  P\ls E\ls A\ls R\ls L%
  \epe@rl{Functional pearl}%
}

\def\edpe@rl{\spe@rl E\ls D\ls U\ls C\ls A\ls T\ls I\ls O\ls N\ls A\ls L\ns 
  P\ls E\ls A\ls R\ls L\ls S%
  \epe@rl{Educational pearls}%
}

\def\Edpe@rl{\spe@rl E\ls D\ls U\ls C\ls A\ls T\ls I\ls O\ls N\ls A\ls L\ns 
  P\ls E\ls A\ls R\ls L%
  \epe@rl{Educational pearl}%
}

\def\otherpearl{\spe@rl
  \@ifundefined{othrpearl}
    {Please define {\normalfont\ttfamily\char92 othrpearl} to obtain\\ the correct title!}
    {\othrpearl}%
  \epe@rl{Short title--please redefine with {\normalfont\ttfamily\char92 shorttitle}}%
}

\def\authormark#1{\xdef\@authormark{#1}}

\def\author{\@ifnextchar [{\@authortwo}{\@authorone}}
\def\@authortwo[#1]#2{\@author{#2}\xdef\@authormark{#1}}
\def\@authorone#1{\@author{#1}\xdef\@authormark{#1}}
%
%\def\@author#1{\global\advance\authorcount by 1
%    \expandafter\xdef\csname author\romannumeral\the\authorcount\endcsname{#1}\affil{}}
%
\def\@author#1{\global\advance\authorcount by 1
    \expandafter\gdef\csname author\romannumeral\the\authorcount\endcsname{#1}}
%
\def\affil#1{\expandafter\gdef\csname affil\romannumeral\the\authorcount\endcsname{#1}}
\def\email#1{\expandafter\gdef\csname email\romannumeral\the\authorcount\endcsname{\normalfont\rmfamily
  \itshape\textup{(}e-mail: \textup{\texttt{#1})}}}
%
\def\and{{\reset@font and}}
%
\def\authorsep{\unskip, }
\newcount\authorcount\authorcount=0
\newcount\tempcount
\newcount\authortempcount
%
\def\@authors{%
    \ifnum\authorcount>0%  %%%% Authors available
       \tempcount=1%
       \loop%
       \ifnum\authorcount>0%
          \noindent{\reset@font\authorsize\csname author\romannumeral\the\tempcount \endcsname}\par\vskip3pt%
          \noindent{\baselineskip10pt\normalfont\reset@font\affilsize\itshape\csname affil\romannumeral\the\tempcount \endcsname\par}%
          \noindent{\baselineskip10pt\normalfont\affilsize\itshape\csname email\romannumeral\the\tempcount \endcsname\par}%
%             \ifnum\authorcount>1\ifnum\authorcount>2\ \else \ \and\  \fi\fi%
           \global\advance\authorcount by -1%
          \advance\tempcount by 1 %
         \vskip7pt
       \repeat
       \global\authortempcount\tempcount
    \fi}%
%
\def\spchapter{\@ifnextchar[{\@@spchapter}{\@@spchapter[]}}

\def\@@spchapter[#1]#2{\gdef\@spchapter{#2}}
\spchapter{}
%
\ifindex
   \def\@maketitle#1{\cleardoublepage\bgroup%
                    {\vspace*{18pt}\indexheadfont
\indexname\par}\vskip43pt
                    \egroup
                  }%
\else
\def\@maketitle#1{%
  \newpage\null
  \ifbookreview\vskip-29pt\else\vskip-25\p@\fi%
  {\centering \sloppy
   \pe@rl{#1}%
   \ifsptitle
      \ifx\@spchapetr\@empty\else{\spchapterfont\@spchapter}\par\vskip7pt\fi%
   \else
      \ifsplissue
       \ifx\@spchapetr\@empty\else{\splissuefont\@spchapter}\par\fi%
        \else
      \fi
   \fi
   {\normalfont\LARGE\itshape \@title\par}%
   \ifx\@subtitle\@empty%
   \else%
      	\vskip8pt%
	{\subtitlefont \@subtitle\par}%
%	\vskip4pt%
   \fi%
   \vskip 16\p@
   {%
      \@authors
   \par}%
  }%
  \ifsptitle\vspace*{-4\p@}\else\vskip 13.5\p@ \fi\ifbookreview\vskip26.5pt\fi%\@plus 2\p@ \@minus 1\p@
}
\fi
\def\abs@header#1{%
  \vbox{\hrule \@height .25pt  \@width30.05pc
  \vskip 8\p@ \@plus 3\p@ \@minus 1\p@
  \centerline{\normalfont\normalsize\bfseries #1}}%
}

\def\abs@body{%
  \list{}{\leftmargin\z@ \rightmargin\leftmargin
    \listparindent 1em \parsep \z@ \@plus 1\p@
    \topsep 8\p@ %\@plus 3\p@ \@minus 1\p@
    }%
  \item[]\normalfont\small\rmfamily
}

\newcommand\abstractname{Abstract}
\newenvironment{abstract}
  {\ifsptitle\vspace*{17.3\p@}\else\fi\abs@header{\abstractname}\abs@body}
  {\endlist\vbox{\hrule \@height .25pt \@width 30.05pc}%
   \gdef\abs@header##1{\vskip 2\p@
     \centerline{\normalfont\normalsize\bfseries ##1}}}

\newcommand\capsulename{Capsule Review}
\newenvironment{capsule}
  {\abs@header{\capsulename}\abs@body}
  {\endabstract}


\mark{{}{}}

\newcommand\shortauthor[1]{\gdef\@shortauthor{#1}}
\gdef\@shortauthor{}

\renewcommand\title{\@ifnextchar [{\@titletwo}{\@titleone}}
\def\@titleone#1{\gdef\@title{#1}\xdef\@shorttitle{#1}}
\def\@titletwo[#1]#2{\gdef\@title{#2}\xdef\@shorttitle{#1}}
\gdef\@title{\mbox{}}

\newcommand\subtitle[1]{\xdef\@subtitle{#1}}
\subtitle{}

\newcommand\shorttitle[1]{\xdef\@shorttitle{#1}}

\newcommand\volume[1]{\gdef\@volume{#1}}
\gdef\@volume{{\normalfont\bfseries 1} (1):}

\newcommand\pagerange[1]{\gdef\@pagerange{#1}}
\gdef\@pagerange{1--000}

\newcommand\pubyear[1]{\gdef\@year{#1}}
\gdef\@year{19XX}

\newcommand\jdate[1]{\gdef\@jdate{#1}}
\gdef\@jdate{January \@year}

\newcommand\doi[1]{\gdef\@doi{10.1017/#1}}
\gdef\@doi{10.1017/S0000000000000000}

%% TB

\def\Copyright{\raise.2pt\hbox{\fontsize{8}{8}\selectfont\ooalign{\hfil\raise.9pt\hbox{\hskip-.3pt{\normalfont\fontsize{7.5}{7.5}\selectfont
c}}%
                \hfil\crcr\mathhexbox20D}}}

\newcommand\journal[1]{\gdef\@journal{#1}}
%
\def\pubonline#1{\gdef\@pubonline{#1}}
\def\@pubonline{}
%
\ifonline
  \def\@journal{%
  \vbox to 8.6\p@{\noindent\parbox[t]{4.8in}{\normalfont\onlineaffilsize\rmfamily
    {\itshape JFP\/}\ {\bf \@volume}\ (\@issue):\ \ifonepage\thepage\else\thepage--\pageref{lastpage}\fi* %
      (First pubd online \@cpyyear)\hskip5pt \Copyright\ 
      \@cpyyear\ Cambridge University Press\ doi:\@doi\\[2\p@]
    *Provisional -- final page numbers to be inserted when paper edition is published}% published
  \vss}}
\else
 \ifincremental
  \def\@journal{%
    \vbox to 8.6\p@{\noindent\parbox[t]{4.8in}{\sluglinefont%
    {\it JFP\kern-1pt{:}\/}\ page \ifonepage\thepage\else\thepage\ of\ \pageref{lastpage}\fi.\hskip7.5pt %
    \Copyright\ \@cpyyear\ Cambridge University Press\\[2\p@]
    doi:\@doi}%
  \vss}}%
\else
  \def\@journal{%
    \vbox to 8.6\p@{\noindent\parbox[t]{4.8in}{\sluglinefont%
    {\itshape JFP\/}\ {\bf \@volume}\ (\@issue):\ \ifonepage\thepage\else\thepage--\pageref{lastpage}\fi, %
     \@pubyear.\hskip7.5pt \Copyright\ 
      \@cpyyear\ Cambridge University Press\\[2\p@]
      doi:\@doi\hskip5pt \ifx\@pubonline\empty\else First published online \@pubonline\fi\hskip5pt  {Printed in the United Kingdom}}%{Printed in the United Kingdom}}%
  \vss}%
}
\fi\fi

\def\@underjournal{%
  \vbox to 5.6\p@{\noindent\parbox[t]{4.8in}{\normalfont\affilsize\rmfamily
    {\itshape Under consideration for publication in
     J.\ Functional Programming\/}\\[2.5\p@]
     \ }%
  \vss}%
}
%% 
\def\bookrevmark#1{\gdef\@bookrevmark{#1}}
\bookrevmark{Book review}
%
\def\rhfont{\fontsize{11}{11}\selectfont}
%%
\def\ps@headings{\let\@mkboth\markboth
  \def\@oddhead{\hfil{\ifbookreview\fontsize{10}{13}\selectfont\fi\itshape\@shorttitle}\hfil \llap{\rhfont\thepage}}%
  \def\@evenhead{\rlap{\rhfont\thepage}\hfil\ifbookreview{\fontsize{10}{13}\selectfont\itshape\@bookrevmark}\else\itshape\@authormark\fi\hfil}%
  \let\@oddfoot\@empty
  \let\@evenfoot\@oddfoot
  \def\sectionmark##1{\markboth{##1}{}}%
  \def\subsectionmark##1{\markright{##1}}%
}

\def\ps@Empty{%
      \def\@oddfoot{}%
      \let\@evenfoot\@oddfoot
      \def\@evenhead{}%
      \def\@oddhead{}%
      \let\@mkboth\markboth
      \let\chaptermark\@gobble
      \let\sectionmark\@gobble%
}

\def\ps@myheadings{\let\@mkboth\@gobbletwo
  \def\@oddhead{\hfil{\itshape\rightmark}\hfil \llap{\rhfont\thepage}}%
  \def\@evenhead{\rlap{\rhfont\thepage}\hfil\itshape\leftmark\hfil}%
  \let\@oddfoot\@empty
  \let\@evenfoot\@oddfoot
  \let\sectionmark\@gobble
  \let\subsectionmark\@gobble
}

\def\@indjournal{%
  \vbox to 6.5\p@{\noindent\parbox[t]{4.8in}{\normalfont\affilsize\rmfamily
    {\itshape J. Functional Programming\/}\ {\bf \@volume}\ (\@issue):\
\thepage--\pageref{lastpage}, \@pubyear\hskip7.5pt {Printed in
United Kingdom}}%
  \vss}%
}

\ifprodtf
  \let\@j@urnal\@journal
\else
  \let\@j@urnal\@underjournal
\fi

\def\ps@titlepage{\leftskip\z@ \let\@mkboth\@gobbletwo
  \def\@oddhead{\ifindex\@indjournal
\hfil\hbox{\llap{\rhfont\thepage}}\else\@j@urnal \hfil\raise1.6pt\hbox{\llap{\rhfont\thepage}}\fi}%
  \let\@evenhead\@oddhead
  \let\@oddfoot\@empty
  \let\@evenfoot\@oddfoot
  \let\sectionmark\@gobble
  \let\subsectionmark\@gobble
}

\def\@pnumwidth{1.55em}
\def\@tocrmarg {2.55em}
\def\@dotsep{4.5}
\setcounter{tocdepth}{2}

\def\@dottedtocline#1#2#3#4#5{% FROM LATEX.LTX
  \ifnum #1>\c@tocdepth \else
    \vskip \z@ \@plus.2\p@
    {\leftskip #2\relax \rightskip \@tocrmarg \parfillskip -\rightskip
     \parindent #2\relax\@afterindenttrue
     \interlinepenalty\@M
     \leavevmode
     \@tempdima #3\relax
     \advance\leftskip \@tempdima \null\hskip -\leftskip
     {#4}\nobreak
     \leaders\hbox{$\m@th
        \mkern \@dotsep mu\hbox{\phantom{.}}\mkern \@dotsep
        mu$}\hfill
     \nobreak
     \hb@xt@\@pnumwidth{\hfil\normalfont \normalcolor #5}%
     \par}%
  \fi}

\newcommand\contentsname{Contents}

\newcommand\tableofcontents{%
  \section*{\contentsname}%
  \@starttoc{toc}\par
  \vspace{13\p@}%
}

\newcommand*\l@part[2]{%
  \ifnum \c@tocdepth >-2\relax
    \addpenalty{-\@highpenalty}%
    \addvspace{.5\baselineskip \@plus 1\p@}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      {\leavevmode
       \normalfont\rmfamily
       #1\hfil \hb@xt@\@pnumwidth{\hfil}}\par
       \nobreak
       \if@compatibility
         \global\@nobreaktrue
         \everypar{\global\@nobreakfalse\everypar{}}%
      \fi
    \endgroup
    \vskip .25\baselineskip \@plus 1\p@
  \fi
}

\newcommand*\l@section[2]{%
  \ifnum \c@tocdepth >\z@
    \addpenalty\@secpenalty
    \setlength\@tempdima{1.5em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      \leavevmode \normalfont\rmfamily
      \advance\leftskip\@tempdima
      \hskip -\leftskip
      {\bfseries #1}\nobreak\hfil \nobreak\hb@xt@\@pnumwidth{\hss #2}\par
    \endgroup
  \fi}

\newcommand*\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\newcommand*\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\newcommand*\l@paragraph{\@dottedtocline{4}{7.0em}{4.1em}}
\newcommand*\l@subparagraph{\@dottedtocline{5}{10em}{5em}}

\newcommand\listfigurename{List of Figures}
\newcommand\listoffigures{%
  \section*{\listfigurename}%
  \@starttoc{lof}\par
  \vskip 13\p@
}

\newcommand*\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}

\newcommand\listtablename{List of Tables}
\newcommand\listoftables{%
  \section*{\listtablename}%
  \@starttoc{lot}\par
  \vskip 13\p@
}

\let\l@table\l@figure

\renewcommand\footnoterule{%
  \kern-3\p@
  \hrule \@width .4\columnwidth height \z@
  \kern 3\p@}

\newif\iftitlefn

%%
\newbox\tempbox
\newdimen\@footmax
\def\footmax#1{%
  \setbox\tempbox\hbox{\footnotesize$^{#1}$}%
  \global\@footmax\wd\tempbox\global\advance\@footmax.5em}
%
\footmax{0}
%%
\newcommand\@makefntext[1]{%
  \leavevmode\@hangfrom{\hb@xt@ \@footmax{\hss$\iftitlefn\else^\fi{\@thefnmark}\hskip.5em$}}#1}
%%

\ifprodtf \else \let\highast\ast\fi

\def\@fnsymbol#1{\ensuremath{% FROM LATEX.LTX
  \ifcase#1\or \hbox{$\highast$}\or \dagger\or \ddagger\or
    \mathchar "278\or \mathchar "27B\or \|\or \hbox{$\highast\highast$}\or
    \dagger\dagger\or \ddagger\ddagger\or \mathchar "278\mathchar "278\or
    \mathchar "27B\mathchar "27B\or \|\|\or \else\@ctrerr\fi}%
}

\renewcommand\@makefnmark{\hbox{$^{\@thefnmark}$}}% FROM LATEX.LTX
\renewcommand\thefootnote{\@arabic\c@footnote}% FROM LATEX.LTX
\renewcommand\thempfootnote{\mathit{\@alph\c@mpfootnote}}% FROM LATEX.LTX

\setcounter{topnumber}{2}
\renewcommand\topfraction{.9}
\setcounter{bottomnumber}{1}
\renewcommand\bottomfraction{.9}
\setcounter{totalnumber}{3}
\renewcommand\textfraction{.1}
\renewcommand\floatpagefraction{.9}
\setcounter{dbltopnumber}{2}
\renewcommand\dbltopfraction{.9}
\renewcommand\dblfloatpagefraction{.5}

\newcounter{table}
\renewcommand\thetable{\@arabic\c@table}
\def\fps@table{tbp}
\def\ftype@table{1}
\def\ext@table{lot}
\newcommand\tablename{Table}
\def\fnum@table{\tablename\ \thetable}

\newenvironment{table}
  {\@float{table}}
  {\end@float}

\newenvironment{table*}
  {\@dblfloat{table}}
  {\end@dblfloat}

\def\fstyle@table{\normalfont\small\rmfamily}
\def\fjust@table{\centering}
\def\fcapjust@table{\centering}
\def\fcapsize@table{\normalfont\normalsize\rmfamily}
\def\fcapstyle@table{\normalfont\normalsize\itshape}

\newcommand\contname{(cont.)}
\newcommand\continuedfigure{%
  \addtocounter{figure}\m@ne
  \let\curr@thefigure\thefigure
  \def\thefigure{\curr@thefigure\ \contname}%
}

\newcommand\continuedtable{%
  \addtocounter{table}\m@ne
  \let\curr@thetable\thetable
  \def\thetable{\curr@thetable\ \contname}%
}

\newif\ifrem@fullpt
\newcommand\removefullpoint{\global\rem@fullpttrue}

\newif\ifbot@fig
\newenvironment{bottomfigure}{\def\fps@figure{b}%
  \setcounter{bottomnumber}{1}%
  \global\bot@figtrue
  \@float{figure}\fstyle@figure}
  {\end@float}

\newbox\@tempboxb

\def\enskip{\hskip4.5pt}
\long\def\@makecaption#1#2{%
  \ifbot@fig \rule{30.05pc}{.25\p@}\fi
  \vskip 0\p@ %\@plus .4\p@ \@minus .4\p@
  \begingroup
  \setbox\@tempboxb\hbox{#2}%
  \def\@xtra{\ifdim\wd\@tempboxb>\z@ \ifrem@fullpt\else .\enskip\fi\fi}%
  \setbox\@tempboxa\hbox{#1\@xtra #2}%
  \ifdim\wd\@tempboxa>\tw@\textwidth
    {\let\centering\relax #1\@xtra #2\par}%
  \else
    #1\@xtra #2\par
  \fi
  \endgroup
  \global\bot@figfalse
  \global\rem@fullptfalse
}

\newcounter{figure}
\renewcommand\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{2}
\def\ext@figure{lof}
\newcommand\figurename{Fig.}
\def\fnum@figure{\figurename\ \thefigure}

\newenvironment{figure}
  {\@float{figure}}
  {\end@float}

\newenvironment{figure*}
  {\@dblfloat{figure}}
  {\end@dblfloat}

\def\fstyle@figure{\normalfont\small\rmfamily}
\def\fjust@figure{\centering}
\def\fcapjust@figure{\centering}
\def\fcapsize@figure{\normalfont\small\rmfamily}
\def\fcapstyle@figure{\normalfont\small\rmfamily}

\long\def\@caption#1[#2]#3{% FROM LATEX.LTX
  \par
  \addcontentsline{\csname ext@#1\endcsname}{#1}%
    {\protect\numberline{\csname the#1\endcsname}{\ignorespaces #2}}%
  \begingroup
    \@parboxrestore
    \if@minipage
      \@setminipage
    \fi
    \normalsize
    \@makecaption{\csname fcapjust@#1\endcsname
                  \csname fcapsize@#1\endcsname
                  \csname fnum@#1\endcsname}%
                 {\csname fcapstyle@#1\endcsname \ignorespaces #3}\par
  \endgroup
}

\def\@xfloat #1[#2]{% FROM LATEX.LTX
  \@nodocument
  \def\@captype {#1}%
  \def\@fps {#2}%
  \@onelevel@sanitize \@fps
  \def \reserved@b {!}%
  \ifx \reserved@b \@fps
    \@fpsadddefault
  \else
    \ifx \@fps \@empty
      \@fpsadddefault
    \fi
  \fi
  \ifhmode
    \@bsphack
    \@floatpenalty-\@Mii
  \else
    \@floatpenalty-\@Miii
  \fi
  \ifinner
    \@parmoderr\@floatpenalty\z@
  \else
    \@next\@currbox\@freelist
      {%
       \@tempcnta \sixt@@n
       \expandafter \@tfor \expandafter \reserved@a
         \expandafter :\expandafter =\@fps
         \do
          {%
           \if \reserved@a h%
             \ifodd \@tempcnta
             \else
               \advance \@tempcnta \@ne
             \fi
           \fi
           \if \reserved@a t%
             \@setfpsbit \tw@
           \fi
           \if \reserved@a b%
             \@setfpsbit 4%
           \fi
           \if \reserved@a p%
             \@setfpsbit 8%
           \fi
           \if \reserved@a !%
             \ifnum \@tempcnta>15
               \advance\@tempcnta -\sixt@@n\relax
             \fi
           \fi
           }%
       \@tempcntb \csname ftype@\@captype \endcsname
       \multiply \@tempcntb \@xxxii
       \advance \@tempcnta \@tempcntb
       \global \count\@currbox \@tempcnta
       }%
    \@fltovf
  \fi
  \global \setbox\@currbox
    \color@vbox
      \normalcolor
      \vbox \bgroup
        \hsize\columnwidth
        \@parboxrestore
        \@floatboxreset
        \csname fstyle@\@captype\endcsname
        \csname fjust@\@captype\endcsname
}

\let\oldtabular\tabular
\let\endoldtabular\endtabular

\def\tabular{% FROM LATEX.LTX
  \def\@halignto{to \textwidth}\tabskip\tabcolsep \@plus 1fil\@ttabular
}

\def\@ttabular{\leavevmode \hbox \bgroup $\let\@acol\@tabacol
   \let\@classz\@tabclassz
   \let\@classiv\@tabclassiv \let\\\@tabularcr\@ttabarray}

\def\@ttabarray{\m@th\@ifnextchar[\@tarray{\@ttarray}}

\def\@tarray[#1]#2{\t@barray[#1]{@{\tabskip\tw@\tabcolsep \@plus 3\p@}#2}}
\def\@ttarray#1{\t@barray[c]{@{\tabskip\tw@\tabcolsep \@plus 3\p@}#1}}

\def\t@barray[#1]#2{%
  \if #1t\vtop \else \if#1b\vbox \else \vcenter \fi\fi
  \bgroup
  \setbox\@arstrutbox\hbox{%
    \vrule \@height\arraystretch\ht\strutbox
           \@depth\arraystretch \dp\strutbox
           \@width\z@}%
  \@mkpream{#2}%
  \edef\@preamble{%
    \halign \noexpand\@halignto
      \bgroup \tabskip\z@skip \@arstrut \@preamble \tabskip\tabcolsep \@plus 1fil\cr}%
  \let\@startpbox\@@startpbox \let\@endpbox\@@endpbox
  \let\tabularnewline\\%
  \let\par\@empty
  \let\@sharp##%
  \set@typeset@protect
  \lineskip\z@skip\baselineskip\z@skip
  \@preamble}

\newcommand\ls{\kern.15em\relax}
\newcommand\ns{\kern.55em\relax}

\def\hline{% FROM LATEX.LTX
  \noalign{\ifnum0=`}\fi \vskip 6\p@
  \hrule \@height \arrayrulewidth \vskip 6\p@
  \futurelet \reserved@a\@xhline}

\def\@xhline{% FROM LATEX.LTX
  \ifx\reserved@a\hline
    \vskip -12\p@
    \vskip\doublerulesep
  \fi
  \ifnum0=`{\fi}}

\newcommand\today{}
\edef\today{\number\day\ \ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December
 \fi \ \number\year}

\renewcommand\@biblabel[1]{}% FROM LATEX.LTX
\newcommand\newblock{\hskip .11em \@plus .33em \@minus .07em}

\newcommand\refname{References}
\newenvironment{thebibliography}[1]
  {\section*{\refname}%
   \normalfont\small\rmfamily
   \addcontentsline{toc}{section}{\refname}%
   \list{}{\usecounter{enumiv}\labelwidth\z@ \leftmargin 9pt \itemindent -9pt}%
   \parindent\z@
   \parskip 2\p@ \@plus .1\p@
   \sloppy\clubpenalty\z@ \widowpenalty\@M
   \sfcode`\.\@m\relax}
  {\def\@noitemerr
   {\@latex@warning{Empty `thebibliography' environment}}%
   \endlist}
%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  End Bibliography Section %%%%%%%%%%%%%%%%
\def\@citex[#1]#2{% FROM LATEX.LTX
  \let\@citea\@empty
  \@cite{\@for\@citeb:=#2\do
    {\@citea\def\@citea{; }%
     \edef\@citeb{\expandafter\@firstofone\@citeb}%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \@ifundefined{b@\@citeb}{\mbox{\reset@font\bfseries ?}%
       \G@refundefinedtrue
       \@latex@warning
         {Citation `\@citeb' on page \thepage \space undefined}}%
       {\csname b@\@citeb\endcsname}}}{#1}}

\def\@cite#1#2{{\if@tempswa #2\else (#1)\fi}}% FROM LATEX.LTX

\let\@internalcite\cite
\def\cite{\def\citename##1{##1}\@internalcite}
\DeclareRobustCommand\shortcite{\def\citename##1{}\@internalcite}

\newif\iffontfound
\newcommand\checkfont[1]{%
  \batchmode
  \font\test=#1\relax
  \errorstopmode
  \fontfoundfalse
  \ifx\test\nullfont \else \fontfoundtrue\fi
}
%%%%%%%%%%%
%
\def\ct@indenttext#1{\parindent24pt{\par\hangindent48pt #1\par}}
\def\ct@Indenttext#1{\parindent48pt{\par\hangindent48pt #1\par}}
%
%
%
\newcount\minute
\newcount\hour
\def\currenttime{%
     \minute\time
     \hour\minute
     \divide\hour60
     \the\hour:\multiply\hour60\advance\minute-\hour\the\minute}
%%%%%
\def\gray{\special{color CMYK 0 0 0 0.5}}
\def\@questionmark{\vbox to 0pt{\vskip13pc\hskip-5pc
                  \hbox to \textwidth{\special{color push}\gray\fontsize{270}{270}\selectfont ?
                  \special{color pop}\hss}}}
\def\questionmark#1{\xdef\@questionmark{#1}}%
%
\def\@TotalChars{}
\def\TotalChars#1{\xdef\@TotalChars{#1}}%
%%
\def\document{\endgroup
  \ifx\@unusedoptionlist\@empty\else
    \@latex@warning@no@line{Unused global option(s):^^J%
            \@spaces[\@unusedoptionlist]}%
  \fi
  \@colht\textheight
  \@colroom\textheight \vsize\textheight
  \columnwidth\textwidth
  \@clubpenalty\clubpenalty
  \if@twocolumn
    \advance\columnwidth -\columnsep
    \divide\columnwidth\tw@ \hsize\columnwidth \@firstcolumntrue
  \fi
  \hsize\columnwidth \linewidth\hsize
  \begingroup\@floatplacement\@dblfloatplacement
    \makeatletter\let\@writefile\@gobbletwo
    \global \let \@multiplelabels \relax
    \@input{\jobname.aux}%
  \endgroup
  \if@filesw
     \immediate\openout\@mainaux=\jobname.aux
     \immediate\write\@mainaux{\relax}
  \fi
  \process@table
  \let\glb@currsize\@empty  %% Force math initialization.
  \normalsize
  \everypar{}%
  \ifx\normalsfcodes\@empty
    \ifnum\sfcode`\.=\@m
      \let\normalsfcodes\frenchspacing
    \else
      \let\normalsfcodes\nonfrenchspacing
    \fi
  \fi
  \@noskipsecfalse
  \let \@refundefined \relax
  \let\AtBeginDocument\@firstofone
  \@begindocumenthook
  \ifdim\topskip<1sp\global\topskip 1sp\relax\fi
  \global\@maxdepth\maxdepth
  \global\let\@begindocumenthook\@undefined
  \ifx\@listfiles\@undefined
    \global\let\@filelist\relax
    \global\let\@addtofilelist\@gobble
  \fi
  \gdef\do##1{\global\let ##1\@notprerr}%
  \@preamblecmds
  \global\let \@nodocument \relax
  \global\let\do\noexpand
  \ignorespaces}
%
%%
\def\enddocument{\label{lastpage}%
   \@checkend{document}%
   \@enddocumenthook
   \ifodd\c@page\cleardoublepage\else\clearpage\fi
   \begingroup
     \if@filesw
       \immediate\write\@mainaux{\string\questionmark{}}%
       \immediate\closeout\@mainaux
       \let\@setckpt\@gobbletwo
       \let\@newl@bel\@testdef
       \@tempswafalse
       \makeatletter
       \catcode`\\0
       \catcode`\{1
       \catcode`\}2
       \catcode`\^=7
       \catcode`\_=8
       \catcode`\&=4
       \catcode`\$=3  
       \catcode`\@11
       \catcode`\#6
       \catcode`\"=12
       \input\jobname.aux
     \fi
     \@dofilelist
     \ifdim \font@submax >\fontsubfuzz\relax
       \@font@warning{Size substitutions with differences\MessageBreak
                  up to \font@submax\space have occured.\@gobbletwo}%
     \fi
     \@defaultsubs
     \@refundefined
     \if@filesw
       \ifx \@multiplelabels \relax
         \if@tempswa
           \@latex@warning@no@line{Label(s) may have changed.
               Rerun to get cross-references right}%
         \fi
       \else
         \@multiplelabels
       \fi
     \fi
   \endgroup
   \deadcycles\z@\@@end}
%%
\def\@outputpage{%
\begingroup           % the \endgroup is put in by \aftergroup
  \let \protect \noexpand
  \@resetactivechars
  \@parboxrestore
  \shipout \vbox{%
    \set@typeset@protect
    \aftergroup \endgroup
    \aftergroup \set@typeset@protect
                                % correct? or just restore by ending
                                % the group?
  \if@specialpage
    \global\@specialpagefalse\@nameuse{ps@\@specialstyle}%
  \fi
  \if@twoside
    \ifodd\count\z@ \let\@thehead\@oddhead \let\@thefoot\@oddfoot
         \let\@themargin\oddsidemargin
    \else \let\@thehead\@evenhead
       \let\@thefoot\@evenfoot \let\@themargin\evensidemargin
    \fi
  \fi
  \reset@font
  \normalsize
  \normalsfcodes
  \let\label\@gobble
  \let\index\@gobble
  \let\glossary\@gobble
  \baselineskip\z@skip \lineskip\z@skip \lineskiplimit\z@
    \@begindvi\trimmarks
    \vskip \topmargin
    \moveright\@themargin \vbox {%
      \setbox\@tempboxa \vbox to\headheight{%
        \vfil
        \color@hbox
          \normalcolor
          \hb@xt@\textwidth{\@thehead}%
        \color@endbox
        }%                        %% 22 Feb 87
      \dp\@tempboxa \z@
      \box\@tempboxa
      \vskip \headsep
      \box\@outputbox
      \baselineskip \footskip
      \color@hbox
        \normalcolor
        \hb@xt@\textwidth{\@thefoot}%
      \color@endbox
      }%
    }%
  \global \@colht \textheight
  \stepcounter{page}%
  \let\firstmark\botmark
  \ifodd\c@page
     \ifspreadlong\global\spreadlongfalse
     \enlargethispage{\@spreadlong}\fi
  \fi
}
%%%%%
\newif\ifspreadlong
\def\spreadlong#1{\ifodd\c@page\wlog{Ignoring spreadlong}
                  \else
                     \spreadlongtrue\gdef\@spreadlong{#1}%
                     \enlargethispage{#1}%
                  \fi}
% check specs and enable one or both of these commands
\def\leaflong#1{\enlargethispage{#1}}
%%%%%
\def\trimmarks{%
  \vbox to 0pt{%
     \vskip-25pt\parindent0pt
     \draftnote\offinterlineskip}%
  \ifdraft
    \vbox to 0pt{\hsize\trimwidth\offinterlineskip
    \parindent0pt\leftskip0pt\rightskip0pt
    \fboxsep0pt\fboxrule\draftrule
    \fbox{\vbox{\vskip\trimheight\hskip\trimwidth}}}%
%
    \vbox to 0pt{\hsize\trimwidth\offinterlineskip
    \parindent0pt\leftskip0pt\rightskip0pt
    \vbox to \trimheight{\offinterlineskip\parindent0pt
    \hbox to \trimwidth{\vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}\raisebox{2pc}{\hbox{\hskip-3.5pc\vrule width2pc height\trimrule}}\hfill
      \raisebox{2pc}{\vrule width2pc height\trimrule\hskip-3.75pc}
      \vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}%
    }\vfill
    \hbox to \trimwidth{\hbox{\hskip-3.5pc\vrule height\trimrule width2pc}\vbox to 3pc{\vspace*{4.5pc}\hbox{\hskip1.5pc\vrule width\trimrule height2pc}}\hfill
    \vbox to 3.5pc{\vskip5pc\hbox{\vrule height2pc width\trimrule}}\rlap{\hskip1.5pc\vrule width2pc height\trimrule}}}}%
%    
  \else
    \vbox to 0pt{\hsize\trimwidth\offinterlineskip
    \parindent0pt\leftskip0pt\rightskip0pt
    \vbox to \trimheight{\offinterlineskip\parindent0pt
    \hbox to \trimwidth{\vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}\raisebox{2pc}{\hbox{\hskip-3.5pc\vrule width2pc height\trimrule}}\hfill
      \raisebox{2pc}{\vrule width2pc height\trimrule\hskip-3.75pc}
      \vbox to 2pc{\vskip-3.5pc\hbox{\vrule height2pc width\trimrule}}%
    }\vfill
    \hbox to \trimwidth{\hbox{\hskip-3.5pc\vrule height\trimrule width2pc}\vbox to 3pc{\vspace*{4.5pc}\hbox{\hskip1.5pc\vrule width\trimrule height2pc}}\hfill
    \vbox to 3.5pc{\vskip5pc\hbox{\vrule height2pc width\trimrule}}\rlap{\hskip1.5pc\vrule width2pc height\trimrule}}}}
\fi
\insidedraftrules}
%
\def\insidedraftrules{\overfullrule0pt\leftskip0pt\rightskip0pt\vbox to 0pt{%
  \offinterlineskip\parindent0pt
  \vskip \topmargin
  \tempdimen\normaltextheight
  \advance\tempdimen\headheight
  \advance\tempdimen\headsep
  \moveright\@themargin
  \vbox{\vbox to 0pt{\vskip\headheight\vskip\headsep\vskip.2pt
   \vrule height\draftrule width\textwidth
   }
   \hbox{\fboxsep0pt\fboxrule\draftrule
        \fbox{\vbox to \tempdimen
                    {\hsize\textwidth\hskip\textwidth}}}}}}%
%

%%
%%
\usepackage{rotating}
%%
\ifprinter
   \def\draftnote{}
   \def\Qauthor{}
\else
\def\draftnote{\vbox to 0pt{\vskip-12pt
   \hbox{\ \footnotesize}}%\TeXversion
   \hbox{\ \footnotesize ZU064-05-FPR\qquad\jobname\qquad\today\qquad\currenttime\qquad %Char Count= \@TotalChars
   \@questionmark\hfil}}%
   \def\Qauthor#1{\marginpar{{\raggedright\footnotesize\bf #1\endgraf}}}
\fi
%%
\newdimen\figheight
\newdimen\figwidth
%
\def\ArtDir{art/}%
\input epsf.sty
%
\newbox\figtempbox
\def\ArtPiece#1{\epsfbox{\ArtDir#1}}%
%
\def\figurebox#1#2{%
    \@ifnextchar[{\@figurebox{#1}{#2}}{\@figurebox{#1}{#2}[]}}
%
\def\@figurebox#1#2[#3]{%
      \gdef\@thirdarg{#3}%
      \ifx\@thirdarg\empty
         \global\figheight=#1
         \global\figwidth=#2
      \else 
         \setbox\figtempbox=\hbox{\epsfbox{\ArtDir\@thirdarg}}%
         \global\figwidth=\wd\figtempbox
         \global\figheight=\ht\figtempbox
      \fi
       \centerline{\figbox}
    \vskip7pt}%
%
\def\figbox{%
     \ifx\@thirdarg\empty
        \vbox{\vskip.3pt\hsize\figwidth
        \hrule\hbox to\figwidth{\vrule\hfill\vbox to\figheight{%
              \hsize\figwidth\vfill}\vrule}\hrule}%
     \else
        \vbox{\hsize\figwidth
 	      \hbox to\figwidth{\vbox to\figheight{\hsize\figwidth\box\figtempbox}}}%
    \fi}
%
%
%
\newdimen\tabledim
\newskip\tableleftskip
\newskip\tablerightskip
\newskip\tabnoteleftskip
\newskip\tabnoterightskip
\newdimen\tablewidth
%

%
\def\tbl#1#2{%
  \setbox\tempbox\hbox{\tablefont#2}%
  \tabledim\hsize
  \advance\tabledim-\wd\tempbox
  \ifdim\tabledim>0pt
		 		\divide\tabledim2
  \else
  			\global\tabledim0pt
  \fi
  \global\tableleftskip\tabledim 
  \global\tablerightskip\tabledim plus.5fill
  \global\tabnoteleftskip\tabledim
  \global\tabnoterightskip\tabledim
  \caption{\tablefont #1}%
  {\centerline{\box\tempbox}}}%
%
\let\bulletlist\itemize
\let\endbulletlist\enditemize
\let\arabiclist\enumerate
\let\endarabiclist\endenumerate
\let\ulist\unnumlist
\let\endulist\endunnumlist
\def\bibauthor#1{{#1}}
\def\x{@{\extracolsep{\fill}}}
\def\tablefont{\fontsize{9}{11}\selectfont}%\leftskip\tableleftskip\rightskip\tablerightskip\mathversion{normal}}% use plus 1fill if needed
\def\tablecaptionfont{\fontsize{10}{12}\selectfont\itshape\leftskip\tableleftskip\rightskip\tablerightskip}%\itshape
\def\tablecaptionnumfont{\reset@font\fontsize{10}{12}\selectfont}% 
\def\TCHfont{\fontsize{9}{13}\selectfont}%
\def\TSCHfont{}%
\def\tabnotefont{\fontsize{9}{11}\selectfont\leftskip\tabnoteleftskip\rightskip\tabnoterightskip}% use plus 1fill if needed
\def\toprule{\\[-5pt]\Hline\\[-9pt]\Hline\\[-7.1pt]}
\def\colrule{\\[-7.8pt]\HHline\\[-7pt]}
\def\Colrule{\\[-8.6pt]\HHline\\[-5.2pt]}
\def\botrule{\\[-8.3pt]\Hline\\[-9pt]\Hline}
\def\crule#1{\\[-10.9pt]#1\\[-21.4pt]}
%
\def\Hline{%
  \noalign{\ifnum0=`}\fi\hrule \@height .5pt \futurelet%\@height \arrayrulewidth
   \@tempa\@xhline}
%
\def\HHline{%
  \noalign{\ifnum0=`}\fi\hrule \@height .5pt \futurelet%\@height \arrayrulewidth
   \@tempa\@xhline}
%
%
%
\def\pubDate#1{(#1)}
%
\newenvironment{ack}{\par\addvspace{\baselineskip}}{\par}
%
\def\@Afterheading{%
  \global\@nobreaktrue
  \everypar{%
    \if@nobreak
      \global\@nobreakfalse
      \clubpenalty \@M
      \if@afterindent \else
        {\setbox\z@\lastbox}%
      \fi
    \else
      \clubpenalty \@clubpenalty
      \everypar{}%
    \fi}}
%
\def\getBIBNUM#1{%
     \expandafter\getstring#1\@}
%
\def\getstring #1#2#3#4\@{\gdef\@@getstr{#1#2#3}}
%
\let\summary\abstract
\let\endsummary\endabstract
\let\makechaptertitle\relax
%
\@namedef{equation*}{$$}
\@namedef{endequation*}{$$}
%
\gdef\zero@{0}
\gdef\REF{ref}
\gdef\removedash#1-#2-#3#4#5#6#7#8#9{%
\gdef\tempa{#2}%
\gdef\tempb{#3}%
\ifx\tempa\REF%
\else%
\ifx\tempb\N%
\expandafter\removezeros#7#8#9%
\else%
\fi%
\fi%
\gdef\tempa{}\gdef\tempb{}}
%
\gdef\N{n}
%
\gdef\removezeros#1#2#3{%
\gdef\tempd{#1}%
\gdef\tempe{#2}%
\gdef\tempf{#3}%
\ifnum\tempd=\zero@%
  \ifnum\tempe=\zero@%
    $^\tempf$%
  \else%
    $^{\tempe\tempf}$%
   \fi%
\else%
    $^{\tempd\tempe\tempf}$%
\fi
\gdef\tempd{}\gdef\tempe{}\gdef\tempf{}}
\newcount\colcount
\newcount\firstcol
\newcount\lastcol
\def\getCOLNUM#1#2{
\global\colcount\expandafter\getnumber#2
\global\advance\colcount-\expandafter\getnumber#1
\global\advance\colcount1
\global\firstcol\expandafter\getnumber#1
\global\lastcol\expandafter\getnumber#2}
%
%\def\getnumber col#1{#1}
\def\getnumber #1{#1}
%
\gdef\removexref#1-#2-#3#4#5#6#7#8{%
\thechapter.\expandafter\removexzeros#6#7#8}
%
\gdef\removehash#1#2{#2}
\gdef\removexzeros#1#2#3{%
\gdef\tempd{#1}%
\gdef\tempe{#2}%
\gdef\tempf{#3}%
\ifnum\tempd=\zero@%
  \ifnum\tempe=\zero@%
{\tempf}%
  \else%
{\tempe\tempf}%
   \fi%
\else%
{\tempd\tempe\tempf}%
\fi
\gdef\tempd{}\gdef\tempe{}\gdef\tempf{}}
%
\newif\ifframed
\newif\ifnotablenum
%
\renewcommand{\textellipsis}{%
   .\kern\fontdimen3\font
   .\kern\fontdimen3\font
   .\kern\fontdimen3\font}
%
%
\let\thenotes\Notes
\let\endthenotes\endNotes
\let\endnote\Enote
\def\listhead#1{}
\let\parahead\prhead
%
\let\@chaptertitle\@chaptitle
%
\def\Pound{\hbox{\char'243}}%
%
\newbox\tempbox
%
\def\pubyear#1{\gdef\@pubyear{#1}}%\pubyear{2002}
\def\cpyyear#1{\gdef\@cpyyear{#1}}%\pubyear{2002}
\cpyyear{}
%\def\volume#1{\gdef\@volume{#1}}%\volume{xxx}
\def\issue#1{\gdef\@issue{#1}}%\volume{xxx}
\issue{}
\def\doi#1{\gdef\@doi{#1}}%\doi{10.1017$/$S002211200100622X}
%
\let\chapter\title
%
\def\indexfont{\fontsize{9}{10}\selectfont}
%
\def\alphabet#1{{\bf#1}\par\vskip.5\baselineskip}

%
\def\indexheadfont{\fontsize{18.5}{20.5}\selectfont\bfseries\centering}
\newcommand\indexname{Author index}
\newenvironment{theindex}[2][\relax]{\thispagestyle{empty}\authormark{\indexname}%\global\indextrue%%
      \ifx#2\relax\else\gdef\indexname{#2}\fi%
      \ifx#1\relax\else\gdef\indexhead{#1}\fi%
      \maketitle\indexfont%
      \parindent\z@
      \let\item\@idxitem
}{%
      \par%\global\indexfalse
}
\newcommand\@idxitem  {\par\hangindent9pt}
\newcommand\subitem   {\par\hangindent2em\hspace*{1em}}
\newcommand\subsubitem{\par\hangindent2em\hspace*{2em}}
\newcommand\indexspace{\par \vskip\baselineskip}
%
\newenvironment{indexpara}{\setbox\tempbox\hbox\bgroup}{\egroup}
\def\au#1{{\indexfont\scshape#1}}
\def\ttl#1{{\indexfont#1}}
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%\newcommand\email[1]{\par{\normalfont\rmfamily
%  \itshape\textup{(}e-mail: \textup{\texttt{#1})}}\par}

\edef\r@{\ifprodtf mtr\else cmr\fi}
%\edef\s@{\ifprodtf mtss\else cmr\fi}

\let\real@font@warning\@font@warning
\DeclareMathVersion{program}
\let\@font@warning\@gobble
\SetSymbolFont{letters}{program}{OT1}{\r@}{m}{sl}
\let\@font@warning\real@font@warning
\SetMathAlphabet{\mathnormal}{program}{OT1}{\r@}{m}{sl}


\newcommand{\programmath}{\mathversion{program}}
\newcommand{\unprogrammath}{\mathversion{normal}}
\newcommand{\figrule}{\begin{center}\hrule\end{center}}

\DeclareRobustCommand\dplus{\mathbin{+\!\!+}}
\DeclareRobustCommand\dequals{\mathbin{==}}
\DeclareRobustCommand\dcolon{\mathbin{::}}
\DeclareRobustCommand\dcolonequals{\mathbin{::=}}

\pagestyle{headings}
\pagenumbering{arabic}
\frenchspacing
\flushbottom

\def\parahead#1{}

\ifprinter
\voffset-18.4mm
\hoffset-25.4mm
\else
\voffset2.3pc
\hoffset-1pc
\fi
%%
\ifcompmod
\else
   \usepackage{mathptmx,bm}
   \DeclareMathVersion{bold}
   \usepackage{amsfonts}
\fi
%%
\endinput

% end of file jfp.cls
