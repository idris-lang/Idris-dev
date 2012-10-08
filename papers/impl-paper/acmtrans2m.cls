% latex2e by nr 7/3/96
% acmtrans.cls revised 4/19/96
%              revised again 31-JAN-1996 (see end of file)
%              revised 5-14-1997 :
%                       Don't use sans-serif font in categories and descriptors
%                       include latexsym by default
%                       Define longpage and shortpage
% Adjusted from the acmtrans2e.cls file to the needs of ACM TOCL by
% Marco Aiello on June 14, 2000.
% Further changes made by Frederic Goualard on Sep. 27, 2000
% to take care of the indentation problem in the bibliography 
% arising without the use of the hyperref package.
% Modularization to adapt to the needs of JACM, TOCL, 
% TODAES, TODS, TOGS, TOMS, AND TOPLAS, by Marco Aiello on 
% June 2001.
% Here is the basic framework that is needed to convert your paper 
% into ACM Transactions format and bibliographic format.  For a tutorial
% introduction, see ``instructions.tex'' (compile it with LaTeX) that
% accompanies the distribution of this style file.
%
%  -> \documentclass{acmtrans2m}
%  -> \markboth{}{}
%         takes 2 arguments and it is for the left- and right-page headers:
%         the first set of braces is assigned for author's name(s) 
%         and
%         the second set of braces is assigned for the title 
%             (if the title is too long, contraction may be needed
%  -> \title{}
%         if the title is too long, it can be separated by \\
%  -> \author{}
%         author1 \\ author1 affiliation
%         \and
%         author2 \\ author2 affiliation
%  -> \begin{abstract}
%  -> \end{abstract}
%
%  -> \category{}{}{}
%         takes 3 arguments for the Computing Reviews Classification Scheme.
%         ex: \category{D.3.3}{Programming Languages}{Language Constructs and 
%                   Features}[data types and structures]
%                   the last argument, in square brackets, is optional.
%  -> \terms{} (ex: \terms{Human Factors, Languages})
%  -> \keywords{} (in alphabetical order \keywords{document processing, sequences, 
%                      string searching, subsequences, substrings})
%  -> \begin{document}
%
%  -> \begin{bottomstuff}
%          similar to \thanks     
%          for authors' addresses; research/grant statements
%  -> \end{bottomstuff}
%  -> \maketitle
%
%     Now you can start the body of the paper; your figures, tables and 
%          use all the latex constructs.
%
%  -> \begin{acks}
%          acknowledgements
%  -> \end{acks}
%
%  -> \bibliographystyle{acmtrans}
%  -> \bibliography{mybib_file}
%
%     ****
%     If your paper has been accepted with a separate (electronic only)
%        appendix, you need to add the following control sequence:
%
%
%       body of appendix 
%!!!!!! \appendixhead has be cut into two: \appendixhead and \elecappendix
%!!!!!! See end of file. (jtb)
%
%  -> \end{document}
%
% Do not worry about the other definitions in this style file
% Remember to compile: latex, bibtex, latex latex
%
% Bibliographic cite forms needed:
%
%  \cite{key}
%    which produces citations with author list and year.
%    eg. [Brown 1978; Jarke, et al. 1985]
%  \citeA{key}
%    which produces citations with only the author list.
%    eg. [Brown; Jarke, et al.]
%  \citeN{key}
%    which produces citations with the author list and year, but
%    can be used as nouns in a sentence; no brackets appear around
%    the author names, but only around the year.
%      eg. Shneiderman [1978] states that......
%    \citeN should only be used for a single citation.
%    \citeNN{refkey1,refkey2} for author [ref1year; ref2year]
%    \citeyear{key}
%        which produces the year information only, within brackets.
%
% Abbreviated author lists use the ``et al.'' construct.
%
% The above are examples of required ACM bibliographic cite formats needed.
% *******************
% Here is the complete list of cite forms from the chicago bibliographic style
%
%  \cite{key}
%    which produces citations with abbreviated author list and year.
%  \citeNP{key}
%    which produces citations with abbreviated author list and year.
%  \citeA{key}
%    which produces only the abbreviated author list.
%  \citeANP{key}
%    which produces only the abbreviated author list.
%  \citeN{key}
%    which produces the abbreviated author list and year, with only the
%    year in parentheses. Use with only one citation.
%  \citeyear{key}
%    which produces the year information only, within parentheses.
%  \citeyearNP{key}
%    which produces the year information only.
%
% Abbreviated author lists use the ``et al.'' construct.
%
% `NP' means `no parentheses' 
%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{acmtrans2m} [1996/07/03 ACM Transactions class based on <23 April 96>]
\RequirePackage{latexsym}
%aiellom{
\RequirePackage{url}

% Do not change the following! Use the appropriate acmtocl, acmtods, ... option
\def\@acmVolume{V} %the volume
\def\@acmNumber{N} %the number
\def\@acmYear{YY}  %the last two digits of the year, 
\def\@acmMonth{Month}  %the month
\def\@journalName{ACM Journal Name} %the name of the ACM journal
\def\@journalNameShort{jn} %the acronym of the ACM journal
\def\@permissionCodeOne{0000-0000} %the permission code of the ACM journal
\def\@permissionCodeTwo{0000} %the permission code of the ACM journal part 2
\def\@pageCode{\acmPageCode} %the first page of the article in 4 digits


\newif\if@acmjacm
\newif\if@acmtocl
\newif\if@acmtodaes
\newif\if@acmtods
\newif\if@acmtogs
\newif\if@acmtoms
\newif\if@acmtoplas

\DeclareOption{acmnow}{
  \typeout{}
  \typeout{Directly generating the Month and Year for footers from the clock.}
  \def\@acmYear{\yearTwoDigits}  
  \def\@acmMonth{\monthWord}  
}

\DeclareOption{acmjacm}{
  \typeout{}
  \typeout{Using ACM, JACM's option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  %\global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  \global\@acmtodsfalse
  \global\@acmtogsfalse
  \global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmjacmtrue
  \def\@journalName{Journal of the ACM}
  \def\@journalNameShort{jacm}        
  \def\@permissionCodeOne{0004-5411} 
  \def\@permissionCodeTwo{0100} 
}

\DeclareOption{acmtocl}{
  \typeout{}
  \typeout{Using ACM, TOCL's option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  \global\@acmtodsfalse
  \global\@acmtogsfalse
  \global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmtocltrue
  \def\@journalName{ACM Transactions on Computational Logic}
  \def\@journalNameShort{tocl}        
  \def\@permissionCodeOne{1529-3785} 
  \def\@permissionCodeTwo{0700} 
}

\DeclareOption{acmtodaes}{
  \typeout{}
  \typeout{Using ACM, TODAES option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  %\global\@acmtodaesfalse
  \global\@acmtodsfalse
  \global\@acmtogsfalse
  \global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmtodaestrue
  \def\@journalName{ACM Transactions on Design Automation of Electronic Systems}
  \def\@journalNameShort{todaes}        
  \def\@permissionCodeOne{1084-4309} 
  \def\@permissionCodeTwo{0400} 
}

\DeclareOption{acmtods}{
  \typeout{}
  \typeout{Using ACM, TODS's option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  %\global\@acmtodsfalse
  \global\@acmtogsfalse
  \global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmtodstrue
  \def\@journalName{ACM Transactions on Database Systems}
  \def\@journalNameShort{tods}        
  \def\@permissionCodeOne{0362-5915} 
  \def\@permissionCodeTwo{0300} 
}

\DeclareOption{acmtogs}{
  \typeout{}
  \typeout{Using ACM, TOGS's option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  \global\@acmtodsfalse
  %\global\@acmtogsfalse
  \global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmtogstrue
  \def\@journalName{ACM Transactions on Graphics}
  \def\@journalNameShort{togs}        
  \def\@permissionCodeOne{0730-0301} 
  \def\@permissionCodeTwo{0100} 
}

\DeclareOption{acmtoms}{
  \typeout{}
  \typeout{Using ACM, TOMS's option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  \global\@acmtodsfalse
  \global\@acmtogsfalse
  %\global\@acmtomsfalse
  \global\@acmtoplasfalse
  \global\@acmtomstrue
  \def\@journalName{ACM Transactions on Mathematical Software}
  \def\@journalNameShort{toms}        
  \def\@permissionCodeOne{0098-3500} 
  \def\@permissionCodeTwo{1200} 
}

\DeclareOption{acmtoplas}{
  \typeout{}
  \typeout{Using ACM, TOPLAS option: 2001/06/01 by Marco Aiello et al.}
  \typeout{}
  \global\@acmjacmfalse  
  \global\@acmtoclfalse
  \global\@acmtodaesfalse
  \global\@acmtodsfalse
  \global\@acmtogsfalse
  \global\@acmtomsfalse
  %\global\@acmtoplasfalse
  \global\@acmtoplastrue
  \def\@journalName{ACM Transactions on Programming Languages and Systems}
  \def\@journalNameShort{toplas}        
  \def\@permissionCodeOne{0164-0925} 
  \def\@permissionCodeTwo{0500} 
}
%}aiellom



\if@compatibility\else
\DeclareOption{a4paper}
   {\setlength\paperheight {297mm}%
    \setlength\paperwidth  {210mm}%
    \def\special@paper{210mm,297mm}}
\DeclareOption{a5paper}
   {\setlength\paperheight {210mm}%
    \setlength\paperwidth  {148mm}%
    \def\special@paper{148mm,210mm}}
\DeclareOption{b5paper}
   {\setlength\paperheight {250mm}%
    \setlength\paperwidth  {176mm}%
    \setlength\voffset     {-15mm}%
    \setlength\hoffset     {-20mm}%
    \def\special@paper{176mm,250mm}}
\DeclareOption{letterpaper}
   {\setlength\paperheight {11in}%
    \setlength\paperwidth  {8.5in}%
    \def\special@paper{8.5in,11in}}
\DeclareOption{legalpaper}
   {\setlength\paperheight {14in}%
    \setlength\paperwidth  {8.5in}%
    \def\special@paper{8.5in,14in}}
\DeclareOption{executivepaper}
   {\setlength\paperheight {10.5in}%
    \setlength\paperwidth  {7.25in}%
    \def\special@paper{7.25in,10.5in}}
\DeclareOption{landscape}
   {\setlength\@tempdima   {\paperheight}%
    \setlength\paperheight {\paperwidth}%
    \setlength\paperwidth  {\@tempdima}}
\fi

\DeclareOption{checkMargin}{\setlength\overfullrule{5pt}}
\DeclareOption{final}{\setlength\overfullrule{0pt}}

\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}

\DeclareOption{10pt}{\def\@ptsize{0}} %needed for amssymbols.sty 
\DeclareOption{11pt}{\ClassError{acmtrans}{11pt style not supported}
                        {ACM transactions documents can be set in 10pt only}}
\DeclareOption{12pt}{\ClassError{acmtrans}{11pt style not supported}
                        {ACM transactions documents can be set in 10pt only}}
\newif\if@hyperref
\DeclareOption{hyperref}{%
        \def\pages{\pageref{@firstpg}--\pageref{@lastpg}}%
        \def\mypage{\thepage}%
        \def\@getpagenum#1#2#3#4{#2}%
        \def\pdfinfo#1#2{\pdfmark{pdfmark=/DOCINFO,Title=#1,Author=#2}}
        \global\@hyperreftrue
        }
\DeclareOption{nohyperref}{
                \def\pages{\pageref{@firstpg}--\pageref{@lastpg}}%
                \def\@getpagenum#1#2{#2}%
                \def\mypage{\thepage}%
                \def\pdfinfo#1#2{}%
                \def\pdfbookmark#1#2{}%
                \global\@hyperreffalse
                }
\DeclareOption{notfinal}{
                \def\pages{BD}%
                \def\mypage{TBD}%
                \def\@getpagenum#1#2{#2}%
                \def\pdfinfo#1#2{}%
                \def\pdfbookmark#1#2{}%
                }
\DeclareOption{omitline}{\def\@abstractbottom{\relax}}
\DeclareOption{dontomitline}{\def\@abstractbottom{\if@acmjacm\else\hbox{\vrule height .2pt width 30pc}\fi}}
\ExecuteOptions{twoside,notfinal,10pt,dontomitline,nohyperref,letterpaper} % defaults



\ProcessOptions

%{aiellom to automatize the issue specific data
\def\acmVolume#1{\def\@acmVolume{#1}}
\def\acmNumber#1{\def\@acmNumber{#1}}
\def\acmYear#1{\def\@acmYear{#1}}
\def\acmMonth#1{\def\@acmMonth{#1}}


% Command to get the year from the system and display the last two digits
\newcommand{\ignoretwo}[2]{}
\newcommand{\yearTwoDigits}{\expandafter\ignoretwo\the\year}
%To transform the month number in its name in English
\newcommand{\monthWord}{\ifnum\the\month=1 January\fi\ifnum\the\month=2 February\fi\ifnum\the\month=3 March\fi\ifnum\the\month=4 April\fi\ifnum\the\month=5 May\fi\ifnum\the\month=6 June\fi\ifnum\the\month=7 July\fi\ifnum\the\month=8 August\fi\ifnum\the\month=9 September\fi\ifnum\the\month=10 October\fi\ifnum\the\month=11 November\fi\ifnum\the\month=12 December\fi}
% overright the \@setref definition, so that if a reference is undefined 
% then it returns a number 0 and then the usual double boldface 
% question marks ??
% this is necessary for the \acmPageCode command, otherwise it gives an error 
% everytime the aux file is not there
\def\@setref#1#2#3{%
  \ifx#1\relax
    \number 0\relax
    \protect\G@refundefinedtrue
    \nfss@text{\reset@font\bfseries ??}%
    \@latex@warning{Reference `#3' on page \thepage \space undefined}%
  \else
    \expandafter#2#1\null
  \fi}
%make the code a four digits string based on the first page number
\newcommand{\acmPageCode}{\bgroup
  \newcount\c@tempo
  \setcounter{tempo}{\number\pageref{@firstpg}}\ifnum \c@tempo<1000 0\fi\ifnum \c@tempo<100 0\fi\ifnum \c@tempo<10 0\fi\ifnum \c@tempo<1 0\fi\pageref{@firstpg}
  \egroup
}
%}aiellom



\lineskip 1pt \normallineskip 1pt
\def\baselinestretch{1}

\renewcommand\normalsize{%
  \@setfontsize\normalsize\@xpt\@xiipt
  \abovedisplayskip 6pt plus2pt minus1pt\belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 6pt plus0pt minus 3pt
  \belowdisplayshortskip 6pt plus0pt minus3pt\let\@listi\@listI} 

\newcommand\small{%
  \@setfontsize\small\@ixpt{11pt}%
  \abovedisplayskip 5pt plus 2pt minus 1pt\belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 5pt plus0pt minus2pt\belowdisplayshortskip 5pt plus0pt
      minus 2pt
  \def\@listi{\leftmargin\leftmargini \topsep 5pt plus 2pt minus 1pt\parsep 0pt
    plus .7pt 
  \itemsep 1.6pt plus .8pt}}
\newcommand\footnotesize{%
%   \@setfontsize\footnotesize\@viiipt{10pt}
 \@setsize\footnotesize{10pt}\viiipt\@viiipt
  \abovedisplayskip 4pt plus 1pt minus 0pt\belowdisplayskip \abovedisplayskip
  \abovedisplayshortskip 4pt plus 0pt minus 1pt\belowdisplayshortskip 4pt plus
       0pt minus 1pt
  \def\@listi{\leftmargin\leftmargini \topsep 4pt plus 1pt minus
     0pt\parsep 0pt plus .5pt 
     \itemsep 1pt plus .7pt}}

\newcommand\scriptsize{\@setfontsize\scriptsize\@viipt\@viiipt}
\newcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
\newcommand\large{\@setfontsize\large\@xiipt{14}}
\newcommand\Large{\@setfontsize\Large\@xivpt{18}}
\newcommand\LARGE{\@setfontsize\LARGE\@xviipt{20}}
\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}

\normalsize 

 \oddsidemargin .75in \evensidemargin .75in \marginparwidth .5in 
 \marginparsep .125in 
 \topmargin .25in \headheight 12pt\headsep 16pt
  %% not in latex2e  \footheight 10pt
  \footskip 15pt 

\textheight 47pc \textwidth 30pc \columnsep 10pt \columnseprule 0pt 
% next five lines added by K.R. Apt, March 20, 01
\advance\textheight-2.6pt
\newdimen\normaltextheight
\setlength\normaltextheight{\textheight}
%\renewcommand\rmdefault{pnc}
%\renewcommand\sfdefault{phv}


\footnotesep 7pt
\skip\footins 15pt plus 4pt minus 3pt 
\floatsep 12pt plus 2pt minus 2pt 
\textfloatsep \floatsep 
\intextsep 1pc plus 1pc 
%%% not in 2e %% \@maxsep 1pc 
%%% not in 2e %% \@dblmaxsep 20pt 
\dblfloatsep 12pt plus 2pt minus 2pt 
\dbltextfloatsep 20pt plus 2pt minus 4pt 
\@fptop 0pt plus 1fil \@fpsep 1pc plus 2fil \@fpbot 0pt plus 1fil 
\@dblfptop 0pt plus 1fil \@dblfpsep 8pt plus 2fil \@dblfpbot 0pt plus 1fil
\marginparpush 6pt 

\parskip 0pt plus .1pt \parindent 10pt \partopsep 0pt 
\@lowpenalty 51 \@medpenalty 151 \@highpenalty 301 
\@beginparpenalty -\@lowpenalty \@endparpenalty -\@lowpenalty \@itempenalty
-\@lowpenalty 


\def\part{\@ucheadtrue
 \@startsection{part}{9}{\z@}{-10pt plus -4pt minus 
 -2pt}{4pt}{\reset@font\normalsize\sffamily}}
\def\section{\@ucheadtrue
 \@startsection{section}{1}{\z@}{-10pt plus -4pt minus 
 -2pt}{4pt}{\reset@font\normalsize\sffamily}}
\def\subsection{\@ucheadfalse
 \@startsection{subsection}{2}{\z@}{-8pt plus -2pt minus 
 -1pt}{4pt}{\reset@font\normalsize\sffamily}}
\def\subsubsection{\@ucheadfalse
 \@startsection{subsubsection}{3}{\parindent}{6pt plus 
1pt}{-5pt}{\reset@font\normalsize\itshape}}
\def\paragraph{\@ucheadfalse
 \@startsection{paragraph}{3}{\parindent}{6pt plus 
1pt}{-5pt}{\reset@font\normalsize\itshape}}

\renewcommand{\@seccntformat}[1]{\textup{\csname the#1\endcsname}}

\gdef\@period{.}
\def\@trivlist{\@topsepadd\topsep
\if@noskipsec \gdef\@period{}\leavevmode\gdef\@period{.}\fi
 \ifvmode \advance\@topsepadd\partopsep \else \unskip\par\fi
 \if@inlabel \@noparitemtrue \@noparlisttrue 
 \else \@noparlistfalse \@topsep\@topsepadd \fi
 \advance\@topsep \parskip
 \leftskip\z@\rightskip\@rightskip \parfillskip\@flushglue
 \@setpar{\if@newlist\else{\@@par}\fi} \global\@newlisttrue
\@outerparskip\parskip}


\def\@startsection#1#2#3#4#5#6{%
  \if@noskipsec \leavevmode \fi
  \par
  \@tempskipa #4\relax
  \@afterindenttrue
  \ifdim \@tempskipa <\z@
    \@tempskipa -\@tempskipa \@afterindentfalse
  \fi
  \if@nobreak
    \everypar{}%
  \else
    \addpenalty\@secpenalty\addvspace\@tempskipa
  \fi
  \@ifstar
    {\@ssect{#3}{#4}{#5}{#6}}%
    {\@dblarg{\@sect{#1}{#2}{#3}{#4}{#5}{#6}}}}
\def\@sect#1#2#3#4#5#6[#7]#8{%
  \ifnum #2>\c@secnumdepth
    \let\@svsec\@empty
  \else
    \refstepcounter{#1}%
      \if@uchead%
            \protected@edef\@svsec{\@seccntformat{#1}.\quad\relax}%
        \else%
            \protected@edef\@svsec{\@seccntformat{#1}\quad\relax}%
        \fi%
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@
    \begingroup
      #6{%
        \@hangfrom{\hskip #3\relax\@svsec}%
          \interlinepenalty \@M \if@uchead\MakeUppercase{#8}\else#8\fi \@@par}%
    \endgroup
    \csname #1mark\endcsname{#7}%
    \addcontentsline{toc}{#1}{%
      \ifnum #2>\c@secnumdepth \else
        \protect\numberline{\csname the#1\endcsname}%
      \fi
      #7}%
  \else
    \def\@svsechd{%
      #6{\hskip #3\relax
      \@svsec \if@uchead\Makeuppercase{#8}\else#8\fi}%
      \csname #1mark\endcsname{#7}%
      \addcontentsline{toc}{#1}{%
        \ifnum #2>\c@secnumdepth \else
          \protect\numberline{\csname the#1\endcsname}%
        \fi
        #7}}%
  \fi
  \@xsect{#5}}

\def\@xsect#1{\@tempskipa #1\relax
 \ifdim \@tempskipa>\z@
 \par \nobreak
 \vskip \@tempskipa
 \@afterheading
 \else \global\@nobreakfalse \global\@noskipsectrue
 \everypar{\if@noskipsec \global\@noskipsecfalse
 \clubpenalty\@M \hskip -\parindent
 \begingroup \@svsechd\@period \endgroup \unskip
 \hskip -#1
 \else \clubpenalty \@clubpenalty
 \everypar{}\fi}\fi\ignorespaces}
\newif\if@uchead\@ucheadfalse


\setcounter{secnumdepth}{3}
\newcounter{secnumbookdepth}
\setcounter{secnumbookdepth}{3}

\newfont{\apbf}{cmbx9}

\def\@withappendix#1{App--\number #1}

\newcommand{\elecappendix}{
}

\def\appenheader{\global\@topnum\z@ \global\@botroom \textheight \begin{figure}
\newfont{\sc}{cmcsc10}
\parindent\z@
\hbox{}
\vskip -\textfloatsep
\vskip 11pt
\hrule height .2pt width 30pc
\vskip 2pt\rule{0pt}{10pt}\ignorespaces}
\def\endappenheader{\end{figure}\gdef\appendixhead{}}

\def\@appsec{}

\def\appendix{\par
 \setcounter{section}{0}
 \setcounter{subsection}{0}
 \def\@appsec{APPENDIX } 
        \def\thesection{\Alph{section}}
        \def\theHsection{\Alph{section}}}



\labelsep 5pt
\settowidth{\leftmargini}{(9)} \addtolength\leftmargini\labelsep
\settowidth{\leftmarginii}{(b)} \addtolength\leftmarginii\labelsep
\leftmarginiii \leftmarginii
\leftmarginiv \leftmarginii 
\leftmarginv \leftmarginii 
\leftmarginvi \leftmarginii 
\leftmargin\leftmargini
\labelwidth\leftmargini\advance\labelwidth-\labelsep
\def\@listI{\leftmargin\leftmargini \parsep 0pt plus 1pt\topsep 6pt plus 2pt
minus 2pt\itemsep 2pt plus 1pt minus .5pt}
\let\@listi\@listI
\@listi 
\def\@listii{\leftmargin\leftmarginii
 \labelwidth\leftmarginii\advance\labelwidth-\labelsep
 \topsep 0pt plus 1pt 
 \parsep 0pt plus .5pt 
 \itemsep \parsep}
\def\@listiii{\leftmargin\leftmarginiii
 \labelwidth\leftmarginiii\advance\labelwidth-\labelsep
 \topsep 0pt plus 1pt 
 \parsep 0pt plus .5pt 
 \itemsep \parsep}
\def\@listiv{\leftmargin\leftmarginiv
 \labelwidth\leftmarginiv\advance\labelwidth-\labelsep}
\def\@listv{\leftmargin\leftmarginv
 \labelwidth\leftmarginv\advance\labelwidth-\labelsep}
\def\@listvi{\leftmargin\leftmarginvi
 \labelwidth\leftmarginvi\advance\labelwidth-\labelsep}




\def\enumerate{\ifnum \@enumdepth >3 \@toodeep\else
 \advance\@enumdepth \@ne 
 \edef\@enumctr{enum\romannumeral\the\@enumdepth}\list
 {\csname label\@enumctr\endcsname}{\usecounter
 {\@enumctr}\def\makelabel##1{##1\hss}}\fi}
\def\longenum{\ifnum \@enumdepth >3 \@toodeep\else
 \advance\@enumdepth \@ne 
 \edef\@enumctr{enum\romannumeral\the\@enumdepth}\list
 {\csname label\@enumctr\endcsname}{\usecounter
 {\@enumctr}\labelwidth\z@}\fi}
%\leftmargin\z@ \itemindent\parindent}\fi} - this indents each item in enumerate
\let\endlongenum\endlist
%%--------------------CHANGED: always roman parentheses. dave ---------------%%
\def\labelenumi{{\rm (}\arabic{enumi}\/{\rm )}} 
\def\theenumi{\arabic{enumi}} 
\def\labelenumii{{\rm (}\alph{enumii}\rm{)}}
\def\theenumii{\alph{enumii}}
\def\p@enumii{\theenumi}
\def\labelenumiii{\roman{enumiii}.}
\def\theenumiii{\roman{enumiii}}
\def\p@enumiii{\theenumi{\rm (}\theenumii{\rm )}}
\def\labelenumiv{\Alph{enumiv}.}
\def\theenumiv{\Alph{enumiv}} 
\def\p@enumiv{\p@enumiii\theenumiii}

\def\p@enumiv{\p@enumiii\theenumiii}

\def\itemize{\list{---\hskip -\labelsep}{\settowidth
 {\leftmargin}{---}\labelwidth\leftmargin
 \addtolength{\labelwidth}{-\labelsep}}}
\let\enditemize\endlist
\def\longitem{\list{---}{\labelwidth\z@
 \leftmargin\z@ \itemindent\parindent \advance\itemindent\labelsep}}
\let\endlongitem\endlist
\def\verse{\let\\=\@centercr 
 \list{}{\leftmargin 2pc 
 \itemindent -1.5em\listparindent \itemindent 
 \rightmargin\leftmargin\advance\leftmargin 1.5em}\item[]}
\let\endverse\endlist
\def\quotation{\list{}{\leftmargin 2pc \listparindent .5em
 \itemindent\listparindent
 \rightmargin\leftmargin \parsep 0pt plus 1pt}\item[]}
\let\endquotation=\endlist
\def\quote{\list{}{\leftmargin 2pc \rightmargin\leftmargin}\item[]}
\let\endquote=\endlist

\def\description{\list{}{\listparindent\parindent\labelwidth\z@
 \leftmargin\z@ \itemindent\parindent\advance\itemindent\labelsep
 \def\makelabel##1{\it ##1.}}}
\let\enddescription\endlist

\def\describe#1{\list{}{\listparindent\parindent\settowidth{\labelwidth}{#1}\leftmargin
 \labelwidth\addtolength\leftmargin\labelsep\def\makelabel##1{##1\hfil}}}
\let\enddescribe\endlist

        \def\program{\ifx\@currsize\normalsize\small \else \rm \fi\tabbing}
        \let\endprogram\endtabbing
         \def\@begintheorem#1#2{\trivlist \item[\hskip 10pt\hskip 
         \labelsep{\sc{#1}\hskip 5pt\relax #2.}] \itshape}
        % aiellom{: this is what makes the theorem environment with names 
        % ABOVE #1 is the word example, corollary, etc.
        %            #2 is the number
        % \def\@opargbegintheorem#1#2#3{\trivlist
        % \item[\hskip 10pt \hskip \labelsep{\sc #1\savebox\@tempboxa{#3}\ifdim 
        % \wd\@tempboxa>\z@ \hskip 5pt\relax \box\@tempboxa\fi.}] \itshape}
        %  is been changed to
        % #1 is the word theorem, lemma, etc.
        % #2 is the number
        % #3 is the name of the theorem, lemma, etc.
        \def\@opargbegintheorem#1#2#3{\trivlist
        \item[\hskip 10pt \hskip 
\labelsep{\sc{#1}\savebox\@tempboxa{\sc{#3}}\ifdim 
        \wd\@tempboxa>\z@ \hskip 5pt\relax \sc{#2}  \box\@tempboxa\fi.}]
\itshape}
        % aiellom} 



\newif\if@qeded\global\@qededfalse
\def\proof{\global\@qededfalse\@ifnextchar[{\@xproof}{\@proof}}
\def\endproof{\if@qeded\else\qed\fi\endtrivlist}
\def\qed{\unskip\kern 10pt{\unitlength1pt\linethickness{.4pt}\framebox(6,6){}}
\global\@qededtrue}
\def\@proof{\trivlist \item[\hskip 10pt\hskip 
 \labelsep{\sc Proof.}]\ignorespaces}
\def\@xproof[#1]{\trivlist \item[\hskip 10pt\hskip 
 \labelsep{\sc Proof #1.}]\ignorespaces}

\def\newdef#1#2{\expandafter\@ifdefinable\csname #1\endcsname
{\@definecounter{#1}\expandafter\xdef\csname
the#1\endcsname{\@thmcounter{#1}}\global
 \@namedef{#1}{\@defthm{#1}{#2}}\global
 \@namedef{end#1}{\@endtheorem}}}
\def\@defthm#1#2{\refstepcounter
 {#1}\@ifnextchar[{\@ydefthm{#1}{#2}}{\@xdefthm{#1}{#2}}}
\def\@xdefthm#1#2{\@begindef{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@ydefthm#1#2[#3]{\trivlist \item[\hskip 10pt\hskip 
 \labelsep{\it #2\savebox\@tempboxa{#3}\ifdim 
 \wd\@tempboxa>\z@ \ \box\@tempboxa\fi.}]\ignorespaces}
\def\@begindef#1#2{\trivlist \item[\hskip 10pt\hskip 
 \labelsep{\it #1\ \rm #2.}]}

\def\theequation{\arabic{equation}}

\def\titlepage{\@restonecolfalse\if@twocolumn\@restonecoltrue\onecolumn
 \else \newpage \fi \thispagestyle{empty}\c@page\z@}
\def\endtitlepage{\if@restonecol\twocolumn \else \newpage \fi}

\arraycolsep 2.5pt \tabcolsep 6pt \arrayrulewidth .4pt \doublerulesep 2pt 
\tabbingsep \labelsep 

\skip\@mpfootins = \skip\footins
\fboxsep = 3pt \fboxrule = .4pt 

\newcounter{part}
\newcounter{section}
\newcounter{subsection}[section]
\newcounter{subsubsection}[subsection]
\newcounter{paragraph}[subsubsection]

\def\thepart{\Roman{part}} 
\def\thesection {\arabic{section}}
\def\thesubsection {\thesection.\arabic{subsection}}
\def\thesubsubsection {\thesubsection.\arabic{subsubsection}}
\def\theparagraph {\thesubsubsection.\arabic{paragraph}}

\def\@pnumwidth{1.55em}
\def\@tocrmarg {2.55em}
\def\@dotsep{4.5}
\setcounter{tocdepth}{3}

\def\tableofcontents{\section*{Contents\@mkboth{CONTENTS}{CONTENTS}}
 \@starttoc{toc}}
\def\l@part#1#2{\addpenalty{\@secpenalty}
 \addvspace{2.25em plus 1pt} \begingroup
 \@tempdima 3em \parindent \z@ \rightskip \@pnumwidth \parfillskip
-\@pnumwidth 
 {\large \bf \leavevmode #1\hfil \hbox to\@pnumwidth{\hss #2}}\par
 \nobreak \endgroup}
\def\l@section#1#2{\addpenalty{\@secpenalty} \addvspace{1.0em plus 1pt}
\@tempdima 1.5em \begingroup
 \parindent \z@ \rightskip \@pnumwidth 
 \parfillskip -\@pnumwidth 
 \bf \leavevmode #1\hfil \hbox to\@pnumwidth{\hss #2}\par
 \endgroup}
\def\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\def\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\def\listoffigures{\section*{List of Figures\@mkboth
 {LIST OF FIGURES}{LIST OF FIGURES}}\@starttoc{lof}}
\def\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\def\listoftables{\section*{List of Tables\@mkboth
 {LIST OF TABLES}{LIST OF TABLES}}\@starttoc{lot}}
\let\l@table\l@figure


\def\thebibliography#1{\par\footnotesize 
\@ucheadfalse
\@startsection{subsection}{2}{\z@}{16pt plus 2pt minus 
        1pt}{2pt}{\sf}*{REFERENCES}%
\list{\arabic{enumi}.}{%
 \settowidth{\labelwidth}{99.}%
 \leftmargin\labelwidth
 \advance\leftmargin\labelsep \topsep \z@ \parsep 0pt plus .1pt
 \itemsep \parsep 
 \usecounter{enumi}}%
 \def\newblock{\hskip .11em plus .33em minus .07em}
 \sloppy
 \widowpenalty=4500
 \clubpenalty=4500
 \sfcode`\.=1000\relax}
\let\endthebibliography=\endlist
 

\newif\if@restonecol
\def\theindex{\@restonecoltrue\if@twocolumn\@restonecolfalse\fi
\columnseprule \z@
\columnsep 35pt\twocolumn[\section*{Index}]
 \@mkboth{INDEX}{INDEX}\thispagestyle{plain}\parindent\z@
 \parskip\z@ plus .3pt\relax\let\item\@idxitem}
\def\@idxitem{\par\hangindent 40pt}
\def\subitem{\par\hangindent 40pt \hspace*{20pt}}
\def\subsubitem{\par\hangindent 40pt \hspace*{30pt}}
\def\endtheindex{\if@restonecol\onecolumn\else\clearpage\fi}
\def\indexspace{\par \vskip 10pt plus 5pt minus 3pt\relax}

\def\footnoterule{\kern-3\p@
 \hrule \@height 0.2\p@ \@width 47\p@ 
  \kern 2.6\p@
} 

\long\def\@makefntext#1{\parindent 1em\noindent 
 $^{\@thefnmark}$#1}


\setcounter{topnumber}{3}
\def\topfraction{.99}
\setcounter{bottomnumber}{1}
\def\bottomfraction{.5}
\setcounter{totalnumber}{3}
\def\textfraction{.01}
\def\floatpagefraction{.85}
\setcounter{dbltopnumber}{2}
\def\dbltopfraction{.7}
\def\dblfloatpagefraction{.5}

\long\def\@makecaption#1#2{\vskip 1pc \setbox\@tempboxa\hbox{#1.\hskip
1em\relax #2}
 \ifdim \wd\@tempboxa >\hsize #1. #2\par \else \hbox
to\hsize{\hfil\box\@tempboxa\hfil} 
 \fi}

\def\nocaption{\refstepcounter\@captype \par
 \vskip 1pc \hbox to\hsize{\hfil \footnotesize Figure \thefigure
 \hfil}}


\newcounter{figure}
\def\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{Fig.\ \thefigure}
\def\figure{\let\normalsize\footnotesize \normalsize \@float{figure}}
\let\endfigure\end@float
\@namedef{figure*}{\@dblfloat{figure}}
\@namedef{endfigure*}{\end@dblfloat}

\newcounter{table}
\def\thetable{\@Roman\c@table}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{Table \thetable}
\def\table{\let\normalsize\footnotesize \normalsize\@float{table}}
\let\endtable\end@float
\@namedef{table*}{\@dblfloat{table}}
\@namedef{endtable*}{\end@dblfloat}
\def\acmtable#1{\@narrowfig #1\relax
 \let\caption\@atcap \let\nocaption\@atnocap
 \def\@tmpnf{}\@ifnextchar[{\@xntab}{\@ntab}}
\def\endacmtable{\hbox to \textwidth{\hfil
\vbox{\hsize \@narrowfig
\box\@nfcapbox
{\baselineskip 4pt \hbox{\vrule height .4pt width \hsize}}
\vskip -1pt
\box\@nfigbox\vskip -1pt
{\baselineskip 4pt \hbox{\vrule height .4pt width \hsize}}}\hfil}
\end@float}
\def\@xntab[#1]{\def\@tmpnf{[#1]}\@ntab}
\def\@ntab{\expandafter\table\@tmpnf
 \setbox\@nfigbox\vbox\bgroup
 \hsize \@narrowfig \@parboxrestore}
\def\@atmakecap #1#2{\setbox\@tempboxa\hbox{#1.\hskip 1em\relax #2}
 \ifdim \wd\@tempboxa >\hsize \sloppy #1.\hskip 1em\relax #2 \par \else \hbox
to\hsize{\hfil\box\@tempboxa\hfil}
 \fi}
\def\@atcap{\par\egroup\refstepcounter\@captype 
 \@dblarg{\@atcapx\@captype}}
\long\def\@atcapx#1[#2]#3{\setbox\@nfcapbox\vbox {\hsize \wd\@nfigbox
 \@parboxrestore
 \@atmakecap{\csname fnum@#1\endcsname}{\ignorespaces #3}\par}}
\def\@atnocap{\egroup \refstepcounter\@captype 
 \setbox\@nfcapbox\vbox {\hsize \wd\@nfigbox
 \hbox to\hsize{\hfil \footnotesize Table \thetable\hfil}}}

%
%% Narrow figures
%
\def\narrowfig#1{\@narrowfig #1\relax
 \let\caption\@nfcap \let\nocaption\@nfnocap
 \def\@tmpnf{}\@ifnextchar[{\@xnfig}{\@nfig}}
\def\endnarrowfig{\hbox to \textwidth{\if@nfeven
 \box\@nfcapbox\hfil\box\@nfigbox
 \else \box\@nfigbox\hfil\box\@nfcapbox\fi}\end@float}
\def\@xnfig[#1]{\def\@tmpnf{[#1]}\@nfig}
\def\@nfig{\expandafter\figure\@tmpnf
 \setbox\@nfigbox\vbox\bgroup
 \hsize \@narrowfig \@parboxrestore}
\def\@nfmakecap #1#2{\setbox\@tempboxa\hbox{#1.\hskip 1em\relax #2}
 \ifdim \wd\@tempboxa >\hsize \sloppy #1.\hskip 1em\relax #2 \par \else \hbox
to\hsize{\if@nfeven\else\hfil\fi\box\@tempboxa\if@nfeven\hfil\fi}
 \fi}
\def\@nfcap{\par\egroup\refstepcounter\@captype 
 \@dblarg{\@nfcapx\@captype}}
\long\def\@nfcapx#1[#2]#3{\@seteven
 \setbox\@nfcapbox\vbox to \ht\@nfigbox
 {\hsize \textwidth \advance\hsize -2pc \advance\hsize -\wd\@nfigbox
 \@parboxrestore
 \vfil 
 \@nfmakecap{\csname fnum@#1\endcsname}{\ignorespaces #3}\par
 \vfil}}
\def\@nfnocap{\egroup \refstepcounter\@captype \@seteven
 \setbox\@nfcapbox\vbox to \ht\@nfigbox
 {\hsize \textwidth \advance\hsize -2pc \advance\hsize -\wd\@nfigbox
 \@parboxrestore
 \vfil 
 \hbox to\hsize{\if@nfeven\else\hfil\fi 
 \footnotesize Figure \thefigure
 \if@nfeven\hfil\fi}
 \vfil}}
\def\@seteven{\@nfeventrue 
   \@ifundefined{r@@nf\thefigure}{}{%
      \edef\@tmpnf{\csname r@@nf\thefigure\endcsname}%
      \edef\@tmpnf{\expandafter\@getpagenum\@tmpnf}%
      \ifodd\@tmpnf\relax\@nfevenfalse\fi}%
\label{@nf\thefigure}\edef\@tmpnfx{\if@nfeven e\else o\fi}
\edef\@tmpnf{\write\@unused {\noexpand\ifodd \noexpand\c@page 
 \noexpand\if \@tmpnfx e\noexpand\@nfmsg{\thefigure} \noexpand\fi
 \noexpand\else 
 \noexpand\if \@tmpnfx o\noexpand\@nfmsg{\thefigure}\noexpand\fi 
 \noexpand\fi }}\@tmpnf}
\def\@nfmsg#1{Bad narrowfig: Figure #1 on page \thepage}

\newdimen\@narrowfig
\newbox\@nfigbox
\newbox\@nfcapbox
\newif\if@nfeven 

\def\and{\\ and\\}
\def\maketitle{\newpage \thispagestyle{titlepage}\par
 \begingroup \lineskip = \z@\null \vskip -30pt\relax 
 \parindent\z@ \LARGE {\raggedright \hyphenpenalty\@M
 %\sf \@title \par
  \@title \par
 \global\firstfoot %aiellom
 \global\runningfoot %aiellom
}
\label{@firstpg}
{ \vskip 13.5pt\relax \normalsize \sf %vskip 13.5pt between title and author
 \begingroup \addtolength{\baselineskip}{2pt}
 \@author\par \vskip -2pt 
 \endgroup }
 {\ifx \@categories\@empty 
 \else 
 \baselineskip 17pt\relax
 \if@acmjacm\else\hbox{\vrule height .2pt width 30pc}\fi%to eliminate the lines for jacm
 }
 \vskip 8.5pt \footnotesize \box\@abstract \vskip 4pt\relax %vskip8.5 space above abstract
 {\def\and{\unskip\/{\rm ; }}
 Categories and Subject Descriptors: \@categories \fi}\par\vskip 4pt\relax
 \box\@terms \vskip 4pt\relax
 \box\@keywords \par 
 {\baselineskip 14pt\relax 
 \@abstractbottom
 }
 \vskip 23pt\relax
 \endgroup
\let\maketitle\relax
 % \gdef\@author{}\gdef\@title{}
 \gdef\@categories{}}


\newbox\@abstract
\newbox\@terms
\newbox\@keywords
\def\abstract{\global\setbox\@abstract=\vbox\bgroup \everypar{}
 \footnotesize \hsize 30pc \parindent 10pt \noindent 
 \rule{0pt}{10pt}\ignorespaces}
\def\endabstract{\egroup}

\def\terms#1{\setbox\@terms=\vbox{\everypar{}
 \footnotesize \hsize 30pc \parindent 0pt \noindent 
 General Terms: \ignorespaces #1}}
\def\keywords#1{\setbox\@keywords=\vbox{\everypar{}
 \footnotesize \hsize 30pc \parindent 0pt \noindent 
 Additional Key Words and Phrases: \ignorespaces #1}
}

\def\category#1#2#3{\@ifnextchar
 [{\@category{#1}{#2}{#3}}{\@xcategory{#1}{#2}{#3}}}
\def\@category#1#2#3[#4]{\edef\@tempa{\ifx \@categories\@empty 
 \else ; \fi}{\def\protect{\noexpand\protect
 \noexpand}\def\and{\noexpand\and}\xdef\@categories{\@categories\@tempa #1
[{\bf #2}]: 
 #3\kern\z@---\hskip\z@{\it #4}}}}
\def\@xcategory#1#2#3{\edef\@tempa{\ifx \@categories\@empty \else ;
\fi}{\def\protect{\noexpand\protect\noexpand}\def\and{\noexpand
 \and}\xdef\@categories{\@categories\@tempa #1 [{\bf #2}]: #3}}}
\def\@categories{}
\def\bottomstuff{\global\@topnum\z@ \global\@botroom \textheight \begin{figure}
\parindent\z@
\hbox{}
\vskip -\textfloatsep
\vskip 10pt
\hrule height .2pt width 30pc
\vskip 2pt\rule{0pt}{10pt}\ignorespaces}
\def\endbottomstuff{\permission\end{figure}\gdef\permission{}}

\newenvironment{ackslike}[1]
  {\par \footnotesize 
   \@ucheadfalse
   \@startsection{subsection}{2}{\z@}{-16pt plus -2pt minus -1pt}{2pt}{\sf}*
   {\uppercase{#1}}\par\normalsize
   \pdfbookmark{Acknowledgments}{Ack}
        }
  {\par}
\newenvironment{acks}{\begin{ackslike}{ACKNOWLEDGMENTS}}{\end{ackslike}}

\def\received{\par\footnotesize\addvspace{18pt plus 0pt minus
4pt}\parindent\z@}
%the line below replaced by the line that follows (K.R. Apt, July 11, 2000
%\def\endreceived{\label{@lastpg}\hskip-2pt\par}
\def\endreceived{\label{@lastpg}\hskip-2pt\par\normalsize}

\mark{{}{}} 

\def\ps@myheadings{\let\@mkboth\@gobbletwo
\def\@oddhead{\hbox{}\hfill \small\sf \rightmark\hskip
19pt{\Large$\cdot$}\hskip 17pt\mypage}
\def\@oddfoot{\hbox{}\hfill\tiny\@runningfoot}
\def\@evenhead{\small\sf\mypage \hskip 17pt{\Large$\cdot$}\hskip 19pt\leftmark\hfill \hbox{}}
\def\@evenfoot{\tiny\@runningfoot\hfill\hbox{}}
\def\sectionmark##1{}\def\subsectionmark##1{}}
\def\@runningfoot{}
\def\runningfoot{\def\@runningfoot{\@journalName, Vol.\ \@acmVolume, No.\ \@acmNumber, \@acmMonth\ 20\@acmYear.}}
\def\@firstfoot{}
\def\firstfoot{\def\@firstfoot{\@journalName, Vol.\ \@acmVolume, No.\ \@acmNumber, \@acmMonth\ 20\@acmYear, Pages \pages.}}
\def\ps@titlepage{\let\@mkboth\@gobbletwo
\def\@oddhead{}\def\@oddfoot{\hbox{}\hfill
\tiny\@firstfoot}\def\@evenhead{}\def\@evenfoot{\tiny\@firstfoot\hfill\hbox{}}}

\def\today{\ifcase\month\or
 January\or February\or March\or April\or May\or June\or
 July\or August\or September\or October\or November\or December\fi
 \space\number\day, \number\year}
\def\@marrayclassiv{\@addtopreamble{$\displaystyle \@nextchar$}}
\def\@marrayclassz{\ifcase \@lastchclass \@acolampacol \or \@ampacol \or
 \or \or \@addamp \or
 \@acolampacol \or \@firstampfalse \@acol \fi
\edef\@preamble{\@preamble
 \ifcase \@chnum 
 \hfil$\relax\displaystyle\@sharp$\hfil \or $\relax\displaystyle\@sharp$\hfil 
 \or \hfil$\relax\displaystyle\@sharp$\fi}}
\def\marray{\arraycolsep 2.5pt\let\@acol\@arrayacol \let\@classz\@marrayclassz
 \let\@classiv\@marrayclassiv \let\\\@arraycr\def\@halignto{}\@tabarray}
\def\endmarray{\crcr\egroup\egroup}


\ps@myheadings \pagenumbering{arabic} \onecolumn 

%-----------------------BIBLIOGRAPHY STUFF-------------------------
% this is adapted (November 1993) by Andrew Appel and Rebecca Davies from
% 
%%%     filename        = "chicago.sty",
%%%     version         = "4",  % MODIFIED!
%%%     date            = "31 August 1992",
%%%     time            = "09:42:44 199",
%%%     author          = "Glenn Paulley",
%%%     address         = "Data Structuring Group
%%%                        Department of Computer Science
%%%                        University of Waterloo
%%%                        Waterloo, Ontario, Canada
%%%                        N2L 3G1",
%%%     telephone       = "(519) 885-1211",
%%%     FAX             = "(519) 885-1208",
%%%     email           = "gnpaulle@bluebox.uwaterloo.ca",

%%% ====================================================================
%
% this file: Modification of chicago.sty for new ACM bibliography
% style, which is similar (but not identical) to the ``Chicago'' style.
%
% chicago.sty: Style file for use with bibtex style chicago.bst, for
% bibliographies formatted according to the 13th Edition of the Chicago
% Manual of Style.
%
% 'newapa.bst' was made from 'plain.bst', 'named.bst', and 'apalike.bst',
% with lots of tweaking to make it look like APA style, along with tips
% from Young Ryu and Brian Reiser's modifications of 'apalike.bst'.
% newapa.sty formed the basis of this style, chicago.sty. Author-date
% references in newapa.bst formed the basis for chicago.bst. Chicagoa.bst
% supports annotations.
%
% Version 4 (August, 1992):
% - fixed chicago.bst and chicagoa.bst to handle long author lists in
%   sorting
% - fixed chicago.bst and chicagoa.bst so that missing page numbers in
%   ``article'' entries are handled correctly
% - modified chicago.sty to format entries with 2nd and subsequent lines
%   indented.
%
%   Citation format: (author-last-name year)
%             (author-last-name and author-last-name year)
%             (author-last-name et al. year)
%             (author-last-name)
%             author-last-name
%             author-last-name (year)
%             (author-last-name and author-last-name)
%             (author-last-name et al.)
%             (year) or (year,year)
%             year or year,year
%
%   Reference list ordering: alphabetical by author or whatever passes
%    for author in the absence of one.
%
% This BibTeX style has support for abbreviated author lists and for
%    year-only citations.  This is done by having the citations
%    actually look like
%
%    \citeauthoryear{full-author-info}{abbrev-author-info}{year}
%
% The LaTeX style has to have the following (or similar)
%
%     \let\@internalcite\cite
%     \def\fullcite{\def\citeauthoryear##1##2##3{##1, ##3}\@internalcite}
%     \def\fullciteA{\def\citeauthoryear##1##2##3{##1}\@internalcite}
%     \def\shortcite{\def\citeauthoryear##1##2##3{##2, ##3}\@internalcite}
%     \def\shortciteA{\def\citeauthoryear##1##2##3{##2}\@internalcite}
%     \def\citeyear{\def\citeauthoryear##1##2##3{##3}\@internalcite}
%
%
% -------------------------------------------------------------------------
%
% Citation macros.
%
\let\@internalcite\cite

\def\cite{\def\@citeseppen{-1000}%
    \def\@cite##1##2{[##1\if@tempswa , ##2\fi]}%
    \def\citeauthoryear##1##2##3{##2 ##3}\@internalcite}
\def\citeXNP#1#2{%
  \def\@cite@label{#2}%
  \def\@cite##1##2{##1\if@tempswa , ##2\fi}%
  \def\citeauthoryear##1##2##3{\@cite@label}\@internalcite{#1}}
% \def\@citeseppen{-1000}%
%    \def\@cite@label{#1}
%    \def\@cite##1##2{\if@tempswa ##2\fi}%
%    \def\citeauthoryear##1##2##3{##2 ##3}\@internalcite}
\def\citeNP{\def\@citeseppen{-1000}%
    \def\@cite##1##2{##1\if@tempswa , ##2\fi}%
    \def\citeauthoryear##1##2##3{##2 ##3}\@internalcite}
\def\citeN{\def\@citeseppen{-1000}%
    \def\@cite##1##2{##1\if@tempswa , ##2]\else{]}\fi}%
    \def\citeauthoryear##1##2##3{##2 [##3}\@citedata}
\def\shortcite#1{\citeyear{#1}}
\def\citeS#1{[\citeANP{#1} \citeyearNP{#1}]}
\def\citeNS#1{\citeANP{#1} \citeyear{#1}}
\def\citeNPS#1{\citeANP{#1} \citeyearNP{#1}}
%testing year,year
\def\citeNN{\def\@citeseppen{-1000}%
    \def\@cite##1##2{[##1\if@tempswa , ##2\fi]}%
    \def\citeauthoryear##1##2##3{##3}\@citedata}

\def\citeA{\def\@citeseppen{-1000}%
    \def\@cite##1##2{[##1\if@tempswa , ##2\fi]}%
    \def\citeauthoryear##1##2##3{##2}\@internalcite}
\def\citeANP{\def\@citeseppen{-1000}%
    \def\@cite##1##2{##1\if@tempswa , ##2\fi}%
    \def\citeauthoryear##1##2##3{##2}\@internalcite}

\def\citeyear{\def\@citeseppen{-1000}%
    \def\@cite##1##2{[##1\if@tempswa , ##2\fi]}%
    \def\citeauthoryear##1##2##3{##3}\@citedata}
\def\citeyearNP{\def\@citeseppen{-1000}%
    \def\@cite##1##2{##1\if@tempswa , ##2\fi}%
    \def\citeauthoryear##1##2##3{##3}\@citedata}

%
% \@citedata and \@citedatax:
%
% Place commas in-between citations in the same \citeyear, \citeyearNP,
% or \citeN command.
% Use something like \citeN{ref1,ref2,ref3} and \citeN{ref4} for a list.
%
\def\@citedata{%
        \@ifnextchar [{\@tempswatrue\@citedatax}%
                                  {\@tempswafalse\@citedatax[]}%
}

\def\@citedatax[#1]#2{%
\if@filesw\immediate\write\@auxout{\string\citation{#2}}\fi%
  \def\@citea{}\@cite{\@for\@citeb:=#2\do%
    {\@citea\def\@citea{; }\@ifundefined% by Young
       {b@\@citeb}{{\bf ?}%
       \@warning{Citation `\@citeb' on page \thepage \space undefined}}%
{\csname b@\@citeb\endcsname}}}{#1}}%

% don't box citations, separate with ; and a space
% also, make the penalty between citations negative: a good place to break.
%
\def\@citex[#1]#2{%
\if@filesw\immediate\write\@auxout{\string\citation{#2}}\fi%
  \def\@citea{}\@cite{\@for\@citeb:=#2\do%
    {\@citea\def\@citea{; }\@ifundefined% by Young
       {b@\@citeb}{{\bf ?}%
       \@warning{Citation `\@citeb' on page \thepage \space undefined}}%
{\csname b@\@citeb\endcsname}}}{#1}}%

% (from apalike.sty)
% No labels in the bibliography.
%
\def\@biblabel#1{}

% (from apalike.sty)
% Set length of hanging indentation for bibliography entries.
%
\newlength{\bibhang}
\setlength{\bibhang}{2em}

% Indent second and subsequent lines of bibliographic entries. Stolen
% from openbib.sty: \newblock is set to {}.

\newdimen\bibindent
\bibindent=1em
\@ifundefined{refname}%
   {\@ifundefined{chapter}%
     {\newcommand{\refname}{\footnotesize REFERENCES}}%
     {\newcommand{\refname}{\footnotesize BIBLIOGRAPHY}}%
   }%
   {}%
\@ifundefined{chapter}%
 {\def\thebibliography#1{\footnotesize \section*{\refname\@mkboth 
   {\uppercase{\refname}}{\uppercase{\refname}}}\list
   {[\arabic{enumi}]}{
   \settowidth\labelwidth{[#1]}
   \leftmargin\labelwidth
   \advance\leftmargin\labelsep
   \advance\leftmargin\bibindent
   \itemindent -\bibindent
   \listparindent \itemindent
   \parsep \z@
   \usecounter{enumi}}
   \def\newblock{}
   \sloppy
   \sfcode`\.=1000\relax}}
 {\def\thebibliography#1{\footnotesize \chapter*{\refname\@mkboth 
   {\uppercase{\refname}}{\uppercase{\refname}}}\list
   {[\arabic{enumi}]}{\settowidth\labelwidth{[#1]}
   \leftmargin\labelwidth
   \advance\leftmargin\labelsep
   \advance\leftmargin\bibindent
   \itemindent -\bibindent
   \listparindent \itemindent
   \parsep \z@
   \usecounter{enumi}}
   \def\newblock{}
   \sloppy
   \sfcode`\.=1000\relax}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% fixes to acm trans macro package
% 31-JAN-1996
% John Tang Boyland

% newdef need to take the optional parameters of newtheorem
\def\newdef#1{\@ifnextchar[{\@xnewdef{#1}}{\@ynewdef{#1}}}
\def\@xnewdef#1[#2]#3{\newtheorem{italic@#1}[#2]{{\em #3}}\@newdef{#1}}
\def\@ynewdef#1#2{\@ifnextchar[{\@xynewdef{#1}{#2}}{\@yynewdef{#1}{#2}}}
\def\@xynewdef#1#2[#3]{\newtheorem{italic@#1}{{\em #2}}[#3]\@newdef{#1}}
\def\@yynewdef#1#2{\newtheorem{italic@#1}{{\em #2}}\@newdef{#1}}
% and now fix up definition, to change body to use roman font:
\def\@newdef#1{\newenvironment{#1}{\@ifnextchar[{\@xstartdef{#1}}{\@ystartdef{#1}}}{\end{italic@#1}}}
%changed by K.R. Apt on Sep. 27, 2000. It was: \def\@xstartdef#1[#2]{\begin{italic@#1}[#2]\rm}
\def\@xstartdef#1[#2]{\begin{italic@#1}[{\em #2}]\rm}
\def\@ystartdef#1{\begin{italic@#1}\rm}

% footers produced too small (vpt), when ACM typsets them at 7.5pt (!).
% A better compromise is viipt.
\def\@oddfoot{\hbox{}\hfill\scriptsize\@runningfoot}
\def\@evenfoot{\scriptsize\@runningfoot\hfill\hbox{}}

% first footer was set to (vpt), when ACM typesets them at 6.5pt (!).
% A better compromise is vipt.
\def\firstfootsize{\@setsize\firstfootsize{7pt}\vipt\@vipt}
\def\ps@titlepage{\let\@mkboth\@gobbletwo
\def\@oddhead{}\def\@oddfoot{\hbox{}\hfill\firstfootsize\@firstfoot}%
\def\@evenhead{}\def\@evenfoot{\firstfootsize\@firstfoot\hfill\hbox{}}}

% new permission statement
\long\def\permission{\par
% linebreaks added to conform to the current style
Permission to make digital/hard copy of all or part of this material without
fee 
for personal or classroom use
provided that the copies are not made or distributed for profit
or commercial advantage, the ACM copyright/server notice, the title of the
publication, and its date appear, and notice is given that copying is by
permission of the ACM, Inc.  To copy
otherwise, to republish, to post on servers, or to redistribute to lists
requires prior specific 
permission and/or a fee.\par
\copyright\ 20\@acmYear\ 
ACM \@permissionCodeOne/20\@acmYear/\@permissionCodeTwo-\@pageCode\$5.00 % aiellom
}

% make sure \permission doesn't get trashed
\def\endbottomstuff{\permission\end{figure}}

% alternate way of using citeyear
%  \def\shortcite#1{\citeyear{#1}
% enumerations and longenums are wrong
% 1. the second line in a paragraph of an enumerations in theorems
%  (or other trivlists) doesn't line up under the first
% 1. the second line of a longenum doesn't properly wrap around
%  back to the left margin.

% the original definition of \@listI doesn't set labelwidth
\def\@listI{\leftmargin\leftmargini
 \labelwidth\leftmargini\advance\labelwidth-\labelsep
 \parsep 0pt plus 1pt
 \topsep 6pt plus 2pt minus 2pt
 \itemsep 2pt plus 1pt minus .5pt}
\let\@listi\@listI
\@listi 

% add set of \labelwidth and \itemindent
\def\longenum{\ifnum \@enumdepth >3 \@toodeep\else
 \advance\@enumdepth \@ne 
 \edef\@enumctr{enum\romannumeral\the\@enumdepth}\list
 {\csname label\@enumctr\endcsname}{\usecounter
 {\@enumctr}\labelwidth\z@\leftmargin\z@
 \itemindent\parindent \advance\itemindent\labelsep}\fi}

% split electronic appendix into two parts:


%aiellom{
\def\appendixhead#1{\appendix
\section*{ELECTRONIC APPENDIX}
The electronic appendix for this article can be accessed in
  the ACM Digital Library by visiting the following URL:$\;$ 
  \url{http://www.acm.org/pubs/citations/journals/}{\tt \@journalNameShort /20\@acmYear-\@acmVolume-\@acmNumber/p\pageref{@firstpg}-#1}.
% \quad \href{http://www.acm.org/tocl}{{\small http://www.acm.org/tocl} }
}
%aiellom}

\long\def\elecappendix{
\clearpage
\makeatletter
\pagenumbering{withappendix}
\makeatother
\appendix
\par\noindent{\sc This document is the online-only appendix to:}\hfill \vskip 1em
{\vbox{\Large\sf \parindent0pt\@title{}}}\vskip .5em
\vbox{\sf \parindent0pt\@author{}}\vskip .5em\noindent
\vskip 10pt\noindent
{\firstfootsize 
\@journalName, Vol.\ \@acmVolume, No.\ \@acmNumber, \@acmMonth\ 20\@acmYear, Pages \pages.}
\vskip 11pt\noindent
\hrule height .2pt
\par
\bottomstuff
\endbottomstuff
}

% provide for a single acknowledgment
\def\ack{ \par \footnotesize 
\@ucheadfalse
\@startsection{subsection}{2}{\z@}{-16pt plus -2pt minus 
 -1pt}{2pt}{\sf}*{ACKNOWLEDGMENT}\par\normalsize
\pdfbookmark{Acknowledgment}{Ack}
}
\def\endack{\par}

% provide both spellings of Acknowledgment(s)
\let\acknowledgments\acks
\let\endacknowledgments\endacks
\let\acknowledgment\ack
\let\endacknowledgment\endack

\newcommand{\longpage}{\enlargethispage{\baselineskip}}
\newcommand{\shortpage}{\enlargethispage{-\baselineskip}}


% Don't indent bibliography and
% override \refname (which sets fontsize):
\def\thebibliography#1{
  \footnotesize\section*{\footnotesize\sf{REFERENCES}\@mkboth
  {\uppercase{\refname}}{\uppercase{\refname}}}%
   \pdfbookmark{References}{Ref}
   \list
  {\@biblabel{\arabic{enumiv}}}{%
   %\settowidth\labelwidth{[#1]}
   \labelwidth 0pt
   \leftmargin \bibindent
   \labelsep 0pt
   \if@hyperref
     \itemindent -\bibindent
   \fi
   \listparindent -\bibindent
   \labelsep -\bibindent
    \usecounter{enumiv}%
    \let\p@enumiv\@empty
    \def\theenumiv{\arabic{enumiv}}}%
    \def\newblock{\hskip .11em plus.33em minus.07em}%
    \sloppy
    \clubpenalty=4500
    \widowpenalty=4500
    \frenchspacing}
\def\endthebibliography{%
  \def\@noitemerr{\@warning{Empty `thebibliography' environment}}%
  \endlist}
\def\@lbibitem[#1]#2{\item[]\if@filesw
      {\def\protect##1{\string ##1\space}\immediate
       \write\@auxout{\string\bibcite{#2}{#1}}}\fi\hskip-1em\ignorespaces}
% Fix cite so it doesn't repeat author lists in citations:

\def\cite{\def\@citeseppen{-1000}%
    \def\@cite##1##2{[##1\if@tempswa , ##2\fi]}%
    \let\@lastauthor=\@noauthor
    \let\citeauthoryear=\citeauthoryear@no@repeats\@internalcite}
    %\def\citeauthoryear##1##2##3{##2 ##3}\@internalcite

\def\@noauthor={\relax}
\let\@lastauthor=\@noauthor
\let\@currauthor=\@noauthor

\def\citeauthoryear@no@repeats#1#2#3{%
  \def\@currauthor{\csname @author #1\endcsname}%
  \ifx\@lastauthor\@currauthor{#3}\else{#2 #3}\fi%
  \let\@lastauthor=\@currauthor}

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*\mit{\@fontswitch\relax\mathnormal}


\if@hyperref
   \let\pdfbookmark=\relax
   \RequirePackage[pdfmark]{hyperref}
\fi

% \renewcommand{\thefootnote}{\arabic{footnote}\hspace{-3pt}}


