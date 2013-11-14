%% This is file swtreport.cls
%%
%% It extends the basic report class in the following way:
%%  1. Fix the page size
%%  2. Provide a different title page
%%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{swtreport}[2012/07/14 tech report class for swt chair]

\@ifundefined{pdfoutput}{\errmessage{swtreport only supports PDF
    output}}{\relax}

\RequirePackage{graphicx}
\RequirePackage[pdftex,dvipsnames,usenames]{color}
\RequirePackage{amsthm}
\RequirePackage{relsize}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{report}}
\ProcessOptions
\LoadClass[a4paper]{report}

\renewcommand{\sfdefault}{phv}

\setlength{\textwidth}{12.2cm}
\setlength{\textheight}{19.3cm}
\frenchspacing
\widowpenalty=10000
\clubpenalty=10000

\setlength\oddsidemargin   {63\p@}
\setlength\evensidemargin  {63\p@}
\setlength\marginparwidth  {90\p@}

\setlength\headsep   {16\p@}

\setlength\footnotesep{7.7\p@}
\setlength\textfloatsep{8mm\@plus 2\p@ \@minus 4\p@}
\setlength\intextsep   {8mm\@plus 2\p@ \@minus 2\p@}

\setcounter{secnumdepth}{2}


% Theorem environments
% currently copied from AMS user guide
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\newtheorem{conjecture}{Conjecture}[section]
\newtheorem{example}{Example}[section]

\theoremstyle{remark}
\newtheorem*{remark}{Remark}
\newtheorem*{note}{Note}
\newtheorem{case}{Case}

\def\acknowledge#1{\gdef\@acknowledge{#1}}
\gdef\@acknowledge{}

\renewenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\@ne
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
     \if@twoside\else
        \setcounter{page}\@ne
     \fi
    }

\def\and{%                  % \begin{tabular}
  \end{tabular}%
  \par%\hskip 1em \@plus.17fil%
  \begin{tabular}[t]{l}}%   % \end{tabular}

\newcommand{\inst}[1]{\\{\hspace*{1cm}\smaller[2] #1}}

\newdimen\swt@leftmargin

\renewcommand\maketitle{%
  \begin{samepage}%
    \swt@leftmargin -\oddsidemargin
    \advance \swt@leftmargin by -1.5cm
    \let\footnotesize\small
    \let\footnoterule\relax
    \let\footnote\thanks
    \hspace*{\swt@leftmargin}\parbox{18cm}{\sffamily\begin{titlepage}%
    {\lineskip .75em\centering\textsf{\Huge \@title}\par}
    \vspace*{3em}\noindent
    {\color[gray]{0.5}\rule{18cm}{1mm}}
    \noindent
    {Technical Report \hfill \@date}
    {\color[gray]{0.5}\rule{18cm}{1mm}\\[2cm]}
    \begin{minipage}[b][9cm][c]{18cm}
      \hspace*{.5cm}
      \begin{minipage}[t][9cm][c]{8cm}
        \large
        \lineskip .75em
        \begin{tabular}[t]{l}%
          \@author
        \end{tabular}
      \end{minipage}%
      \hfill%
      \parbox[t][9cm][c]{9cm}{%
        \includegraphics[width=8cm]{unifr-neu}%\\[1cm]
                        %{\LARGE Chair of Software Engineering}
    }\\\mbox{}
    \end{minipage}%
    \@thanks
    \nopagebreak[4]%
    \par\noindent\raisebox{-3cm}[0pt][-4cm]{%
      \parbox{18cm}{%
        \raisebox{-0.8cm}[1cm]{\includegraphics[width=3cm]{iif-logo-en}}%
        \hspace*{1ex}\parbox{5in}{\small\@acknowledge}}}
      \end{titlepage}}
  \end{samepage}
  \newpage
  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@acknowledge\@empty
  \global\let\@fpnote\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\acknowledge\relax
  \global\let\fpnote\relax
  \global\let\and\relax
}

%% \newdimen\csltitle@topmargin
%% \newdimen\csltitle@leftmargin
%% \newdimen\csltitle@textwidth

%% \if@titlepage
%%   \renewcommand\maketitle{%
%%   \begin{samepage}%
%%   %%     \csltitle@leftmargin -\oddsidemargin
%%   %% \advance \csltitle@leftmargin by -.5in
%%   %% \hspace*{\csltitle@leftmargin}
%%     \hspace*{1cm}\parbox{7in}{\sffamily\begin{titlepage}%
%%   \let\footnotesize\small
%%   \let\footnoterule\relax
%%   \let \footnote \thanks
%%   \vspace*{1cm}\noindent
%%   %% \csltitle@topmargin -\topmargin
%%   %% \advance \csltitle@topmargin by -\headheight
%%   %% \advance \csltitle@topmargin by -\headsep
%%   %% \advance \csltitle@topmargin by -.5in
%%   %% \vspace*{\csltitle@topmargin}\noindent
%%   %% \csltitle@textwidth \textwidth
%%   %% \advance \csltitle@textwidth by \csltitle@leftmargin
%%   {\centering\includegraphics{unifr-neu}}\par
%%   \vspace*{1.5in}\noindent
%%   {\color[gray]{0.5}\rule{7in}{1mm}}
%%   \begin{flushright}
%%     Technical Report $\bullet$ \textsf{\@date}
%%   \end{flushright}
%%   \vspace*{.75in}
%%   \hspace*{1in}\raisebox{-.75in}[2in][0in]{\parbox{0in}{\rule{0pt}{6in}}\parbox[b]{6in}{%
%%   \begin{flushleft}%
%%     {\textsf{\LARGE \@title}\par}%
%%     \vskip 3em%
%%     {\large
%%      \lineskip .75em%
%%       \begin{tabular}[t]{l}%
%%         \@author
%%       \end{tabular}\par}%
%%       \vskip 1.5em%
%%       %% \ifx\@fpnote\@fpxnote\else \par\vspace*{3ex}\fbox{\parbox{\csltitle@textwidth}{\@fpnote}}\vspace*{1ex} \fi
%%   \end{flushleft}}}%
%%   \@thanks
%%   \nopagebreak[4]%
%%   \par\noindent\raisebox{-3.5in}[0pt][-4in]{\parbox{7in}{%
%%   \raisebox{-0.8cm}[1cm][1cm]{\includegraphics{iif-logo-en}}%
%%   \hspace*{1ex}\parbox{5in}{\small\@acknowledge}}%
%%   \end{titlepage}}%
%%   \end{samepage}%
%%   \setcounter{footnote}{0}%
%%   \global\let\thanks\relax
%%   \global\let\maketitle\relax
%%   \global\let\@thanks\@empty
%%   \global\let\@author\@empty
%%   \global\let\@date\@empty
%%   \global\let\@acknowledge\@empty
%%   \global\let\@fpnote\@empty
%%   \global\let\@title\@empty
%%   \global\let\title\relax
%%   \global\let\author\relax
%%   \global\let\date\relax
%%   \global\let\acknowledge\relax
%%   \global\let\fpnote\relax
%%   \global\let\and\relax
%% }
%% \else
%% \renewcommand\maketitle{\par
%%   \begingroup
%%     \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
%%     \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
%%     \long\def\@makefntext##1{\parindent 1em\noindent
%%             \hb@xt@1.8em{%
%%                 \hss\@textsuperscript{\normalfont\@thefnmark}}##1}%
%%     \if@twocolumn
%%       \ifnum \col@number=\@ne
%%         \@maketitle
%%       \else
%%         \twocolumn[\@maketitle]%
%%       \fi
%%     \else
%%       \newpage
%%       \global\@topnum\z@   % Prevents figures from going at top of page.
%%       \@maketitle
%%     \fi
%%     \thispagestyle{plain}\@thanks
%%   \endgroup
%%   \setcounter{footnote}{0}%
%%   \global\let\thanks\relax
%%   \global\let\maketitle\relax
%%   \global\let\@maketitle\relax
%%   \global\let\@thanks\@empty
%%   \global\let\@author\@empty
%%   \global\let\@date\@empty
%%   \global\let\@title\@empty
%%   \global\let\title\relax
%%   \global\let\author\relax
%%   \global\let\date\relax
%%   \global\let\and\relax
%% }

%% \def\@maketitle{%
%%   \newpage
%%   \null
%%   \vskip 2em%
%%   \begin{center}%
%%   \let \footnote \thanks
%%     {\LARGE \@title \par}%
%%     \vskip 1.5em%
%%     {\large
%%       \lineskip .5em%
%%       \begin{tabular}[t]{c}%
%%         \@author
%%       \end{tabular}\par}%
%%     \vskip 1em%
%%     {\large \@date}%
%%   \end{center}%
%%   \par
%%   \vskip 1.5em}
%% \fi

\if@twoside
  \def\ps@headings{%
      \let\@oddfoot\@empty\let\@evenfoot\@empty
      \def\@evenhead{\thepage\hfil\slshape\leftmark}%
      \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
      \let\@mkboth\markboth
    \def\chaptermark##1{%
%      \markboth {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\m@ne
%            \@chapapp\ \thechapter. \ %
%        \fi
%        ##1}}{}}%
      \markboth {{%
        \ifnum \c@secnumdepth >\m@ne
            \@chapapp\ \thechapter. \ %
        \fi
        ##1}}{}}%
    \def\sectionmark##1{%
%      \markright {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\z@
%          \thesection. \ %
%        \fi
%        ##1}}}}
      \markright {{%
        \ifnum \c@secnumdepth >\z@
          \thesection. \ %
        \fi
        ##1}}}}
\else
  \def\ps@headings{%
    \let\@oddfoot\@empty
    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
    \let\@mkboth\markboth
    \def\chaptermark##1{%
%      \markright {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\m@ne
%            \@chapapp\ \thechapter. \ %
%        \fi
%        ##1}}}}
      \markright {{%
        \ifnum \c@secnumdepth >\m@ne
            \@chapapp\ \thechapter. \ %
        \fi
        ##1}}}}
\fi

\renewcommand\tableofcontents{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
%    \chapter*{\contentsname
%        \@mkboth{%
%           \MakeUppercase\contentsname}{\MakeUppercase\contentsname}}%
    \chapter*{\contentsname
        \@mkboth{%
           \contentsname}{\contentsname}}%
    \@starttoc{toc}%
    \if@restonecol\twocolumn\fi
    }
\renewcommand\listoffigures{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
    \chapter*{\listfigurename
%      \@mkboth{\MakeUppercase\listfigurename}%
%              {\MakeUppercase\listfigurename}}%
      \@mkboth{\listfigurename}%
              {\listfigurename}}%
    \@starttoc{lof}%
    \if@restonecol\twocolumn\fi
    }

\renewcommand\listoftables{%
    \if@twocolumn
      \@restonecoltrue\onecolumn
    \else
      \@restonecolfalse
    \fi
    \chapter*{\listtablename
      \@mkboth{%
%          \MakeUppercase\listtablename}{\MakeUppercase\listtablename}}%
          \listtablename}{\listtablename}}%
    \@starttoc{lot}%
    \if@restonecol\twocolumn\fi
    }

\renewenvironment{thebibliography}[1]
     {\chapter*{\bibname
%        \@mkboth{\MakeUppercase\bibname}{\MakeUppercase\bibname}}%
        \@mkboth{\bibname}{\bibname}}%
      \list{\@biblabel{\@arabic\c@enumiv}}%
           {\settowidth\labelwidth{\@biblabel{#1}}%
            \leftmargin\labelwidth
            \advance\leftmargin\labelsep
            \@openbib@code
            \usecounter{enumiv}%
            \let\p@enumiv\@empty
            \renewcommand\theenumiv{\@arabic\c@enumiv}}%
      \sloppy\clubpenalty4000\widowpenalty4000%
      \sfcode`\.\@m}
{\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}

\renewenvironment{theindex}
               {\if@twocolumn
                  \@restonecolfalse
                \else
                  \@restonecoltrue
                \fi
                \columnseprule \z@
                \columnsep 35\p@
                \twocolumn[\@makeschapterhead{\indexname}]%
%                \@mkboth{\MakeUppercase\indexname}%
%                        {\MakeUppercase\indexname}%
                \@mkboth{\indexname}%
                        {\indexname}%
                \thispagestyle{plain}\parindent\z@
                \parskip\z@ \@plus .3\p@\relax
                \let\item\@idxitem}
               {\if@restonecol\onecolumn\else\clearpage\fi}
