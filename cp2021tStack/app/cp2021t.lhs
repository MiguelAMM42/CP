\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage{amsmath}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "


%---------------------------------------------------------------------------

\title{
       	Cálculo de Programas
\\
       	Trabalho Prático
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 74
\\\hline
a93269 & Inês Oliveira Anes Vicente
\\
a93308 & Jorge Miguel Silva Melo
\\
a93280 & Miguel Ângelo Machado Martins
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b)
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a função
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que
|avg_aux = split avg length| em listas não vazias.

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg :: [Double ]-> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.)

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.}
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Função auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Animação:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes.

\subsection*{Problema 1} \label{pg:P1}
São dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}

\subsubsection{Alínea 1} \label{pg:P1.1}

Para resolver esta alínea, podemos começar por inferir o |outExpAr| através da propriedade do isomorfismo:

\begin{eqnarray*}
\start
	|outExpAr . inExpAr = id|
%
\just\equiv{ |inExpAr|:= |[const X, num_ops]| }
%
  |outExpAr . [const X, num_ops] = id|
%
\just\equiv{ Fusão-+(20) \& Functor-id(26) }
%
  |[outExpAr . const X, outExpAr . num_ops] = [i1,i2]|
%
\just\equiv{ |num_ops|:= |[N,ops]| \& |ops|:= |[bin,uncurry Un]| \& Eq-+(27) }
%
  \begin{lcbr}
    |outExpAr . const X = i1|\\
    |outExpAr . [N,[bin,uncurry Un]] = i2|
  \end{lcbr}
%
\just\equiv{ Fusão-+(20) }
%
  \begin{lcbr}
    |outExpAr . const X = i1|\\
    |[outExpAr . N, outExpAr . [bin,uncurry Un]] = i2|
  \end{lcbr}
%
\just\equiv{ Universal-+(17) }
%
  \begin{lcbr}
    |outExpAr . const X = i1|\\
    \begin{lcbr}
      |outExpAr . N = i2 . i1|\\
      |outExpAr . [bin,uncurry Un] = i2 .i2|
    \end{lcbr}
  \end{lcbr}
%
\just\equiv{ Fusão-+(20) \& Universal-+(17) }
%
  \begin{lcbr}
    |outExpAr . const X = i1|\\
    \begin{lcbr}
      |outExpAr . N = i2 . i1|\\
      \begin{lcbr}
        |outExpAr . bin = i2 . i2 . i1|\\
        |outExpAr . uncurry Un = i2 . i2 .i2|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}  
%
\just\equiv{ Def-comp(72) \& Introdução de variáveis }
% 
  \begin{lcbr}
    |outExpAr(const X ()) = i1()|\\
    \begin{lcbr}
      |outExpAr(N (a)) = i2(i1(a))|\\
      \begin{lcbr}
        |outExpAr(bin(op,(a,b))) = i2(i2(i1(op,(a,b))))|\\
        |outExpAr(uncurry Un(op,a)) = i2(i2(i2(op,a)))|
      \end{lcbr}
    \end{lcbr}
  \end{lcbr}  
\qed
\end{eqnarray*}

\begin{eqnarray*}
\xymatrix@@C=3.1cm{
    |ExpAr A| 
           \ar@@/^1.005pc/[r]^-{|outExpAr|} _-\cong
&
    |1 + ( A + ((BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)))|
           \ar@@/^1.005pc/[l]^-{|inExpAr|}    
}
\end{eqnarray*}


\begin{code}

outExpAr X = i1()    
outExpAr (N a) = i2(i1 a)
outExpAr (Bin op a b) = i2(i2(i1(op,(a,b))))
outExpAr (Un op a) = i2(i2(i2(op,a)))

\end{code}


Tanto no enunciado deste projeto como nas aulas os docentes iam-nos alertando para a importância de ler e analisar código. Na resolução deste exercício acabamos por perceber
essa importância, pois a análise do código do anexo \ref{sec:codigo} e/ou dos ficheiros da pasta \emph{src} mostraram-se essenciais na resolução dos problemas do projeto.
No caso desta segunda alínea do problema 1, depois de percebermos o funcionamento da função |baseExpAr| fornecida, o ficheiro \emph{List.hs} ajudou bastante na resolução deste
exercício.\\

Ao olharmos para a função |baseExpAr| percebemos que a mesma necessita de 7 argumentos. Acabamos por perceber que 7 argumentos eram estes ao interpretar o código da \emph{recList}.\\

Sendo o \emph{recList} o \emph{F f} das listas, fizemos a analogia para esta alínea, tendo em conta o \emph{outExpAr} definido na alínea anterior, uma vez que este gene só será executado depois dele.\\

Tendo em conta que |N a| representa um certo número e |X| uma variável, estes dois casos poderiam ser considerados como casos de paragem, uma vez que não são mais simplificáveis. 
Estas podem portanto ser do tipo |id|, fazendo aqui uma analogia clara com o caso de paragem das listas.  
Porém, nos outros 2 casos, a expressão pode necessitar de mais simplificações. No caso da |Un UnOp (ExpAr a)| só a |ExpAr| precisa de ser simplificada, ficando com o tipo |id >< f|, tal como acontecia, aliás,
no caso das listas.
Já na expressão com o operador binário, é necessário simplificar mais uma expressão do que no caso anterior, ficando, portanto, com o tipo |id >< (f >< f)|.\\

Relembrando a definição da função |baseExpAr|, que a a |recExpAr| invoca:\\

|baseExpAr f g h j k l z = f + (g + (h >< (j >< k) + l >< z))|\\

podemos facilmente atribuir valores a |f|,|g|,|h|,|j|,|k|,|l| e |z|:\\

\begin{itemize}
\item |f| é |id| e representa a |X|.
\item |g| é |id| e representa a |N a|.
\item |h >< (j >< k)|  é |id >< (f >< f)| e representa a |Bin BinOp (ExpAr a) (ExpAr a)|.\\
|h| é, portanto, |id|, |j| e |k| são |f|.
\item Por último, a expressão unária |Un UnOp (ExpAr a)| é representada por |l >< z|, ou seja, |id >< f|.\\
\end{itemize}

\\A expressão final pretendida é |id + (id + (id >< (f >< f) + id >< f))|, que é facilmente inserida na função |baseExpAr| com as conclusões enumeradas em cima.
\\Temos, assim, reunidas as condições para afirmar que:\\

\begin{code}

recExpAr x =  baseExpAr id id id x x id x

\end{code}

\subsubsection{Alínea 2} \label{pg:P1.2}

Temos agora reunidas as condições, com a informação recolhida na alínea 1 e tendo ainda em conta a assinatura da |cataExpAr|, para afirmar que o diagrama do catamorfismo deste
problema pode ser expresso por:

\xymatrix@@C=4cm{
    |ExpAr A| 
           \ar[d]_-{|cata (f)|}      
           \ar@@/^1.005pc/[r]^-{|outExpAr|} _-\cong
&
    |1 + ( A + ((BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)))|
           \ar@@/^1.005pc/[l]^-{|inExpAr|}    
           \ar[d]^{|recExpAr| |cata (f)|}   
\\
     |Rational|
&
     |1 + ( A + ((BinOp >< (Rational >< Rational)) + (UnOp >< Rational)))|
           \ar[l]^-{|f = g_eval_exp a|}
}


Para a resolução desta alínea consideramos que o gene deveria simplificar expressões, aplicando as propriedades das expressões que as mesmas representam.\\
O gene deve ter, portanto, 2 argumentos: os mesmos 2 da |eval_exp|. São estes: um |Floating a| e uma expressão aritmética.\\
Assim sendo, teremos 4 casos, estando os casos das operações binárias e unárias divididos em 2 subcasos:

\begin{code}

g_eval_exp x (Left ())  = x
g_eval_exp x (Right(Left a)) = a
g_eval_exp x (Right(Right(Left (op, (a, b)))))
  |op == Sum = a + b
  |op == Product = a * b 
g_eval_exp x (Right(Right(Right (op, a))))
  |op == Negate = -a
  |op == E = expd a

\end{code}

\subsubsection{Alínea 3} \label{pg:P1.3}

A Simplificação das expressões é feita na função |clean|, cujo o nome sugestivo indicava que seria aqui que a expressão seria de facto simplificada. Podemos, desde já, também inferir que esta será
a parte \emph{divide} do nosso hilomorfismo.
Por outro lado, a função |gopt| poderia reaproveitar o código da alínea anterior(da função |g_eval_exp|), visto que esta função já tem definido o procedimento para simplificar expressões e só é corrida depois da |clean|.
Deste modo estariamos a efetuar cálculos somente se a |clean| não tivesse tirado já proveito dos elementos absorventes das operações.\\
Temos, então, que a função |gopt| representa o \emph{conquer} do hilomorfismo.\\
E que elementos podem ser estes?\\
No nosso caso identificamos 2 bastante conhecidos das propriedades matemáticas:\\

\begin{itemize}
\item No caso da operação binária da multiplicação, sabe-se que que qualquer valor/expressão multiplicad por 0(no caso do exercício |N 0|) resulta em 0.\\
\item No caso da operação unária do exponencial de base \emph{e}, sabemos que se o número de Euler/Nepper estiver elevado a 0, ou seja no caso deste exercício, a |N 0|,
terá como resultado o valor 1.
\end{itemize}


Temos, assim, reunidas as condições para afirmar que a |clean| de uma |ExpAr| pode ser dada por:

\begin{code}

clean (Bin Product (N 0) b) = i2(i1 0)
clean (Bin Product a (N 0)) = i2(i1 0)
clean (Un E (N 0)) = i2(i1 1)
clean exp = outExpAr exp

\end{code}

A |gopt|, como foi referido, tira aproveitamento da definição da |g_eval_exp|:

\begin{code}

gopt x = g_eval_exp x

\end{code}

Podemos também representar todo o hilomorfismo concebido com o diagrama  que se segue:\\

|j| representa |optmize_eval a|\\ \\

\xymatrix@@C=2.5cm{
     |Rational|
&
     |1 + ( A + ((BinOp >< (Rational >< Rational)) + (UnOp >< Rational)))|
           \ar[l]_-{|g = gopt a|}
\\
    |ExpAr A| 
           \ar[u]^-{|cata (g)|}      
           \ar@@/^1.005pc/[r]^-{|outExpAr|} _-\cong
&
    |1 + ( A + ((BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)))|
           \ar@@/^1.005pc/[l]^-{|inExpAr|}    
           \ar[u]_{|recExpAr| |cata (g)|} 
\\
    |ExpAr A| 
           \ar[u]^-{\ana{h}}      
           \ar[r]_-{|h = clean a|}
           \ar@@/^2.8pc/[uu]^-{|j|} 
&
    |1 + ( A + ((BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)))|              
           \ar[u]_{|recExpAr| \ana{h}} 
           \ar@@/^-13.5pc/[uu]_-{|F j|}
}

Relembrando agora a questão deixada no enunciado:\\
\textbf{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo 
em vez de utilizar um catamorfismo com um gene "inteligente"?}
Esta pergunta pode ser respondida comparando a alínea 2 e 3 do problema. Na primeira o gene do catamorfismo apenas simplifica
uma expressão aritmética - Por exemplo, |Bin Product a b| passa a |a * b|. Porém na segunda esta simplificação efetuada pelo gene do
catamorfismo apenas será feita se, previamente, o anamorfismo não tiver tirado proveito dos elementos absorventes de algumas operações:
|Bin Product 0 b| não passa a |0 * b|, mas adquire diretamente o seu resultado final: 0.\\


\subsubsection{Alínea 4} \label{pg:P1.4}

\quad Na resolução desta alínea, o mais importante foi perceber como é que, começando da expressão aritmética, poderiamos chegar ao par de |ExpAr|'s pretendido.\\

Ora, para tal é também essencial compreender que a regra da derivada do produto de 2 funções não só necessita da derivada de uma função como também necessita da 
função em si.\\

Analisando código, também isso uma parte essencial deste trabalho, podemos concluir que este gene terá o seu segundo elemento do par a ser selecionado pelo |p2| na 
assinatura da função |sd|. Visto que o objetivo da função |sd| é calcular a derivada, podemos definir o seu gene como uma função que devolve o valor da expressão como primeiro
elemento do par e o valor da derivada no segundo elemento do par(o valor desejado). O primeiro elemento do par é essecial para poder aplicar
corretamente a lei do produto.\\

\begin{code}

sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) 
    -> (ExpAr a, ExpAr a)
sd_gen  (Left()) = (X, (N 1))
sd_gen  (Right(Left a)) = ((N a), (N 0))
sd_gen  (Right (Right (Left (Sum, (a, b))))) = (Bin Sum (p1 a) (p1 b), Bin Sum (p2 a) (p2 b))
sd_gen  (Right (Right (Left (Product, (a, b))))) = (Bin Product (p1 a) (p1 b), Bin Sum fst_aux snd_aux)
    where fst_aux = Bin Product (p1 a) (p2 b)
          snd_aux = Bin Product (p2 a) (p1 b) 
sd_gen (Right (Right (Right (E, a)))) = ( Un E (p1 a) , Bin Product (Un E (p1 a)) (p2 a) )
sd_gen (Right (Right (Right (Negate, a)))) = (Un Negate (p1 a), Un Negate (p2 a))

\end{code}

O catamorfismo pode ser representado pelo seguinte diagrama:\\

Nota: |C| representa uma |ExpAr|.


\xymatrix@@C=2.5cm{
    |C| 
           \ar[d]_-{|cata (f)|}      
           \ar@@/^1.005pc/[r]^-{|outExpAr|} _-\cong
&
    |1 + ( A + ((BinOp >< (C >< C)) + (UnOp >< C)))|
           \ar@@/^1.005pc/[l]^-{|inExpAr|}    
           \ar[d]^{|recExpAr| |cata (f)|}  
\\
     |(C,C)|
&
     |1 + ( A + ((BinOp >< ((C,C) >< (C,C))) + (UnOp >< (C,C))))| 
           \ar[l]^-{|f = sd_gen c|}
}


\subsubsection{Alínea 5} \label{pg:P1.5}

\quad Este gene será bastante idêntico ao anterior, mas desta vez, tal como é dito no enunciado, ao invés de se manipular a expressão, 
esta será efetivamente calculada. O primeiro elemento do par será o valor da expressão, o segundo elemento será o valor da 
derivada da expressão.

\begin{code}

ad_gen pnt (Left()) = (pnt , 1)
ad_gen pnt (Right(Left a)) = (a, 0)
ad_gen pnt (Right(Right(Left (Sum, (a, b))))) = ((p1 a) + (p1 b) , (p2 a) + (p2 b) )
ad_gen pnt (Right(Right(Left (Product, (a, b))))) = ((p1 a) * (p1 b) , ((p1 a) * (p2 b)) + ((p2 a) * (p1 b)))
ad_gen pnt (Right(Right(Right (E, a)))) = ( expd(p1 a) , (p2 a)*expd((p1 a))) 
ad_gen pnt (Right(Right(Right (Negate, a)))) = (- (p1 a), -(p2 a))

\end{code}

O catamorfismo pode ser representado pelo seguinte diagrama:

\xymatrix@@C=2.5cm{
    |ExpAr A| 
           \ar[d]_-{|cata (f)|}      
           \ar@@/^1.005pc/[r]^-{|outExpAr|} _-\cong
&
    |1 + ( A + ((BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)))|
           \ar@@/^1.005pc/[l]^-{|inExpAr|}    
           \ar[d]^{|recExpAr| |cata (f)|}   
\\
     |(Rational,Rational)|
&
     |1 + ( A + ((BinOp >< ((Rational,Rational) >< (Rational,Rational))) + (UnOp >< (Rational,Rational))))|
           \ar[l]^-{|f = ad_gen a|}
}

\subsection*{Problema 2}

\quad Primeiramente, vamos tentar buscar uma relação entre o \emph{n}-ésimo valor de Catalon e o seu (\emph{n+1})-ésimo valor: \\

\begin{flalign}
        &\ \cfrac{C_{n+1}}{C_n} = \cfrac{\frac{(2(\emph{n}+1))!}{(\emph{n} + 2)!(\emph{n}+1)!}} {\frac{(2\emph{n})!}{(\emph{n}+1)!(\emph{n})!}}\notag\\
        \equiv&\notag\\
        &\ \cfrac{C_{n+1}}{C_n} = \frac{(2(n+1))!(\emph{n})!}{(\emph{n}+2)!(2\emph{n})!}\notag\\
        \equiv\notag\\  
        &\ \cfrac{C_{n+1}}{C_n} = \frac{(2\emph{n}+2)(2\emph{n}+1)(2\emph{n})!(\emph{n})!}{(\emph{n}+2)(\emph{n}+1)(\emph{n})!(2\emph{n})!}\notag\\
        \equiv\notag&\\
        &\ \cfrac{C_{n+1}}{C_n} = \frac{(2\emph{n}+2)(2\emph{n}+1)}{(\emph{n}+2)(\emph{n}+1)}\notag\\ 
        \equiv\notag&\\
        &\ \cfrac{C_{n+1}}{C_n} = \frac{2(\emph{n}+1)(2\emph{n}+1)}{(\emph{n}+2)(\emph{n}+1)}\notag\\
        \equiv\notag&\\
        &\ \cfrac{C_{n+1}}{C_n} = \frac{4\emph{n}+2}{\emph{n}+2}\notag\\
        \equiv\notag&\\
        &C_{n+1} = \frac{4\emph{n}+2}{\emph{n}+2} C_n\notag&
\end{flalign}\\

Tendo chegado a esta expressão, podemos agora dividir a equação entre 2 outras:\\

\begin{flalign}
&c(0) = 1&\notag\\
&c(n+1) = \frac{4\emph{n}+2}{\emph{n}+2} c(n)\notag&\\\notag\\\notag
&num(\emph{n}) = 4\emph{n} + 2&\notag\\
&num(0) = 2&\notag\\
&num(\emph{n+1}) = 4(\emph{n}+1) + 2 = 4 + num(\emph{n})\notag&\\\notag\\\notag
&den(\emph{n}) = \emph{n} + 2\notag&\\
&den(0) = 2&\notag\\
&den(\emph{n+1}) = (\emph{n}+3) = 1 + den(\emph{n})\notag&
\end{flalign}
\\

Pela \emph{regra da algibeira}, teremos:

\begin{code}

loop (a, num, den) = ( a * num `div` den , 4 + num, 1 + den)   
inic = (1, 2, 2)
prj  (a, b, c) = a 
\end{code}

por forma a que

\begin{code}
cat = prj . (for loop inic)

\end{code}
seja a função pretendida.

\subsection*{Problema 3}

\quad Em ambas as alíneas o procedimento inicial começou por ser a análise destas 2 funções tal como estão definidas nos anexos.

\subsubsection{Alínea 1} \label{pg:P3.1}

\quad No caso da |calcLine| não só foi importante analisar o código dos anexos, como também foi importante analisar o código da |prop_calcLine_def|.
Nesta, podemos constatar que é feito um |zipWithM| para a comparação com aquela que será a nossa definição. Ou seja, as 2 listas de racionais(|NPoint|'s) são
"zipadas" numa só e é aplicada a função |linear1d| com o respetivo \emph{time}.\\

O referido anteriormente levou-nos a crer que seria boa ideia, antes de partirmos para o catamorfismo, fazer um zip das listas(|NPoint|'s) recebidas 
de forma a posteriormente só ter de aplicar o catamorfismo a 1 lista, visto que não sabiamos se o podíamos fazer a 2 distintas.\\

O catamorfismo pode, portanto, ser representado pelo seguinte diagrama:

\xymatrix@@C=9cm{
    |(Rational,Rational)|^{*}
           \ar[d]_-{|cata (f)|}      
           \ar@@/^1.005pc/[r]^-{|outList|} _-\cong
&
    |1 + (Rational,Rational) >< (Rational,Rational)|^{*}
           \ar@@/^1.005pc/[l]^-{|inList|}    
           \ar[d]^{|recList| |cata (f)|} 
\\
     |NPoint|
&
     |1 + (Rational,Rational) >< (Rational,Rational)|
           \ar[l]^-{|f = h|}
}

A definição da função segue o raciocínio, tirando proveito deste diagrama e da definição dos anexos:

\begin{code}

calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine p q d = (cataList h) $ (zip p q) where    
    h (Left()) = []
    h (Right((a1,a2), t)) = (++) (singl $ (linear1d a1 a2 d)) t


\end{code}

\subsubsection{Alínea 2} \label{pg:P3.2}

\quad hilomorfismo

\xymatrix@@C=4cm{
     |NPoint|
&
     |NPoint + NPoint >< NPoint |
           \ar[l]_-{|g = alg|}
\\
    |NPoint >< NPoint|^{*}
           \ar[u]^-{|cata (g)|}      
           \ar@@/^1.005pc/[r]^-{|outLTree|} _-\cong
&
    |NPoint + (NPoint >< NPoint|^{*})^{2}
           \ar@@/^1.005pc/[l]^-{|inLTree|}    
           \ar[u]_{|recLTree| |cata (g)|} 
\\
    |NPoint|^{*}
           \ar[u]^-{\ana{h}}      
           \ar[r]_-{|h = coalg|}
           \ar@@/^4.8pc/[uu]^-{|deCasteljau|} 
&
    |NPoint + NPoint|^{*} |>< NPoint|^{*}            
           \ar[u]_{|recLTree| \ana{h}} 
           \ar@@/^-6.8pc/[uu]_-{|F deCasteljau|}
}

Inferimos, assim, a seguinte definição da função |deCasteljau|:\\\\\\\\


\begin{code}

deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau list time = hyloAlgForm alg coalg list where 
      coalg [] = i1 []
      coalg [a] = i1 a
      coalg list = i2 (p,q) where
          p = init list
          q = tail list
      alg (Left a)  = a
      alg (Right(p,q))  = calcLine p q time


coalgo [] = i1 []
coalgo [a] = i1 a
coalgo list = i2 (p,q) where
          p = init list
          q = tail list

algo (Left a)  = a
algo (Right(p,q))  = calcLine p q 1

\end{code}

O hilomorfismo será o hilomorfismo das |LTree|'s

\begin{code}
hyloAlgForm  = hyloLTree     

\end{code}


\subsection*{Problema 4}

Solução para listas não vazias:
\begin{code}

avg = p1.avg_aux 

\end{code}

Para usarmos um catamorfismo para listas não vazias vamos criar uma definição que não use listas vazias:


\begin{code}

out_ex4 [a] = i1(a)
out_ex4 (h:t) = i2(h,t)

\end{code}



\begin{code}
in_ex4 = either singl cons

\end{code}



\begin{code}
cataL_ex4 g = g . (recList (cataL_ex4 g)) . out_ex4 

\end{code}

\begin{eqnarray*}
\start
    |avg_aux = cata(either b q)|
%
\just\equiv{ |avg_aux:= split avg length; b = split b1 b2; q = split q1 q2| }
%
  |aplit avg length = cata (either (split b1 b2) (split q1 q2))|
%
\just\equiv{ Lei da troca }
%
  |split avg length = cata (split (either b1 q1) (either b2 q2))|
%
\just\equiv{ Fokkinga }
%
  \begin{lcbr}
    |f . in = (either b1 q1) . (split f g)|\\
    |g . in = (either b2 q2) . (split f g)|
  \end{lcbr}
%
\just\equiv{ |in| := |either singl cons|; |F f| := |id + id >< f| }
%
  \begin{lcbr}
    |avg . (either singl cons) = (either b1 q1) . (id + id >< (split avg length)|\\
    |length . (either singl cons) = (either b2 q2) . (id + id >< (split avg length)|
  \end{lcbr}
%
\just\equiv{ Fusão - + ; Absorção - +; Natural -id}
%
  \begin{lcbr}
    |either (avg . singl) (avg . cons) = either b1 (q1 . (split p1 (split (avg . p2) (length . p2))))|\\
    |either (length . singl) (length . cons) = either b2 (q2 . (split p1 (split (avg . p2) (length . p2))))|
  \end{lcbr}
% 
\just\equiv{ Eq - + }
%
  \begin{lcbr}
    \begin{lcbr}
      |avg . singl = b1| \\
      |avg . cons = q1 . (split p1 (split (avg . p2) (length . p2)))| 
    \end{lcbr} \\
    \begin{lcbr}
      |length . singl = b2|\\
      |length . cons = q2 . (split p1 (split (avg . p2) (length . p2)))|
    \end{lcbr}
  \end{lcbr}  
%
\just\equiv{ Def-comp(72) ; Introdução de variáveis ; Def - x ; Def-split ; Def-singl ; Def-cons}
% 
  \begin{lcbr}
    \begin{lcbr}
      |avg [x] = b1(x, xs)| \\
      |avg (x:xs) = q1(p1(x, xs), (avg(p2(x,xs)), (length(p2(x,xs))))) | 
    \end{lcbr} \\
    \begin{lcbr}
      |length [x] = b2(x, xs)|\\
      |length (x:xs) = q2 . (p1(x, xs), (avg(p2(x,xs)), (length(p2(x,xs))))) |
    \end{lcbr}
  \end{lcbr}
%
\just\equiv{ Def-proj ; avg[x] = x; length[x] = 1; length(x:xs) = succ . length(xs); Def-avg}
% 
  \begin{lcbr}
    \begin{lcbr}
      |x = b1| \\
      |((x + length * avg(xs)) / (length + 1)) = q1(x, (avg(xs), (length(xs)))) | 
    \end{lcbr} \\
    \begin{lcbr}
      |1 = q1|\\
      |succ . length(xs) = q2 (x, (avg(xs), (length(xs))))  |
    \end{lcbr}
  \end{lcbr}
%
\just\equiv{Simplificação}
%
  \begin{lcbr}
    \begin{lcbr}
      |b1 = id| \\
      |q1(x, (avg(xs), (length(xs)))) = ((x + length(xs) * avg(xs)) / (length(xs) + 1))|
    \end{lcbr} \\
    \begin{lcbr}
      |b2 = 1|\\
      |q2 = succ . p2. p2|
    \end{lcbr}
  \end{lcbr}
\qed
\end{eqnarray*}

Substindo os valores na expressão inicial e para código Haskell temos:



\begin{code}

avg_aux :: [Double] -> (Double, Double)
avg_aux = cataL_ex4 gene where
      gene = either (split id (const 1)) (split aux_split (succ . p2 . p2)) 
      aux_split (h, (a, l)) = (h + (l * a)) / (l + 1)

\end{code}



Solução para árvores de tipo \LTree:

\begin{eqnarray*}
\start
    |avg_aux = cata(either b q)|
%
\just\equiv{ |avg_aux:= split avg length; b = split b1 b2; q = split q1 q2| }
%
  |aplit avg length = cata (either (split b1 b2) (split q1 q2))|
%
\just\equiv{ Lei da troca }
%
  |split avg length = cata (split (either b1 q1) (either b2 q2))|
%
\just\equiv{ Fokkinga }
%
  \begin{lcbr}
    |f . in = (either b1 q1) . (split f g)|\\
    |g . in = (either b2 q2) . (split f g)|
  \end{lcbr}
%
\just\equiv{ |in| := |either Leaf Fork|; |F f| := id + f² }
%
  \begin{lcbr}
    |avg . (either Leaf Fork) = (either b1 q1) . (id + (split avg length) >< (split avg length))|\\
    |length . (either Leaf Fork) = (either b2 q2) . (id + (split avg length) >< (split avg length))|
  \end{lcbr}
%
\just\equiv{ Fusão - + ; Absorção - +; Natural -id; Eq - +}
%
  \begin{lcbr}
    \begin{lcbr}
      |avg . Leaf = b1| \\
      |avg . Fork = q1 . ((split avg length) >< (split avg length))| 
    \end{lcbr} \\
    \begin{lcbr}
      |length . Leaf = b2|\\
      |length . Fork = q2 . ((split avg length) >< (split avg length))|
    \end{lcbr}
  \end{lcbr}  
% 
\just\equiv{ Introdução de variáveis; Def-comp; Def-x; Def-split}
%
  \begin{lcbr}
    \begin{lcbr}
      |avg(Leaf(x)) = b1(x)| \\
      |avg(Fork((x,xs),(y,ys))) = q1((avg(x,xs),length(x,xs)), (avg(y,ys),length(y,ys)))| 
    \end{lcbr} \\
    \begin{lcbr}
      |length(Leaf(x)) = b2(x)| \\
      |length(Fork((x,xs),(y,ys))) = q2((avg(x,xs),length(x,xs)), (avg(y,ys),length(y,ys)))| 
    \end{lcbr}
  \end{lcbr}  
%
\just\equiv{Def-avg; Def-length; Simplificação}
% 
  \begin{lcbr}
    \begin{lcbr}
      |b1 = x| \\
      |q1((a1,a2), (b1,b2)) = (a1 * a2 + b1 * b2) /(a2 + b2) | 
    \end{lcbr} \\
    \begin{lcbr}
      |b2 = 1| \\
      |q2 = uncurry (+) . split (p2 . p1) (p2 . p2) | 
    \end{lcbr}
  \end{lcbr}  
%
\end{eqnarray*}

Substindo os valores na expressão inicial e para código Haskell temos:


\begin{code}

avgLTree :: LTree Double -> Double
avgLTree = p1.cataLTree gene
gene = either (split id (const 1)) (split aux_split f) where
    f = uncurry (+) . split (p2 . p2) (p2 . p1)
    aux_split ((a1,l1),(a2,l2)) = (a1 * l1 + a2 * l2) / (l1 + l2 )
    
\end{code}


%if False

--liftM2 (+) a b where
    --    a = p2 . p2
    --    b = p2 . p1 

--l :: LTree Double
--l = (Fork ((Fork (Leaf 6, Leaf 3), (Fork (Leaf 5, Leaf 2)))))

--k :: LTree Double
--k = (Fork ((Fork (Leaf 16, Leaf 13), (Fork (Leaf 15, Leaf 12)))))

--j :: LTree Double
--j = (Fork ((Fork (l, k), (Fork (Leaf 50, Leaf 20)))))

--teste :: LTree Double 
--teste = (Fork ((Fork (Leaf 10, Leaf 30), (Fork (Leaf 50, Leaf 20)))))

--impar :: LTree Double 
--impar = Fork(Fork(Leaf 1,Fork(Leaf 1, Leaf 3)),Leaf 5) 

%endif


\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}

module BTree

open Cp

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> i1()
    | Node (a,(t1,t2)) -> i2 (a,(t1,t2))

// (2) Ana + cata + hylo -------------------------------------------------------

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g = g << (recBTree (cataBTree g)) << outBTree

let rec anaBTree g = inBTree << (recBTree (anaBTree g) ) << g

let hyloBTree h g = cataBTree h << anaBTree g

// (3) Map ---------------------------------------------------------------------

//instance Functor BTree
//         where fmap f = cataBTree ( inBTree . baseBTree f id )
let fmap f = cataBTree ( inBTree << baseBTree f id )

// (4) Examples ----------------------------------------------------------------

// (4.0) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let inord x =
    let join (x , (l , r)) = l @ [x] @ r
    in (either nil join) x

let inordt x = cataBTree inord x

let preord x = 
    let f (x , (l , r)) = x :: l @ r
    in (either nil f) x

let preordt x = cataBTree preord x // pre-order traversal
    
let postordt x =
    let f (x , (l , r)) = l @ r @ [x]
    in cataBTree (either nil f) x

// (4.4) Quicksort -------------------------------------------------------------

let rec part p x =
    match x with
    | [] -> ([],[])
    | (h::t) -> if (p h) then let (s,l) = part p t in ((h::s),l) else let (s,l) = part p t in (s,(h::l))

let less h x = (if (x < h) then true else false)

let qsep x =
    match x with
    | [] -> i1()
    | (h::t) -> let (s,l) = part (less h) t in i2 (h,(s,l))

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let rec init x =
    match x with
    | [] -> []
    | (h::t) -> [h] @ (init t)

let rec last x =
    match x with
    | [a] -> a
    | (h::t) -> last t

let rec isOnList x =
    match x with
    | (b , []) -> false
    | (b , (h::t)) -> if (b = h) then true else isOnList (b , t)

let rec union x =
    match x with
    | ([] , a) -> a
    | (a , []) -> a
    | (a , b) -> if (isOnList ((last b) , a)) then (union (a , (init b))) else ((union (a , (init b))) @ [(last b)])

let headbtl a l = (a::l)

let tunion (a,(l,r)) = union ((List.map (headbtl a) l) , (List.map (headbtl a) r))

let traces x = cataBTree (either (konst [[]]) tunion) x
 
// (4.6) Towers of Hanoi -------------------------------------------------------

// pointwise:
// hanoi(d,0) = []
// hanoi(d,n+1) = (hanoi (not d,n)) ++ [(n,d)] ++ (hanoi (not d, n))

let strategy x =
    match x with
    | (d,0) -> i1 ()
    | (d,n) -> i2 ((n,d),((not d,(n-1)),(not d,(n-1))))

let present x = inord x

let hanoi x = hyloBTree present strategy x

// (5) Depth and balancing (using mutual recursion) --------------------------

let f((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))

let h(a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)

let baldepth x = 
    let g x = either (konst(true,1)) (h << (id><f)) x 
    in cataBTree g x

let balBTree x = (p1 << baldepth) x

let depthBTree x = (p2 << baldepth) x

// (6) Going polytipic -------------------------------------------------------

// natural transformation from base functor to monoid
//let tnat f =
//    let theta = uncurry (<>)
//    in either (konst mempty) (theta << (f >< theta))
//
// monoid reduction 
//
//let monBTree f = cataBTree (tnat f)

// alternative to (4.2) serialization ----------------------------------------

//let preordt' x = monBTree singl x

// alternative to (4.1) counting ---------------------------------------------

//let countBTree' x = monBTree (konst (Sum 1)) x

// (7) Zipper ----------------------------------------------------------------

//type Deriv<'a> = Dr of Bool 'a BTree<'a>
//
//type Zipper<'a> = [ Deriv<'a> ]
//
//let rec plug x t =
//    match x with
//    | [] -> t
//    | ((Dr false a l)::z) = Node (a,(plug z t,l))
//    | ((Dr true a r)::z) = Node (a,(r,plug z t))
//
//-------------------------- end of library ----------------------------------

\end{verbatim}

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}