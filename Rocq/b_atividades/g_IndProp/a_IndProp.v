Set Warnings "-notation-overridden".
Require Import Nat.

(******************* Proposições Indutivamente Definidas *********************)

(* No capítulo de Lógica, vimos várias maneiras de escrever proposições, 
incluindo conjunção, disjunção e quantificação existencial. Neste capítulo, 
trazemos mais uma nova ferramenta para o contexto: proposições definidas 
indutivamente. Para começar, alguns exemplos... *)

(*** Exemplo: A Conjectura de Collatz ***)

(* A Conjectura de Collatz é um famoso problema em aberto na teoria dos números. 
O seu enunciado é bastante simples. Primeiro, definimos uma função csf sobre 
números da seguinte forma (onde csf significa ''Collatz step function'' — função 
de passo de Collatz): *)

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

(* Em seguida, analisamos o que acontece quando aplicamos csf repetidamente a 
um determinado número inicial. Por exemplo, csf 12 é 6, e csf 6 é 3, portanto, 
ao aplicar csf repetidamente, obtemos a sequência 12, 6, 3, 10, 5, 16, 8, 4, 2, 
1. 

Da mesma forma, se começarmos com 19, obtemos a sequência mais longa 19, 58, 
29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1. 

Ambas as sequências eventualmente chegam a 1. A pergunta feita por Collatz foi: 
A sequência que começa a partir de qualquer número natural positivo tem garantia 
de eventualmente chegar a 1? 

Para formalizar essa questão no Rocq, podemos tentar definir uma função recursiva 
que calcule o número total de passos que tal sequência leva para alcançar 1. *)

Fail Fixpoint alcanca1_em (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + alcanca1_em (csf n).

(* Você pode escrever essa definição em uma linguagem de programação padrão. 
No entanto, essa definição é rejeitada pelo verificador de terminação do Rocq, 
já que o argumento para a chamada recursiva, csf n, não é 'obviamente menor' do 
que n.

De fato, esta não é apenas uma limitação sem propósito: as funções no Rocq devem 
ser totais para garantir a consistência lógica. 

Além disso, não podemos corrigir isso criando um verificador de terminação mais 
inteligente: decidir se essa função específica é total seria equivalente a 
resolver a Conjectura de Collatz!

Outra ideia seria expressar o conceito de 'eventualmente alcançar 1 na 
sequência de Collatz' como uma propriedade de números definida recursivamente: 
Collatz_vale_para : nat → Prop. *)