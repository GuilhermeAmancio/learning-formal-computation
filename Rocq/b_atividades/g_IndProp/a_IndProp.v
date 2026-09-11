(* Require Import LFPTBR.pasta.arquivo. *)

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

Ambas as sequências partualmente chegam a 1. A pergunta feita por Collatz foi: 
A sequência que começa a partir de qualquer número natural positivo tem garantia 
de partualmente chegar a 1? 

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

Outra ideia seria expressar o conceito de 'partualmente alcançar 1 na 
sequência de Collatz' como uma propriedade de números definida recursivamente: 
Collatz_vale_para : nat → Prop. *)

Fail Fixpoint Collatz_vale_para (n : nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if par n then Collatz_vale_para (div2 n)
                   else Collatz_vale_para ((3 * n) + 1)
  end.

(* Esta função recursiva também é rejeitada pelo verificador de terminação, já que,
embora possamos em princípio convencer o Rocq de que div2 n é menor do que n, com 
certeza não podemos convencê-lo de que (3 × n) + 1 é menor do que n! Felizmente, 
há outra maneira de fazer isso: podemos expressar o conceito ''atinge 1 
partualmente na sequência de Collatz'' como uma propriedade de números definida 
indutivamente. Intuitivamente, essa propriedade é definida por um conjunto de 
regras:
               
-------------------------------------------- (Cvp_um) 
          Collatz_vale_para 1

par n = true   Collatz_vale_para (div2 n)  
-------------------------------------------- (Cvp_par) 
          Collatz_vale_para n


par n = false    Collatz_vale_para ((3 * n) + 1)
--------------------------------------------- (Cvp_impar)  
          Collatz_vale_para n 
 

Portanto, há três maneiras de provar que um número n partualmente atinge 1 na 
sequência de Collatz:
  - n é 1;
  - n é par e div2 n partualmente atinge 1;
  - n é ímpar e (3 × n) + 1 partualmente atinge 1.

Podemos provar que um número atinge 1 construindo uma derivação (finita) usando 
essas regras. Por exemplo, aqui está a derivação provando que 12 atinge 1 (onde 
omitimos as premissas de paridade):

                   -------------------- (Cvp_um)
                    Collatz_vale_para 1
                    -------------------- (Cvp_par)
                    Collatz_vale_para 2
                    -------------------- (Cvp_par)
                    Collatz_vale_para 4
                    -------------------- (Cvp_par)
                    Collatz_vale_para 8
                    -------------------- (Cvp_par)
                    Collatz_vale_para 16
                    -------------------- (Cvp_impar)
                    Collatz_vale_para 5
                    -------------------- (Cvp_par)
                    Collatz_vale_para 10
                    -------------------- (Cvp_impar)
                    Collatz_vale_para 3
                    -------------------- (Cvp_par)
                    Collatz_vale_para 6
                    -------------------- (Cvp_par)
                    Collatz_vale_para 12

Formalmente no Rocq, a propriedade Collatz_vale_para é definida indutivamente: *)

Inductive Collatz_vale_para : nat -> Prop :=
  | Cvp_um : Collatz_vale_para 1
  | Cvp_par (n : nat) : even n = true ->
                         Collatz_vale_para (div2 n) ->
                         Collatz_vale_para n
  | Cvp_impar (n : nat) : even n = false ->
                         Collatz_vale_para ((3 * n) + 1) ->
                         Collatz_vale_para n.


Example Collatz_vale_para_12 : Collatz_vale_para 12.
Proof.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_impar. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_impar. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_par. reflexivity. simpl.
  apply Cvp_um.
Qed.

(* A conjectura de Collatz afirma então que a sequência iniciada a partir de 
qualquer número positivo chega a 1: *)

Conjecture collatz : forall n, n <> 0 -> Collatz_vale_para n.

(* Se você conseguir provar essa conjectura, terá um futuro brilhante como 
teórico dos números! Mas não perca muito tempo com ela — ela está em aberto 
desde 1937. *)

(**************** Exemplo: Relação binária para comparar números ****************)

(* Uma relação binária em um conjunto X tem o tipo Rocq X -> X -> Prop. Esta é 
uma família de proposições parametrizada por dois elementos de X — ou seja, uma 
proposição sobre pares de elementos de X. 

Por exemplo, uma relação binária familiar em nat é le : nat → nat → Prop, a relação 
''menor ou igual a'', que pode ser definida indutivamente pelas duas regras 
seguintes: 

                     ---------------- (le_n)  
                         le n n	

                         le n m	
                     ---------------- (le_S) 
                         le n (S m)	

Estas regras dizem que existem duas maneiras de mostrar que um número é menor ou 
igual a outro: seja observando que eles são o mesmo número, ou, se o segundo 
tiver a forma S m, fornecendo evidências de que o primeiro é menor ou igual a m. 

Isso corresponde à seguinte definição indutiva em Rocq: *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).
Notation "n <= m" := (le n m) (at level 70).

(* Esta definição é um pouco mais simples e elegante do que a função booleana leb 
(menorigualb) que definimos em Básico. Como de costume, le e leb são equivalentes, 
e há um exercício sobre isso mais adiante. *)

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

(*************************** Exemplo: Fecho transitivo **************************)

(* Outro exemplo: O fecho transitivo de uma relação R é a menor relação que 
contém R e que é transitiva. Isso pode ser definido pelas duas regras seguintes: 

                      R x y	
                 ---------------- (passo_base)
                 fech_trans R x y	

        fech_trans R x y    fech_trans R y z	
        ------------------------------------ (passo_trans)  
                 fech_trans R x z

Em Rocq, isso se apresenta da seguinte forma: *)

Inductive fecho_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | passo_base (x y : X) :
      R x y ->
      fecho_trans R x y
  | passo_trans (x y z : X) :
      fecho_trans R x y ->
      fecho_trans R y z ->
      fecho_trans R x z.

(* Por exemplo, suponha que definamos uma relação ''genitor de'' em um grupo de 
pessoas... *)

Inductive Pessoa : Type := Sage | Cleo | Ridley | Moss.
Inductive genitor_de : Pessoa -> Pessoa -> Prop :=
  gd_SC : genitor_de Sage Cleo
| gd_SR : genitor_de Sage Ridley
| gd_CM : genitor_de Cleo Moss.

(* Neste exemplo, Sage é o genitor tanto de Cleo quanto de Ridley; e Cleo é o 
genitor de Moss. 

A relação genitor_de não é transitiva, mas podemos definir uma relação 
ancestral_de como seu fecho transitivo:*)

Definition ancestral_de : Pessoa -> Pessoa -> Prop :=
  fecho_trans genitor_de.

(* Aqui está uma derivação mostrando que Sage é um ancestral de Moss: 

 -------------------(gd_SC)        -------------------(gd_CM)
 genitor_de Sage Cleo              genitor_de Cleo Moss
---------------------(passo-base)  ---------------------(passo-base)
ancestral_de Sage Cleo             ancestral_de Cleo Moss
----------------------------------------------------(passo-trans)
                ancestral_de Sage Moss 

*)

Example ancestral_de_ex : ancestral_de Sage Moss.
Proof.
  unfold ancestral_de. apply passo_trans with Cleo.
  - apply passo_base. apply gd_SC.
  - apply passo_base. apply gd_CM. Qed.

(* O cálculo do fecho transitivo pode ser indecidível mesmo para uma relação R que 
seja decidível (por exemplo, a relação cms abaixo), portanto, em geral, não 
podemos esperar definir o fecho transitivo como uma função booleana. Felizmente, o 
Rocq nos permite definir o fecho transitivo como uma relação indutiva. 

O fecho transitivo de uma relação binária não pode, em geral, ser expresso em 
lógica de primeira ordem. A lógica do Rocq é, no entanto, muito mais poderosa e 
pode definir facilmente tais relações indutivas. *)

(********************* Exemplo: Fecho Reflexivo e Transitivo ********************)

(* Como outro exemplo, o fecho reflexivo e transitivo de uma relação R é a menor 
relação que contém R e que é reflexiva e transitiva. Isso pode ser definido pelas 
três regras seguintes (onde adicionamos uma regra de reflexividade a fecho_trans): 

                          R x y	
                ------------------------- (rt_passo)  
                 fecho_refl_trans R x y	
  	  
                ---------------------- (rt_refl)
                 fecho_refl_trans R x x	

            fecho_refl_trans R x y    fecho_refl_trans R y z	
         ----------------------------------------------------- (rt_trans)  
                          fecho_refl_trans R x z

*)

Inductive fecho_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | rt_passo (x y : X) :
      R x y ->
      fecho_refl_trans R x y
  | rt_refl (x : X) :
      fecho_refl_trans R x x
  | rt_trans (x y z : X) :
      fecho_refl_trans R x y ->
      fecho_refl_trans R y z ->
      fecho_refl_trans R x z.
  
(* Por exemplo, isso permite uma definição equivalente da conjectura de Collatz. 
Primeiro, definimos uma relação binária correspondente à ''função de passo de 
Collatz'' (csf): *)

Definition cs (n m : nat) : Prop := csf n = m.

(* Esta relação de passo de Collatz pode ser usada em conjunto com a operação de 
fecho reflexivo e transitivo para definir uma relação de múltiplos passos de 
Collatz (cms), expressando que um número n alcança outro número m em zero ou mais 
passos de Collatz *)

Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz' : forall n, n <> 0 -> cms n 1.

(* Esta relação cms definida em termos de fecho_refl_trans permite derivações mais 
interessantes do que as lineares da relação Collatz_vale_para definida 
diretamente: 

csf 16 = 8         csf 8 = 4           csf 4 = 2         csf 2 = 1
--------(rt_passo)  -------(rt_passo)  -------(rt_passo)  -------(rt_passo)
cms 16 8           cms 8 4              cms 4 2           cms 2 1
-------------------------(rt_trans)  ------------------------(rt_trans)
        cms 16 4                              cms 4 1
        ---------------------------------------------(rt_trans)
                           cms 16 1

*)

(* Exercício *)