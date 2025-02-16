---
title: 'Deductions in Hilbert Systems'
date: 2024-04-30T19:51:40-05:00
pubDate: 2024-05-02
tags: ['logic', 'proof theory']
---

Hilbert systems are systems of deduction based on a large set of axioms and a minimal set of inference rules. Since deductions in Hilbert systems can be very hard to come up with, I will discuss some tips and tricks that I learned when I tried to solve this problem in Troelstra's *Basic Proof Theory*:[^0]

[^0]: Exercise 2.4.2D

> Prove that the following two sets of axioms are equivalent.[^1]  
> System $A$:
> 1. $P \imp (Q \imp P)$
> 2. $(P \imp Q \imp R) \imp (P \imp Q) \imp (P \imp R)$
> 
> System $B$:
> 
> 3. $A \imp (B \imp A)$ (identical to 1)
> 4. $(A \imp A \imp B) \imp (A \imp B)$ (Contraction)
> 5. $(A \imp B) \imp (C \imp A) \imp (C \imp B)$ (Pseudo-Transitivity)[^2]
> 6. $(A \imp B \imp C) \imp (B \imp A \imp C)$ (Permutation)
> 
> The only inference rules available are [Modus Ponens](https://en.wikipedia.org/wiki/Modus_ponens) (MP; also called $\imp$-Elimination).[^3]

[^1]: These are the axioms for the $\imp$ fragment of minimal logic (hence also valid in intuitionist and classical logic).
[^2]: We call this Pseudo-Transitivity (of $\imp$) because transitivity is just axiom 5 with the order of its antecedents flipped: $(C \imp A) \imp (A \imp B) \imp (C \imp B)$. Provided that we also have axiom 6 (permutation), we can straightforwardly derive the transitivity axiom.
[^3]: We will treat the axioms as axiom schemas, where $P,Q,R,A,B,C$ are schematic variables in the metalanguage. Equivalently, we can also treat them as axioms with propositional variables, and use the uniform substitution rule. So, for example, substituting $A$ for $P$ and $A \imp B$ for $Q$ in axiom 1, we get $A \imp ((A \imp B) \imp A)$.

Note that here, we use the convention that $\imp$ is right associative, meaning
> $A \imp B \imp C \equiv (A \imp (B \imp C))$.

We may drop or add parenthesis so long that it does not change the structure of the formulas. For a conditional of the form $\phi \imp (\psi \imp \chi)$, we say that the (first and second) **antecedents** are $\phi$ and $\psi$, and the **consequent** is $\chi$.

{{% accordion "Author's Note" false "success" %}}
As I was finishing up this post, I realized that axiom 5 and 6 have already been proved [on Wikipedia](https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_theorems_and_their_proofs). But the proof of axiom 6 utilizes the hypothetical syllogism metatheorem, whereas [our proof of axiom 6](#permutation-proof) will not have this dependency.
{{% /accordion %}}

#### Proving Principle of Identity
For practice, consider proving $A \imp A$ (the principle of identity) in the first system. How do we approach this? 

We start by fitting the formula into the last part of the axioms. We have two options:  
Try axiom 1: $(A \imp A) \imp\ ?\ \imp (A \imp A)$  
or axiom 2: $(A \imp\ ?\ \imp A) \imp\ (A \imp\ ?\ ) \imp (A \imp A)$

Axiom 1 isn't usually useful, because if we want to use Modus Ponens to get the final consequent, we must apply the antecedents in order, but its first antecedent is precisely what we want to prove!

So, let's go with axiom 2. What should we substitute in for the question mark? In order to use Modus Ponens, we know that the antecedents must be theorems. It is not hard to see, then, that if we substitute $A \rightarrow A$ itself, then both antecedents are theorems. So, we have the following proof:
{{% proof "$A \rightarrow A$" %}}
||
:--|-|:--
1\. $(A \imp (A \imp A) \imp A)$ $\imp (A \imp (A \imp A))$ $\imp (A \imp A)$ | | Axiom 2 ($P\equiv A$, $Q\equiv (A\imp A)$, $R\equiv A$)
2\. $A \imp (A \imp A) \imp A$ | | Axiom 1 ($P \equiv A$, $Q \equiv (A \imp A)$)
3\. $(A \imp (A \imp A)) \imp (A \imp A)$ | | MP (1, 2)
4\. $A \imp (A \imp A)$ | |  Axiom 1 ($P,Q \equiv a$)
5\. $A \imp A$ | | MP (3, 4)
{ .prooftable }
{{% /proof %}}

We are now ready to tackle the problem presented earlier. Although there is a solution in the book, it utilizes the fact that the first system was proved to be equivalent a Natural Deduction system. Here, we present a more direct proof by deriving each axiom from the other system.

### Proving System B from System A
We prove that axioms 4, 5, and 6 are provable from 1 and 2. 

#### Contraction (Axiom 4)
> **Contraction**: $(A \imp A \imp B) \imp (A \imp B)$

Contraction seems easy to prove, as it fits the last part of axiom 2 (Let $P$ be $A$, $Q$ be $A\imp B$, and $R$ be $B$). Once we see that, we almost have a proof:
{{% proof "Axiom 4" "sketch" %}}
||
:--|-|:--
1\. $(A \imp (A \imp B) \imp B) \imp (A \imp (A \imp B)) \imp (A \imp B)$ || Axiom 2
2\. $A \imp (A \imp B) \imp B$ || ??
3\. $(A \imp (A \imp B)) \imp (A \imp B)$ || MP (1,2)
{.prooftable}
{{% /proof %}}

But we need to fill in the rule at line 2. We know we are on the right track because $A \imp (A \imp B) \imp B$ looks provable——it is just a conditional form of Modus Ponens! 
{{% proof "$A \imp ((A \imp B) \imp B)$" %}}
||
:--|-|:--
1\. $((A \imp B) \imp A \imp B)$ $\imp ((A \imp B) \imp A)$ $\imp ((A \imp B) \imp B)$ || Axiom 2 ($P\equiv (A \imp B)$)
2\. $(A \imp B) \imp (A \imp B)$ || From $A \imp A$
3\. $((A \imp B) \imp A) \imp ((A \imp B) \imp B)$ || MP (1,2)
4\. $A \imp ((A \imp B) \imp A)$ || Axiom 1
5\. $((A \imp B) \imp A) \imp ((A \imp B) \imp B)$ $\imp (A \imp ((A \imp B) \imp A))$ $\imp (A \imp ((A \imp B) \imp B))$ || Axiom 5!!
6\. $(A \imp ((A \imp B) \imp A))$ $\imp (A \imp ((A \imp B) \imp B))$ || MP (3,5)
6\. $A \imp ((A \imp B) \imp B)$ || MP (4,6)
{ .prooftable }
{{% /proof %}}

We start the proof by observing that $(A\imp B)\imp B$ fits the consequent of axiom 2. This may seem weird, because the first $A$ of $A \imp ((A \imp B) \imp B)$ is not part of the instantiated axiom, but it works out if we have proven axiom 5 already (line 5). We will do that now.

#### Pseudo-Transitivity (Axiom 5)
> **Pseudo-Transitivity**: $(A \imp B) \imp (C \imp A) \imp (C \imp B)$

Plugging this in to axiom 2, we have (Let $P$ be $A \imp B$ and $R$ be the rest):  
$((A \imp B) \imp\ ?\ \imp ((C \imp A) \imp (C \imp B)))$ $\imp ((A \imp B) \imp\ ?\ )$ $\imp ((A \imp B) \imp ((C \imp A) \imp (C \imp B)))$

When thinking about what to substitute in for the question mark, we need a crucial trick:[^4]
> **VC** Rule: If $S$ is proven, then we can derive $T \imp S$ (for any $T$)
[^4]: Since the proof of it is really simple, we leave it to the reader.

So let $?$ be $(C \imp A \imp B)$. Then the first antecedent becomes:  
$((A \imp B) \imp\ (C \imp A \imp B) \imp ((C \imp A) \imp (C \imp B)))$  
Since $(C \imp A \imp B) \imp ((C \imp A) \imp (C \imp B))$ is a theorem (axiom 2), the first antecedent is provable after an application of *VC*. The second antecedent becomes an instance of axiom 1:
$(A \imp B) \imp  (C \imp A \imp B)$

Here's the full proof:

{{% proof "Axiom 5" %}}
|||
|:--|-|:--|
1\. $((A \imp B) \imp (C \imp A \imp B) \imp ((C \imp A) \imp (C \imp B)))$ $\imp ((A \imp B) \imp (C \imp A \imp B))$ $\imp ((A \imp B) \imp ((C \imp A) \imp (C \imp B)))$ || Axiom 2 ($Q\equiv (C \imp A \imp B)$)
2\. $(C \imp A \imp B) \imp ((C \imp A) \imp (C \imp B))$ || Axiom 2
3\. $(A \imp B) \imp (C \imp A \imp B) \imp ((C \imp A) \imp (C \imp B))$ || VC (2)
4\. $((A \imp B) \imp (C \imp A \imp B))$ $\imp ((A \imp B) \imp ((C \imp A) \imp (C \imp B)))$ || MP (1,3)
5\. $(A \imp B) \imp (C \imp A \imp B)$ || Axiom 1
6\. $(A \imp B) \imp ((C \imp A) \imp (C \imp B))$ || MP (4,5)
{ .prooftable }
{{% /proof %}}

#### Permutation (Axiom 6) {#permutation-proof}
> **Permutation**: $(A \imp B \imp C) \imp (B \imp A \imp C)$

It is obvious that we should use axiom 2:  
$((A \imp B \imp C) \imp\ ? \ \imp (B \imp A \imp C))$ $\imp ((A \imp B \imp C) \imp\ ? \ )$ $\imp (A \imp B \imp C) \imp (B \imp A \imp C)$

We will substitute $?$ with $(B \imp A \imp B)$. Why? Consider the two antecedents:  
$(A \imp B \imp C) \imp (B \imp A \imp B) \imp (B \imp A \imp C)$  
$(A \imp B \imp C) \imp (B \imp A \imp B)$  
We can straightforwardly prove the second antecedent by the *VC* rule, because $(B \imp A \imp B)$ is already a theorem. What about the first antecedent? Notice that the following two formulas are instantiations of axiom 5 (which we have already proved) and axiom 2, respectively:  
$((A \imp B) \imp (A \imp C)) \imp (B \imp A \imp B) \imp (B \imp A \imp C)$  
$(A \imp B \imp C) \imp (A \imp B) \imp (A \imp C)$  
And if we use axiom 5 on these two formulas, we immediate get the first antecedent.

Let $\phi$ be $(B \imp A \imp B) \imp (B \imp A \imp C)$.
{{% proof "Axiom 6" %}}
||
:--|-|:--
1\. $((A \imp B \imp C) \imp \phi)$ $\imp ((A \imp B \imp C) \imp (B \imp A \imp B))$ $\imp (A \imp B \imp C) \imp (B \imp A \imp C)$ || Axiom 2
2\. $((A \imp B) \imp (A \imp C)) \imp \phi$ || Axiom 5
3\. $(A \imp B \imp C) \imp (A \imp B) \imp (A \imp C)$ || Axiom 2
4\. $(A \imp B \imp C) \imp \phi$ || Pseudo-Transitivity (2,3)
5\. $((A \imp B \imp C) \imp (B \imp A \imp B))$ $\imp (A \imp B \imp C) \imp (B \imp A \imp C)$ || MP (1,5)
6\. $B \imp A \imp B$||Axiom 1
7\. $(A \imp B \imp C) \imp (B \imp A \imp B)$||VC (6)
8\. $(A \imp B \imp C) \imp (B \imp A \imp C)$||MP (5,7)
{.prooftable}
{{% /proof %}}

Note that I have omitted a few steps by using Pseudo-Transitivity (axiom 5) as a derived rule.

### Proving System A from System B
We prove that axiom 2 is derivable from axiom 4~6. This direction of the proof is relatively easier because we have more axioms to work with. First, let us first prove this derived rule:
> **Transitivity\***: Given $P \imp Q \imp R$ and $R \imp D$, we can derive $P \imp Q \imp D$
{{% proof "Transitivity\*" %}}
|||
|:--|-|:--|
1\. $P \imp Q \imp R$||Premise
2\. $R \imp D$||Premise
3\. $((Q \imp R) \imp (Q \imp D))$ $\imp (P \imp Q \imp R)$ $\imp (P \imp Q \imp D)$||Axiom 5 ($C \equiv P$)
4\. $(R \imp D) \imp (Q \imp R) \imp (Q \imp D)$||Axiom 5 ($C \equiv Q$)
5\. $(Q \imp D) \imp (Q \imp D)$||MP (2,4)
6\. $(P \imp Q \imp R) \imp (P \imp Q \imp D)$||MP (3,5)
7\. $(P \imp Q \imp D)$||MP (1,6)
{ .prooftable }
{{% /proof %}}

Now that we have this rule under our belt, we can prove axiom 2. Let $\psi$ be $(Q \imp P \imp R) \imp (P \imp Q) \imp (P \imp R)$. 
{{% proof %}}
|||
|:--|-|:--|
1\. $\psi \imp ((P \imp Q \imp R) \imp (Q \imp P \imp R))$ $\imp ((P \imp Q \imp R) \imp (P \imp Q) \imp (P \imp R))$||Axiom 5 ($A \equiv (Q \imp P \imp R),$ $C \equiv (P \imp Q \imp R)$)
2\. $(Q \imp (P \imp R)) \imp (P \imp Q) \imp (P \imp (P \imp R))$||Axiom 5 ($C \equiv P$)
3\. $(P \imp (P \imp R)) \imp (P \imp R)$||Axiom 4
4\. $\psi$||Transitivity\* (2,3)
5\. $((P \imp Q \imp R) \imp (Q \imp P \imp R))$ $\imp ((P \imp Q \imp R) \imp (P \imp Q) \imp (P \imp R))$||MP (1,4)
6\. $(P \imp Q \imp R) \imp (Q \imp P \imp R)$||Axiom 6
7\. $(P \imp Q \imp R) \imp (P \imp Q) \imp (P \imp R)$||MP (5,6)
{ .prooftable }
{{% /proof %}}

The first step has axiom 2 as its consequent, and its second antecedent is a straighforward application of the permutation axiom. The first consequent took more work to prove; it required recognizing that the second step is possible from axiom 5, and that we can utilize Contraction and Transitivity\*.

### Lessons
To sum it up, we showed that the usual first step is to find an axiom whose consequent fits the goal, then consider filling in the $?$ in a way that makes each antecedent provable. In the case where an antecedent is not straightforwardly provable, we also utilizes other tricks like *VC*, (pseudo-)transitivity, and other already-proven axioms. The order of proving axioms is important; we had to recognize that we need axiom 5 to prove axiom 4 and 6, and whenever we search for axioms to fit the goal, we want to include the ones we have already proven.