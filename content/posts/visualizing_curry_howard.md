---
title: 'Visualizing Curry-Howard Correspondence'
description: A tutorial on finding programs of proofs.
date: 2025-02-19T18:19:55-06:00
pubDate: null
draft: true
tags: ['logic', 'type theory', 'curry-howard']
---

<!-- hide Tex macros -->
> \[\def\tf{\vdash}\]
{ class=hidden }

The [Curry-Howard Correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) says that 
types of terms (programs) corresponds to theorems of some logic, and the programs corresponds to the proofs of 
the theorems. So when a proposition $\psi$ can be proven from a set of premises, then there is derivation of some term 
with type $\psi$ from a typing context, where the typing context contains a term of type $\phi$ for each premise $\phi$, and vice versa. 
Essentially,

\[
\begin{gather*}
    \phi_1, \phi_2, \dots, \phi_n \tf \psi\\
    \text{ iff }\\
    \alpha_1 : \phi_1, \alpha_2 : \phi_2, \dots, \alpha_n : \phi_n \tf \beta : \psi
\end{gather*}
\]

where a statement like $\alpha_1 : \phi_1$ says that $\alpha_1$ has type $\phi_1$.

Here, we will concern ourselves with intuitionist (propositional) logic and an equivalent type system, namely a 
type system with function types, product types, and sum types. Then, we will show some proofs to see, in action, 
what the correspondence looks like. At last, we will talk about strategies to come up with the proof term without 
writing out the proofs, and provide more examples of proof terms and interesting propositions. We assume some familiarity 
with either logical or typing derivations.

### Setup: Logic, Types, and Inference Rules

A reading of intuitionist logic ([BHK interpretation](https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)) goes: 
- $\phi \land \psi$ is true iff there is a proof of $\phi$ and a proof of $\psi$.
- $\phi \lor \psi$ is true iff there is a proof of $\phi$ or there is a proof of $\psi$.
- $\phi \to \psi$ is true iff there is a function that converts proofs of $\phi$ to proofs of $\psi$.
- $\neg \phi$ is true iff there is a "disproof" of $\phi$, meaning that a proof of $\phi$ can be converted to a proof of $\bot$ 
  (a proposition that is always false; a contradiction). So $\neg \phi \doteq \phi \to \bot$.
- There is no proof of $\bot$.
- There is a trivial proof of $\top$ (a proposition that is always true, opposite of $\bot$).

The correspondence of logical connectives and types looks like this:

{{% alignfig %}}
||Logic|Type|Term|
|:--:|:--:|:--:|:--:|
Conjunction / Product | $\phi \land \psi$ | $\phi \times \psi$ | $\langle x, y \rangle$ 
Disjunction / Sum | $\phi \lor \psi$ | $\phi + \psi$ | $x$ or $y$
Implication / Function | $\phi \to \psi$ | $\phi \to \psi$ | $\lambda x. M$
{{% /alignfig %}}

We explain each in turn:
- **Logical conjunction** corresponds to product types (pairs) since, to have some term of type $\phi \times \psi$ is to have a term of type $\phi$ and a term of type $\psi$.
  - The **empty product** $\langle \rangle$ has the empty product type $\top$, which corresponds to... you guessed it, $\top$.
- **Logical disjunction** corresponds to sum types (unions) since, to have some term of type $\phi + \psi$, we need either a term of type $\phi$ or a term of type $\psi$.
  - There is no term that has the **empty sum** type (if there were, what is its type?). We write $\bot$ for the empty sum type.
- **Implication** in logic corresponds to function types. A function mapping values from $\phi$ to $\psi$ has the type $\phi \to \psi$, which can be seen as mapping proofs of $\phi$ to proofs of $\psi$.
- **Negation** is a special instance of implication, since $\neg \phi \doteq \phi \to \bot$. So $\neg \phi$ means there is a function that transform proofs of $\phi$ to proofs of $\bot$.

From now on, we will use the logical symbols as both propositions and types. We will call the terms/programs *proof terms*. Next, we give the inference rules in our intuitionistic logical/typing proof system. 
If you are familiar with them, feel free to skip to the [next section](#example-proofs).

\begin{prooftree}
\AXC{$$}
\RL{Reflex./R}
\UIC{$\Gamma, x : \phi \tf x : \phi$}
\end{prooftree}

{{< columns >}}

{{% alignfig "center" %}}

\begin{prooftree}
\AXC{$\Gamma \tf x : \phi$}
\AXC{$\Gamma \tf y : \psi$}
\RL{$\land$I}
\BIC{$\Gamma \tf \langle x,y \rangle: \phi \land \psi$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \tf x : \phi$}
\RL{$\lor$I}
\UIC{$\Gamma \tf l \cdot x: \phi \lor \psi$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma, x : \phi \tf y : \psi$}
\RL{$\to$I}
\UIC{$\Gamma \tf \lambda x.\ y : \phi \to \psi$}
\end{prooftree}

\begin{prooftree}
\AXC{}
\RL{$\top$I}
\UIC{$\Gamma \tf \langle\rangle : \top$}
\end{prooftree}
{{% /alignfig %}}

--column-- 

{{% alignfig "center" %}}
\begin{prooftree}
\AXC{$\Gamma \tf \langle x,y \rangle: \phi \land \psi$}
\RL{$\land$E}
\UIC{$\Gamma \tf x: \phi$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \tf p : \phi \lor \psi$}
\AXC{$\Gamma, x_1 : \phi \tf q_1 : C$}
\AXC{$\Gamma, y_2 : \psi \tf q_2 : C$}
\RL{$\lor$E}
\TIC{$\Gamma \tf \text{case}\ p\ \{x_1 \Rightarrow q_1 \mid x_2 \Rightarrow q_2\} : C$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \tf f : \phi \to \psi$}
\AXC{$\Gamma \tf x : \phi$}
\RL{$\to$E}
\BIC{$\Gamma \tf f\ x : \psi$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \tf p : \bot$}
\RL{$\bot$E}
\UIC{$\Gamma \tf \text{abort}(p) : \phi$}
\end{prooftree}
{{% /alignfig %}}

{{< /columns >}}

Inference rules for negation falls out from inference rules for implication:

{{< columns >}}

{{% alignfig "center" %}}
\begin{prooftree}
\AXC{$\Gamma, x : \phi \tf y : \bot$}
\RL{$\neg$I}
\UIC{$\Gamma \tf \lambda x.\ y : \phi \to \bot$}
\end{prooftree}
{{% /alignfig %}}

--column--

{{% alignfig "center" %}}
\begin{prooftree}
\AXC{$\Gamma \tf f : \phi \to \bot$}
\AXC{$\Gamma \tf x : \phi$}
\RL{$\neg$E}
\BIC{$\Gamma \tf f\ x : \bot$}
\end{prooftree}
{{% /alignfig %}}

{{< /columns >}}

{{% accordion "Explanation of Inference Rules" false "theme_like" %}}
For each inference rule, if sentences above the line is true, then we can derive the sentence below the line. A proof utilizes any number of inference rules starting from the top with $\text{reflex.}$ rules, to end at the bottom with some
statement $\Gamma \tf x : \phi$. If you ignore every expression before $:$, then the inference rules are much like what you'd see in a Gentzen-style natural deduction systems (with some differences since we have $\Gamma$ here instead of rules that deal with assumptions).

There are two $\land$E rules; I have omitted the rule that derives $\Gamma \tf y : \phi$. 
Similarly, I have omitted the other $\lor$I rule that derives $\Gamma \tf r \cdot y : \phi \lor \psi$. The $l$ and $r$ in $\lor$I stands for "left" and "right". They record which side the proof of $\phi \lor \psi$ comes from.

For the $\lor$E rule, $\text{case}\ p\ \{x_1 \Rightarrow q_1 \mid x_2 \Rightarrow q_2\}$ is like a match/if-then-else statement that evaluates to $q_1$ or $q_2$ based on $p$'s actual type. This corresponds to proof by cases in logic, 
as the inference rule's name suggests.

$\to$I is conditional proof. It says that if $\psi$ is provable from assumptions $\Gamma$ and $\phi$, then $\phi \to \psi$ is provable from just $\Gamma$. This corresponds to introducing the $\lambda$ operator to bind $x$ and create a function. 
$\to$E, on the otherhand, is Modus Ponens. This corresponds to function application. We write $f x$ for $x$ applied to $f$ (with space inbetween) in the veins of languages like ML.

Lastly, $\top$ is always provable from any $\Gamma$ ($\langle\rangle$ is always well-typed). As for $\bot$, if it were ever to be derived, then any proposition $\phi$ can be derived because of $\bot$E (see [principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion)). 
Here, we use $\text{abort(p)}$ to signify that something has gone wrong with the type of program $p$.

{{% /accordion %}}

### Examples of Correspondences
Let's start simple. What is the proof of the principle of identity, $\phi \to \phi$? It would be a conditional proof that assumes there is a proof of $\phi$ and derives $\phi$. So the proof term for such a proof is the identity function, which takes a proof of something and returns a proof of that thing.

\begin{prooftree}
\AXC{}
\RL{Reflex.}
\UIC{$x : \phi \tf x : \phi$}
\RL{$\to$I}
\UIC{$\tf \lambda x.\ x : \phi \to \phi$}
\end{prooftree}

What about a proof of $\phi \to (\psi \to \phi)$? We would assume for conditional proof that $\phi$, then assume $\psi$, and derive $\phi$. From the previous example, we know that introducing a $\lambda$ function corresponds to introducing an assumption for conditional proof. So we need a function that takes a proof of $\phi$ and return a proof of $\psi \to \phi$, which is a function that takes a proof of $\psi$ and returns a proof of $\phi$. So the proof term is: [^1]

[^1]: : The body of a $\lambda$ function extends as far right as possible, so $\lambda x.\ M\ N$ means $(\lambda x. M\ N)$ and not $(\lambda x. M)\ N$.

\[\lambda x.\ \lambda y. x\]

We can verify that this is the case:

\begin{prooftree}
\AXC{}
\RL{Reflex.}
\UIC{$x : \phi, y : \psi \tf x : \phi$}
\RL{$\to$I}
\UIC{$x : \phi \tf \lambda y. x : \psi \to \phi$}
\RL{$\to$I}
\UIC{$\tf \lambda x.\ \lambda y. x : \phi \to (\psi \to \phi)$}
\end{prooftree}

Next up, let's look at the proof of contraposition, $(\phi \to \psi) \to (\neg\psi \to \neg\phi)$. To make things simpler, we first present a proof in natural deduction style:
{{% proof "Contraposition" %}}
||||
|:--|:---|:--|
|1. | $\phi \to \psi$ | Assume for conditional proof ($\lambda x$)|
|2. | $\neg \psi$ | Assume for conditional proof ($\lambda y$) |  
|3. | $\phi$ | Assume for proof by negation[^2] ($\lambda z$) |  
|4. | $\psi$ | Modus Ponens from 1 and 3 ($\to$E) |
|5. | $\bot$ | Contradiction from 2 and 4 ($\neg$E) |
|6. | $\neg \phi$ | Proof by negation, 3 ~ 5 ($\neg$I) |
|7. | $\neg \psi \to \neg \phi$ | Conditional proof, 2 ~ 6 ($\to$I) |
|8. | $(\phi \to \psi) \to (\neg \psi \to \neg \phi)$ | Conditional proof, 1 ~ 7 ($\to$I) |
{ .prooftable }
[^2]: Proof by negation assumes $\phi$, derive a contradiction, and proves $\neg\phi$. This may look like proof by contradiction, which is intuitionistically invalid, but it is not. Proof by contradiction assumes $\neg\phi$, derive a contradiction, and proves $\phi$. See [this](https://math.andrej.com/2010/03/29/proof-of-negation-and-proof-by-contradiction/) for an explanation of the differences.
{{% /proof %}}

Looking at line 4 and 5, we know that they corresponds to function applications because of the rules $\to$E and $\neg$E. What about the whole proof by negation (lines 3 ~ 5)? Here, we need an assumption of $\phi$ and a conclusion of $\bot$ to derive $\neg\phi$. But since $\neg\phi$ is defined as $\phi \to \bot$, proof by negation is just a function application! And that is exactly what the rule $\neg$I says. With all of that in mind, we arrive at the proof term:

\[
\lambda \overset{\overset{\phi \to \psi}{\uparrow}}{x}.\ 
\lambda \overset{\overset{\neg\psi}{\uparrow}}{y}.\ 
\textcolor{green}{\lambda} 
  \overset{\overset{\phi}{\uparrow}}{\textcolor{green}{z}}\textcolor{green}{.}\ 
    \underbrace{\textcolor{green}{y}\ \textcolor{green}{(x\ z)}}_{\bot}
\]

The part that's colored green is the proof terms for proof by negation. Using the inference rules we presented earlier, we can veryify that

\begin{prooftree}
\AXC{}
\RL{R}
\UIC{$x : \phi \to \psi, y : \neg\psi, z : \phi \tf y : \neg\psi$}
\AXC{}
\RL{R}
\UIC{$x : \phi \to \psi, y : \neg\psi, z : \phi \tf x : \phi \to \psi$}
\AXC{}
\RL{R}
\UIC{$x : \phi \to \psi, y : \neg\psi, z : \phi \tf z : \phi$}
\RL{$\to$E}
\BIC{$x : \phi \to \psi, y : \neg\psi, z : \phi \tf x\ z : \psi$} 
\RL{$\neg$E}
\BIC{$x : \phi \to \psi, y : \neg\psi, z : \phi \tf y\ (x\ z) : \bot$}
\RL{$\neg$I}
\UIC{$x : \phi \to \psi, y : \neg\psi \tf \lambda z.\ y\ (x\ z) : \neg \phi$}
\RL{$\to$I}
\UIC{$x : \phi \to \psi \tf \lambda y.\ \lambda z.\ y\ (x\ z) : \neg \psi \to \neg \phi$}
\RL{$\to$I}
\UIC{$\tf \lambda x.\ \lambda y.\ \lambda z.\ y\ (x\ z) : (\phi \to \psi) \to (\neg \psi \to \neg \phi)$}
\end{prooftree}
{ .yscroll }

You can see that each inference in the proof tree, from top to bottom, correponds to a line in the proof starting from line 4 (except for the R rules). 

### Coming Up with Proof Terms

