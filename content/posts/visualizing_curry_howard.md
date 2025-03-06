---
title: 'Visualizing Curry-Howard Correspondence'
description: A tutorial on finding programs of proofs.
date: 2025-02-19T18:19:55-06:00
pubDate: 2025-03-02
tags: ['logic', 'type theory', 'curry-howard']
---

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
If you are familiar with them, feel free to skip to the [next section](#examples-of-correspondences).

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
\AXC{$\Gamma \tf x: \phi \land \psi$}
\RL{$\land$E}
\UIC{$\Gamma \tf x \cdot 1: \phi$}
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

There are two $\land$E rules; I have omitted the rule that derives $\Gamma \tf x \cdot 2 : \phi$. 
Similarly, I have omitted the other $\lor$I rule that derives $\Gamma \tf r \cdot y : \phi \lor \psi$. The $l$ and $r$ in $\lor$I stands for "left" and "right". They record which side the proof of $\phi \lor \psi$ comes from.

For the $\lor$E rule, $\text{case}\ p\ \{x_1 \Rightarrow q_1 \mid x_2 \Rightarrow q_2\}$ is like a match/if-then-else statement that evaluates to $q_1$ or $q_2$ based on $p$'s actual type. This corresponds to proof by cases in logic, 
as the inference rule's name suggests.

$\to$I is conditional proof. It says that if $\psi$ is provable from assumptions $\Gamma$ and $\phi$, then $\phi \to \psi$ is provable from just $\Gamma$. This corresponds to introducing the $\lambda$ operator to bind $x$ and create a function. 
$\to$E, on the otherhand, is Modus Ponens. This corresponds to function application. We write $f x$ for $x$ applied to $f$ (with space inbetween) in the veins of languages like ML.

Lastly, $\top$ is always provable from any $\Gamma$ ($\langle\rangle$ is always well-typed). As for $\bot$, if it were ever to be derived, then any proposition $\phi$ can be derived because of $\bot$E (see [principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion)). 
Here, we use $\text{abort(p)}$ to signify that something has gone wrong with the type of program $p$.

{{% /accordion %}}

### Examples of Correspondences
In all of the examples below, we will consider proofs of logical theorems (of intuitionist logic), which are propositions provable from no premises ($\Gamma = \varnothing$).
We do this mainly because the theorems are interesting, as many of them (particularly in [the next section](#coming-up-with-proof-terms)) tell us how strong, or weak, intuitionist logic
is compared to classical logic that most people are familiar with.

Let's start simple. What is the proof of **the principle of identity**, $\phi \to \phi$? It would be: Assume $\phi$ is true, then $\phi$, therefore, $\phi \to \phi$.
By assuming the antecedent of a conditional and deriving the consequent, we have proved the conditional. This is called a conditional proof. 
Equivalently, by taking a proof term for the antecedent and returning a proof term for the consequent (in a function), we have a proof term for the conditional.

So the proof term the principle of identity is the identity function, which takes a proof of something and returns a proof of the same thing.

\begin{prooftree}
\AXC{}
\RL{Reflex.}
\UIC{$x : \phi \tf x : \phi$}
\RL{$\to$I}
\UIC{$\tf \lambda x.\ x : \phi \to \phi$}
\end{prooftree}

From this simple example, we know that conditional proofs corresponds to introducing a $\lambda$ function in $\to$I.

What about a proof of $\phi \to (\psi \to \phi)$? We would assume for conditional proof that $\phi$, then assume $\psi$, and derive $\phi$. So we need a function that takes a proof of $\phi$ and return a proof of $\psi \to \phi$, which is a function that takes a proof of $\psi$ and returns a proof of $\phi$. So the proof term is: [^1]

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

Next up, let's look at **double negation introduction** (DNI):

\[
  \begin{gather*}
    \phi \to \neg \neg \phi\\
    \equiv\\ 
    \phi \to ((\phi \to \bot) \to \bot) .
  \end{gather*}  
\]

To prove DNI, we would first assume $\phi$. Then since we want to derive $(\phi \to \bot) \to \bot$, we assume $\phi \to \bot$ then derive $\bot$ using $\to$E on the two assumptions.
From the previous example, we know that these conditional proofs comes from introducing a $\lambda$. We also know by looking at $\to$E that it corresponds to a function application.
So the proof term is

\[
  \lambda \overset{\overset{\phi}{\uparrow}}{x}.\ 
  \lambda \overset{\overset{\mathclap{\phi \to \bot}}{\uparrow}}{y}.\ 
  y\ x
\]

We can easily verify that

\[
\begin{prooftree}
\AXC{}
\RL{R}
\UIC{$x : \phi, y : \neg \phi \tf y :\neg \phi$}
\AXC{}
\RL{R}
\UIC{$x : \phi, y : \neg \phi \tf x : \phi$}
\RL{$\neg$E}
\BIC{$x : \phi, y : \neg \phi \tf y\ x : \bot$}
\RL{$\neg$I}
\UIC{$x : \phi \tf \lambda y.\ y\ x : \neg \neg \phi$}
\RL{$\to$I}
\UIC{$\tf \lambda x.\ \lambda y.\ y\ x : \phi \to \neg \neg \phi$}
\end{prooftree}
\]

### Coming Up with Proof Terms

It would be nice to be able to come up with the proof terms without having to write down the full proof. This is not hard to do especially
if the proof does not require any creativity. 

For example, the proof term for **the principle of noncontradiction**,

\[
  \begin{gather*}
    \neg(\phi \land \neg\phi)\\
    \equiv\\ 
    (\phi \land (\phi \to \bot)) \to \bot ,
  \end{gather*}  
\]

is quite simple. Within the conditional proof/$\lambda$ function, we have the assumption $\phi \land (\phi \to \bot)$. To get the proof term of $\bot$, we just apply the right side of the conjunction with the left side within the $\lambda$ function:

\[
  \lambda \overset{\mathclap{\overset{\phi \land (\phi\to\bot)}{\uparrow}}}{x}.\ 
  (x \cdot 2)\ (x \cdot 1) .
\]

Notation wise, when dealing a conjunction $y : \phi \land \psi$, we write $y \cdot 1$ to get the the proof term for $\phi$ and $y \cdot 2$ to get the proof term for $\psi$.

Let's look at **contraposition**, 

\[
  \begin{gather*}
    (\phi \to \psi) \to (\neg\psi \to \neg\phi)\\
    \equiv\\ 
    (\phi \to \psi) \to ((\psi \to \bot) \to (\phi \to \bot)) .
  \end{gather*}  
\]

It might not be obvious what the proof term is at this point. To make things simpler, we first present a proof in natural deduction style:
{{% proof "Contraposition" %}}
||||
|:--|:---|:--|
|1. | $\phi \to \psi$ | Assume for conditional proof ($\lambda x$)|
|2. | $\neg \psi$ | Assume for conditional proof ($\lambda y$) |  
|3. | $\phi$ | Assume for proof by negation ($\lambda z$) |  
|4. | $\psi$ | Modus Ponens from 1 and 3 ($\to$E) |
|5. | $\bot$ | Contradiction from 2 and 4 ($\neg$E) |
|6. | $\neg \phi$ | Proof by negation, 3 ~ 5 ($\neg$I) |
|7. | $\neg \psi \to \neg \phi$ | Conditional proof, 2 ~ 6 ($\to$I) |
|8. | $(\phi \to \psi) \to (\neg \psi \to \neg \phi)$ | Conditional proof, 1 ~ 7 ($\to$I) |
{ .prooftable }
{{% /proof %}}

Note that we used an inference called proof by negation,[^2] which derives $\neg\phi$ by assuming of $\phi$ and concluding in $\bot$. How is this valid?
Well, since $\neg\phi$ is defined as $\phi \to \bot$, proof by negation is just a special instance of a conditional proof ($\to$I)!
Similarly, line 5 is just a special case of a $\to$E. 

Here is an informal way of converting a proof in the style above to its proof terms:
> 1. When you see an assumption, introduce a lambda function, then move into the scope of the lambda function.
> 2. When an assumption is no longer needed (line 5, 6, or 8 above), move outside of the scope of the lambda function.
> 3. The rest of the steps consists to using the relevant rules for the inferences involved. For example, a $\to$E and $\neg$E means function application.

With all of that in mind, we arrive at the proof term:

[^2]: This may look like proof by contradiction, which is intuitionistically invalid, but it is not. 
Proof by contradiction assumes $\neg\phi$, derive $\bot$, and proves $\phi$. See [this](https://math.andrej.com/2010/03/29/proof-of-negation-and-proof-by-contradiction/) for an explanation of the differences.

\[
  \lambda \overset{\overset{\mathclap{\phi \to \psi}}{\uparrow}}{x}.\ 
  \lambda \overset{\overset{\neg\psi}{\uparrow}}{y}.\ 
  \textcolor{green}{\lambda} 
    \overset{\overset{\phi}{\uparrow}}{\textcolor{green}{z}}\textcolor{green}{.}\ 
      \underbrace{\textcolor{green}{y}\ \textcolor{green}{(x\ z)}}_{\bot} .
\]

The part that's colored green is the proof by negation. I have included the full proof below for a sanity check.

{{% accordion "Sanity Check: Contraposition" true "positive" %}}
Using the inference rules we presented earlier, we can veryify that

\[
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
\end{prooftree}\]

You can see that each inference in the proof tree, from top to bottom, correponds to a line in the proof starting from line 4 (except for the R rules). 
{{% /accordion %}}

Before we move on to harder proofs, let us consider another easy example. This time it's a direction of **De Morgan**'s,[^3]
[^3]: The reverse direction is not intuitionistically valid.

\[
  \begin{gather*}
    (\neg \phi \lor \neg \psi) \to \neg (\phi \land \psi)\\
    \equiv\\ 
    ((\phi \to \bot) \lor (\psi \to \bot)) \to ((\phi \land \psi) \to \bot) .
  \end{gather*}  
\]

After assuming the two antecedents for conditional proof ($\to$I) and proof by negation ($\neg$I), respectively, 
we have to utilize a proof by cases on the first assumption, which corresponds to the $\text{case}$ syntax we presented earlier. 
Within each case, we apply part of the second assumption to get $\bot$. The proof term is then:

\[
  \begin{align*}
    & \lambda d.\ \lambda p.\ \text{case}\ d\ \{l\cdot \overset{\overset{\mathclap{\phi \to \bot}}{\uparrow}}{d_1} \hookrightarrow d_1\ (p\cdot 1) \mid 
     r\cdot \overset{\overset{\mathclap{\psi \to \bot}}{\uparrow}}{d_2} \hookrightarrow d_2\ (p\cdot 2)\} \\ 
    &: (\underbrace{(\phi \to \bot) \lor (\psi \to \bot)}_d) \to (\underbrace{(\phi \land \psi)}_p \to \bot) .
  \end{align*}
\]

#### Getting Creative

But not all proofs are mechanical like the ones we've considered. For example, think about how you would prove **triple negation elimination**, 

\[
  \begin{gather*}
    \neg\neg\neg\phi \to \neg\phi\\
    \equiv\\ 
    (((\phi \to \bot) \to \bot) \to \bot) \to (\phi \to \bot) .
  \end{gather*}  
\]

What happens after you have assumed $\neg\neg\neg\phi$ and $\phi$? It seems like there is no inference rule we can use on the assumptions 
that would get us $\bot$. But recall our discussion about proof by negations. If we assume $\neg\phi$, then we immediately see a contradiction, which gets
us $\neg\neg\phi$ by a proof by negation. Then that again contradicts with $\neg\neg\neg\phi$, which gets us $\bot$ by $\neg$E.
So the proof term is:

\[
  \begin{align*}
    &\lambda t.\ \lambda p.\ t\ (\lambda \overset{\overset{\mathclap{\phi\to\bot}}{\uparrow}}{n}.\ n\ p) \\
    &: \underbrace{(((\phi \to \bot) \to \bot) \to \bot)}_{t} \to (\underset{\underset{p}{\downarrow}}{\phi} \to \bot) .
  \end{align*}
\]

So we use $\lambda t$ for conditional proof and $\lambda p$, $\lambda n$ for proofs by negation.

I hope that you are more comfortable with coming up with proof terms by now, as we will consider a more challenging task: to provide proof terms for 
what I call "**doubly negated excluded middle**":[^4]

[^4]: Famously, excluded middle ($\phi \lor \neg\phi$) is not provable in intuitionist logic (nor is double negation elimination, $\neg\neg\phi \to \phi$). But the double negated version of excluded middle is, and so is triple negation elimination, as we saw earlier.

\[
  \begin{gather*}
    \neg\neg(\phi \lor \neg\phi)\\
    \equiv\\ 
    ((\phi \lor (\phi \to \bot)) \to \bot) \to \bot .
  \end{gather*}  
\]

It seems like we would be stuck immediately after starting a proof by negation. The trick is to do two proof by negations, one by assuming $\neg(\phi \lor \neg\phi)$
and the other $\neg\phi$. I find it easier to write out the proof in natural deduction style:
{{% proof %}}
||||
|:--|:---|:--|
|1. | $\neg(\phi \lor \neg\phi)$ | Assume for proof by negation ($\lambda x$)|
|2. | $\phi$ | Assume for proof by negation ($\lambda y$) |  
|3. | $\phi \lor \neg\phi$ | Disjunction Introduction from 2 ($\lor$I) |  
|4. | $\bot$ | Contradiction from 1 and 3 ($\neg$E) |
|5. | $\neg\phi$ | Proof by negation, 2 ~ 4 ($\neg$I) |
|6. | $\phi \lor \neg \phi$ | Disjunction Introduction from 5 ($\lor$I) | 
|7. | $\bot$ | Contradiction from 1 and 6 ($\neg$E) |
|8. | $\neg\neg(\phi \lor \neg\phi)$ | Proof by negation, 1 ~ 7 ($\neg$I) |
{ .prooftable }
{{% /proof %}}

We can then get the proof term by reading it off the proof :

\[
  \begin{align*}
    & \lambda k.\ 
      \underbrace{k\ (r \cdot 
        (\lambda \overset{\overset{\phi}{\uparrow}}{p}.\ 
          k\ (\overbrace{l \cdot p)}^{\mathclap{\text{first } \phi \lor (\phi \to \bot)}}))
          }_{\text{second } \phi \lor (\phi \to \bot)} \\
    & : \underbrace{((\phi \lor (\phi \to \bot)) \to \bot)}_{k} \to \bot
  \end{align*}
\]

The use of $l\cdot p$ and $r \cdot \dots$ introduces a sum type $\phi \lor \neg\phi$ from one of $\phi$ or $\neg\phi$, which corresponds to disjunction introduction, the lambda functions corresponds to proofs by negation,
and the two function applications of $k$ corresponds to $\neg$E. So for example, $\lambda p. k\ (l \cdot p)$ has the type $\phi \to \bot$, since its function body has type $\bot$ (corresponding to line 4 above). After some squinting, we can see that
everything in the proof is accounted by the proof terms.

In summary, we looked at different examples to get a feel for the correspondences between logical and typing inference rules, then we gradually move away from typing derivations and just look at the inference rules to figure out the proof terms. Lastly, when necessary, we utilize natural deduction to help us figure out the proof terms.

In this post, we have only been working in intuitionist propositional logic. There are ways to get classical logic from a type theory; I discussed an example [here]({{<ref "callcc_classical_logic">}}).