---
title: 'callcc and Classical Logic'
date: 2025-02-18T10:25:13-06:00
pubDate: 2025-02-19
tags: ['logic', 'programming', 'type theory']
---

<!-- hide Tex macros -->
> \[\def\tf{\vdash}\]
{ class=hidden }

I couldn't find a simple written explanation of `callcc`, its type, and the connection to classical logic, so I thought I'd write one here.[^1] I won't assume that you are familiar with the syntax of Scheme (because I'm not), so I will be using a made up language. I hope the first part of this post will be self-contained, so that you don't have to understand any particular langauge to understand `callcc`. The second part concerns how the type of `callcc` relates to classical logic under [Curry-Howard Correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence). I will assume some familiarity and comfort with the concept and type theory notations.

[^1]: There is an excellent video on the type of `callcc` [here](https://www.youtube.com/watch?v=7Zkt_IJaYOY).

#### Prelude: Syntax
The syntax we use here is close to functional programming languages like ML.
- Everything is an expression, so has a value.
- Function definition: A function that takes input `x`, `y` and return `z` is written as
```
fn x y => z
```
  
  Besides `callcc`, any other function is anonymous.
- Function application: To call a function `f` with arguments `x` and `y`, we write  
```
f x y
```
- Function type: A function `f` with arguments `x` and `y` has the type 
>$A \to (B \to C)$

if `x` has type $A$, `y` has type $B$, and the return value of $f$ has type `C`. Any function that takes multiple arguments are actually functions that take one argument and return another function (and so on). [^2]
[^2]: See [Currying](https://en.wikipedia.org/wiki/Currying).

- When we write expressions in sequence, `e1; e2; ...; en`, the whole expression has the value of `en`.

There are other mischellaneous syntaxes like integer addition, which we won't be focusing on. But they should be obvious.

### Part 1: What is `callcc` and its type?

```
callcc f
callcc (fn c => ...)
```

`callcc` takes a function `f` and returns a value. The function it takes, `f`, takes another function `c`. Such `c` is what's called the "current continutation", which is "the rest of the computation" outside of `callcc`. All this probably doesn't make much sense, but don't worry, we will see what this means in a bit.

To understand how `callcc` works, we split uses of `callcc` into two scenarios:

**Scenario 1:** If `f` in `callcc` returns a value directly without using `c`, then the value is returned, and nothing special happens. Suppose we have the following code:

```
1 + callcc (fn c => 3)
```

To evaluate the operator `+`, we evaluate `1` to be `1`, then we evaluate `callcc`. Since it just returns `3`, the whole thing evaluates to `1 + 3 = 4`.

**Scenario 2:** If `f` in `callcc` calls the contituation function `c` with some argument `x`, then `callcc` invokes the current continuation with `x`. The rest of the code inside `callcc` is discarded/aborted (even though they might have been evaluated), and we continue in the current continuation. What does "current continutation" means? An example would help:
```
1 + callcc (fn c => c 5)
```
You can treat current continuation as a function that wraps the outer code, and replaces `callcc (fn c => ...)` with its argument. So here, the current continuation is `fn x => 1 + x`. This becomes the argument `c` to `f`.

Again, let us walk through the evaluation. `1` is first evaluated, then we evaluate `callcc`, which calls `c 5`. Then the computation inside callcc is aborted, and the whole expression evaluates to `1 + 5 = 6`. Note that this value is not passed back to the outer context (the `1 + ...`) again, rather, the outer context `c` is used inside `callcc`.

What if we have more code in `callcc`?
```
1 + callcc (fn c => 7 + 9; c 5; c 6)
```
Inside `callcc`, expression sequences are evaluated left to right. First, `7+9` is evaluated. Then `c 5`, which evaluates to `6`, and the computation ends. `c 6` is never evaluated.

So you can see that calling `c` basically aborts the computation inside `callcc`, and "returns the argument to `c` as value to the outer context."

**So, what is the type of `callcc`?**

In either case (whether `c` is used or not), it must return the same type that the outer context is expecting of it (in previous examples, that would be an `int`, because $1 + \dots$ expects an `int`).
So if the outer context is expecting type $A$, we know that it must have the type

\[? \to A\]

where "$?$" is the type of the function it takes as argument (`f`).

What is the type of `f`? it must take some function `c`, and return the same type as what the outer context expects (as in the first case where `c` is unused). So the type of `callcc` is:

\[(? \to A) \to A\]

where $c$ has type "$?$".

What is the type of `c`? We know it must take something of type $A$ again, for it to be useable in the outer context. But what does the outer context return? This is unknowable inside any of these functions, so it must be some general type that could be $A$, but need not be (in the previous examples, the outer context also has type `int`, but it could just as well be, say, `string`). So the type of `callcc` becomes:

\[((A \to B) \to A) \to A.\]

### Part 2: Connection to Classical Logic
How does all this relate to classical logic? If you have heard of the [Curry-Howard Correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), you know that in certain programming languages, the types of well-typed programs corresponds to theorems of some logic, and the programs corresponds to the proofs of the theorems. 

It is well-known that a language with the function, product, and sum type corresponds to intuitionistic (propositional) logic. Here we set up the language briefly, then look at how `callcc` can extend it so that well-typed programs corresponds to classical theorems.[^3]

[^3]: In [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) (the language we are using), $\lambda x. y$ is a function that takes $x$ as input and returns $y$, and $A\ B$ is calling a function $A$ with $B$ as input (separated by space). So for example, $(\lambda\ x. x)\ 1$ returns $1$.

#### Type Theory and Intuitionist Logic

- The **function type** corresponds to implication. In other words, a function of type $A \to B$ transforms proofs of $A$ to proofs of $B$. The lambda abstraction/application rule corresponds to the implication introduction/elimination rule, respectively.

\begin{prooftree}
\AXC{$\Gamma \tf x: A$}
\AXC{$\Gamma \tf y: B$}
\RL{$\lambda$abst/$\to$Intro}
\BIC{$\Gamma \tf \lambda x.\ y : A \to B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \tf M: A \to B$}
\AXC{$\Gamma \tf N: A$}
\RL{$\lambda$app/$\to$Elim}
\BIC{$\Gamma \tf M\ N : B$}
\end{prooftree}
In the typing realm, $\Gamma$ is a set of pairings from variables to their types. In the logic realm, the types in $\Gamma$ are the premises to the conclusion after $\tf$.

- The product type (type of pairs/$2$-tuples) corresponds to conjunction. We won't talk much about conjunctions here.
- The sum type, written as $A \lor B$, is a type that is either $A$ or $B$. This corresponds to disjunction. 
  - In particular, the **empty sum type**, written as $\bot$, is a type that (should) have no inhabitant. 
  - If there is an inhabitant of the empty sum type, then the program has gone wrong! We write this as the following rule, which corresponds to the [principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion), or *ex falso quodlibet*, in logic:
\begin{prooftree}
    \AXC{$\Gamma \tf p : \bot$}
    \RL{Explosion}
    \UIC{$\Gamma \tf \text{abort}(p) : A$}
\end{prooftree}

- **Negation** is defined as $\neg P \equiv P \to \bot$.

#### Getting Classical

There are certain propositions that are not theorems in intuitionist logic, but they are theorems in classical logic. The most famous examples are **Law of Excluded Middle** (LEM) and **Double Negation Elimination** (DNE):

LEM
: $P \lor \neg P$

DNE
: $\neg\neg P \to P$

They are quite magical: If we add LEM or DNE as axioms to intuitionistc logic, we can then prove everything we can prove in classical logic. In other words, intuitionist logic + LEM/DNE = classical logic.

There is, however, a less well-known proposition that is equivalent to the two above, which is [Pierce's law](https://en.wikipedia.org/wiki/Peirce's_law):

Pierce's law
: $((P \to Q) \to P) \to P$

If you change the $P$ to $A$ and $Q$ to $B$, you'll realize: this is exactly the type of `callcc`!

This tells us that when our type theory is intuitionistic, we just need to add `callcc` to get a type theory for classical logic. At this point, you might not be convinced yet, and that's ok. Let us prove that Pierce's law implies DNE.[^4]

[^4]: We leave the reverse direction to the reader because it is unnecessary for our purposes, and we don't have a concrete function whose type is DNE that we can use to construct a function whose type is Pierce's law.

First, we give a proof purely in terms of logic (intuitionistically valid):
{{% proof "Pierce\'s law $\Rightarrow$ DNE" %}}
||||
|:--|:---|:--|
|1. | $((P \to Q) \to P) \to P$ | Pierce's law |
|2. | $\neg\neg P$ | Assume for conditional proof |  
|3. | $\neg P$ | Assume for conditional proof |  
|4. | $\bot$ | From $2$ and 3 |
|5. | $P$ | By explosion from 4 |
|6. | $\neg P \to P$, or $(P \to \bot) \to P$ | Conditional proof, 3 ~ 5 |
|7. | $P$ | $\to$Elim, 1 and 6 (where $Q$ is $\bot$) |
|8. | $\neg\neg P \to P$ | Conditional proof, 2 ~ 7 |
{{% /proof %}}

Then we give the program whose type is the proposition DNE, using `callcc`:

\[
    \lambda \underset{\mathclap{\underset{(P \to \bot) \to \bot}{\downarrow}}}{x}.\ 
    \text{callcc}\ 
    \underbrace{(\lambda \overset{\mathclap{\overset{P \to \bot}{\uparrow}}}{y}.\ 
    \underbrace{\text{abort}(\overbrace{x\ y}^\bot)}_P)}_{(P \to \bot) \to P}
    : ((P \to \bot) \to \bot) \to P.
\]

This might seem a bit complicated at first, so I annotated relevant variables and expressions with their types. Here is the relation between the program and the proof above:

1. corresponds to the use of `callcc` as a well typed function
2. corresponds to binding $x$ in the outer $\lambda$
3. corresponds to binding $y$ in the inner $\lambda$
4. corresponds to the type of $x\ y$
5. corresponds to using $\text{abort}$ for explosion
6. corresponds to the lambda abstraction of $\lambda y.$
7. corresponds to the lambda application to `callcc`
8. corresponds to the lambda abstraction of $\lambda x.$

The whole program then has the type of DNE. Knowing the program representing the proof, one can easily rewrite the proof in the same style as the inference rules mentioned above. Since it wouldn't be too readable on this page, we leave that as an exercise to the reader.