---
title: 'The Grim Reaper Paradox is the Yablo Paradox'
date: 2024-04-07T21:11:13-05:00
type: post
draft: true
tags: ['logic', 'paradox']
ShowToc: true
cover:
  image: grim-reaper.jpg
  relative: true
---

## Introduction
Ok, the title is a bit of a click bait. I have a particular version of the Grim Reaper paradox in mind, namely the one that many uses to argue against the *logical* or *metaphysical* possibility of an infinite past. Here, I will show how this version of the Grim Reaper paradox is the Yablo paradox in disguise (although with some ~~important~~ differences), why that matters, and drawing from their parallel, conclude with why the Grim Reaper paradox fails to show the *im*possibility of an infinite past.

## The Twinning Paradoxes
### Grim Reaper Paradox
This is the Grim Reaper paradox (GM):
> Suppose that the temporal series of past events is [actually infinite](https://en.wikipedia.org/wiki/Actual_infinity) and that an actually infinite number of Grim Reapers exist. Suppose also that, at each [day in the past], a unique Reaper was assigned to issue a death warrant iff no previous Reaper had already issued a death warrant. ([Cohen on the Kalam Cosmological Argument](https://philarchive.org/archive/COHEFA-2), p. [11]) [^1]

For a proof of why it is contradictory, see Alex Malpass extended discussion of it [here](https://useofreason.wordpress.com/2020/01/07/the-paradox-of-dry-eternity/).
[^1]: There is no mention of the Yablo paradox in any of the discussions of this paradox that I can find.

The logical structure of the paradox is pretty clear. Here I will take [Malpass's presentation](https://useofreason.wordpress.com/2020/07/12/the-logical-form-of-the-grim-reaper-paradox/) of an alternative (but equivalent) version of the Grim Reaper's paradox and modify it to fit our version:
>Let $G_t$ be the proposition: "Grim reaper $g_t$ issues a death warrant (at time $t$)."
> 1. There is no first time $t$
> 2. For all $t$, $G_t \leftrightarrow$ (for all $t’$, $t ' \lt t \rightarrow \lnot G_{t'}$)  

With the logical structure of the Grim Reaper paradox in mind, let's take a look at the Yablo paradox.
### Yablo Paradox
The [Yablo paradox](https://en.wikipedia.org/wiki/Stephen_Yablo#Yablo's_paradox) involves an infinitely long list of sentences:  
>$S_1$= For all $i \gt 1$, $\lnot$("$S_i$" is true).  
>$S_2$= For all $i \gt 2$, $\lnot$("$S_i$" is true).  
>$S_3$= For all $i \gt 3$, $\lnot$("$S_i$" is true).  
>$\vdots$  [^2]
[^2]: I wanted to emphasize the predicate `... is true` here, so I used $\lnot$. I could as well just write '"$S_i$" is *not* true', which would be an equivalent way of stating things.

Note the use of quotes around each $S_i$: this concerns the [use-mention distinction](https://en.wikipedia.org/wiki/Use%E2%80%93mention_distinction). Each of $S_1$, $S_2$ is a sentence,  and quoting a sentence enables us to *refer* to the sentence. For eample, consider the sentence `I love bagels` (let's call it B). `"I love bagels" is true` is meaningful, whereas `I love bagels is true` is not. If I write `B`, that means that I love bagels (literally!). if I write `"B"`, then I'm talking about the sentence `"I love bagels"`, but not necessarily asserting it. From now on, we will follow this convention. 

Each sentence on the list has `... is true`, which is what's called the *truth predicate*. To reason about the truth predicate, we need the T-Schema:
> **T-Schema**: $\phi\leftrightarrow$ ($\phi$ is true)  

The T-Schema allow us to go from saying a sentence is true to "asserting" that sentence. With it, we can now prove a contradiction:
{{% proof %}}
Consider some arbitrary $k$, suppose that "$S_k$" is true, then, by the T-Schema, $S_k$. So, for any $i \gt k$, "$S_k$" is not true. Then "$S_{k+1}$" is not true.  Similarly, for any $j \gt {k+1}$, "$S_{j}$" is not true. So $S_{k+1}$, and by the T-Schema, "$S_{k+1}$" is true! Contradiction.  
So $S_k$ is not true. Because $k$ was chosen arbitrarily, we have proven that for any $k$, "$S_k$" is not true. So for any $l \gt 2$, "$S_l$" is not true. So "$S_1$" is true. But we just proved that all sentences on the list is not true, including $S_1$! Contradiction again.
{{% /proof %}}

### Similarity
How does all of this relates to the GM paradox? Well, we just need to *count backwards*. If we assign yesterday the number $1$, the day before yesterday the number $2$, and so on, we have an infinitely long list of sentences that says:  
>$G_1'$= For all $t \gt 1$, $\lnot G_t'$.  
>$G_2'$= For all $t \gt 2$, $\lnot G_t'$.  
>$G_3'$= For all $t \gt 3$, $\lnot G_t'$.  
>$\vdots$

This is not similar enough to the GM paradox yet. Each of $G_t'$ is distinct from $G_t$ because $G_t'$ does not say anything about issuing death warrants. To see the similarity, consider this additional principle:
>**G-Schema**: $G_t \leftrightarrow G_t'$

Notice that the G-Schema was in (2) when we the discussed the [GM paradox](#grim-reaper-paradox-gm). How do we use this to derive a contradiction? Exactly the same way we derived a contradiction in the [Yablo paradox](#yablo-paradox)! In case you're not convinced, here is the proof:

{{% proof a %}}
Consider some arbitrary $k$, suppose that $G_k$, then, by the G-Schema, $G_k'$. So, for any $t \gt k$, $\lnot G_t'$. Then $\lnot G_{k+1}'$.  Similarly, for any $s \gt {k+1}$, $\lnot G_{s}'$. So $G_{k+1}'$! Contradiction.  
So $\lnot G_k$ is not true. Because $k$ was chosen arbitrarily, we have proven that for any $k$, $\lnot G_k$. So for any $k$, $\lnot G_k'$. That entails for any $l \gt 2$, $\lnot G_l'$. Hence, $G_1'$. But we just proved that all sentences on the list is not true, including $G_1'$! Contradiction again.
{{% /proof %}}

Hopefully by now, you are convinced that there is at least some structural similarities between the Grim Reaper and the Yablo paradox. Obviously there are some glaring differences: The Yablo paradox involves the *truth predicate*, whereas the Grim Reaper paradox involves the "issues a death warrant" predicate. 

We know that the *truth predicate* is notorious for generating contradictions: just consider all the variants of the Yablo, the Liar paradox, the Curry paradox, etc. Can we generate similar variants about the Grim Reaper paradox? The answer is yes.

## Variants of the Grim Reaper
### The "Existential" Yablo
If we flip the "for all" in each sentence into "there exists", we get an existential version of the Yablo paradox. We can do the same thing for the printer paradox as well.

| Existential Yablo | |Existential GR |
| :---------------- | ---- |:------------- |
T-Schema: $\phi\leftrightarrow$ ($\phi$ is true) | | G-Schema: $G_t \leftrightarrow G_t'$
$S_1$= there exists $i \gt 1$, $\lnot$("$S_i$" is true) <br /> $S_2$= there exists $i \gt 2$, $\lnot$("$S_i$" is true) <br />$S_3$= there exists $i \gt 3$, $\lnot$("$S_i$" is true) <br /> $\vdots$||$G_1'$= there exists $t \gt 1$, $\lnot G_t'$ <br /> $G_2'$= there exists $t \gt 2$, $\lnot G_t'$ <br /> $G_3'$= there exists $t \gt 3$, $\lnot G_t'$ <br /> $\vdots$

We prove the paradoxicality of the Existential Yablo, and leave the Existential GR as an exercise for the reader.
{{% proof %}}
Suppose that for some arbitrary $k$, "$S_k$" is true. Then there exists $i > k$ such that $\lnot$("$S_i$" is true). By the T-Schema, $\lnot S_i$. So, there <u>does not</u> exist a $j > i$ such that $\lnot$("$S_j$" is true). So $S_{j+1}$ 
{{% /proof %}}

### Relation to the Liar Paradoxes

## Impossibility of an Infinite Past?
