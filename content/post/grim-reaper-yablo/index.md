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
Ok, the title is a bit of a click bait. I have a particular version of the Grim Reaper paradox in mind, namely the one that many uses to argue against the *logical* or *metaphysical* possibility of an infinite past.[^1] Here, I will show how this version of the Grim Reaper paradox is the Yablo paradox in disguise (although with some ~~important~~ differences), why that matters, and drawing from their parallel, conclude with why the paradox fails to show the *im*possibility of an infinite past.
[^1]: See Alex Malpass discussion of it [here](https://useofreason.wordpress.com/2020/01/07/the-paradox-of-dry-eternity/) (I can't find the papers that he refers to anymore).

## The Twinning Paradoxes
I prefer [this version](https://useofreason.wordpress.com/2020/07/12/the-logical-form-of-the-grim-reaper-paradox/) of the paradox (let's call it the **Printer Paradox**):
> Suppose the past has no beginning. There is an eternal machine such that each day at midnight, it checks to see if it has printed out anything yet from its printer. If it has, then it hibernates for the rest of the day. If it has not printed anything out yet, it immediately prints out the date and then hibernates for the rest of the day.
> 
> This is enough to generate our paradox. If it had not already printed anything out, this means that yesterday it would have run the same check and printed out the date. So it can’t be that the machine finds nothing printed out today. But that applies also to yesterday too, and every previous day. So although it can’t be that no date is printed out, no date could be printed on the paper. [Quote]

The logical structure of the paradox is pretty clear. Again I quote Alex:
>1. There is no first time $t$
>2. For all $t$, ($P$ at $t$ iff for all $t’$, (if $t ' \lt t$, then $\lnot P$ at $t$))  
>[Quote]

Contrasting this with the [Yablo paradox](https://en.wikipedia.org/wiki/Stephen_Yablo#Yablo's_paradox), which involves an infinitely long list of sentences:  
>$S_1$. For all $i \gt 1$, $S_i$ is not true.  
>$S_2$. For all $i \gt 2$, $S_i$ is not true.  
>$S_3$. For all $i \gt 3$, $S_i$ is not true.  
>...

We also need to consider what is called the *T-schema*:
> T-Schema: $S$ is true iff $S$  

Now we can prove a contradiction:  
Consider some arbitrary $k$, suppose that $S_k$ is true, then for any $i \gt k$, $S_k$ is not true. Then $S_{k+1}$ is not true. But because $S_k$ is true, that means that for any $j \gt {k+1}$, $S_{j}$ is not true. So $S_{k+1}$ must be true! Contradiction.  
Because $k$ was chosen arbitrarily, we have proven that for any $k$, $S_k$ is true. So for any $l \gt 2$, $S_l$ is true. So $S_1$ is true. But we just proved that all sentences on the list is not true, including $S_1$! Contradiction again.

How does all of this relates to the Printer/Grim Reaper paradox? Well, if we think of the printer $p$ as different printers at each day, and we assign yesterday the number $1$, the day before yesterday the number $2$, and so on, we have an infinitely long list of sentences that says:  
>1. $p_1$ prints iff for all $i \gt 1$, $p_i$ did not print.  
>1. $p_2$ prints iff for all $i \gt 2$, $p_i$ did not print.  
>1. $p_3$ prints iff for all $i \gt 3$, $p_i$ did not print.  
>...  

At first glance, this might look different still. What does the start of the sentences ($p_1$ prints...) corresponds to? Well, they corresponds to the T-Schema! 

There is, however, an important difference: The Yablo paradox is utilizes the [truth predicate](https://en.wikipedia.org/wiki/Truth_predicate), whereas the Printer/Grim Reaper paradox is just about... printers? 