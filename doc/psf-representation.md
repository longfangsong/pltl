# Past subformular representation optimized for rewriting

## Why

Note, when doing $ψ⟨C⟩$, we need to choose different behaviour based on whether $ψ$ is in $C$.

Judge whether a PLTL is in a set directly (by checking whether they are equal one by one) is, generally speaking, inefficient.

And storing past formulas and their sets are also expensive in memory.

So we decided to make a better data structure for make it more efficient.

## Assumptions

We assume there are not too many past subformulars in a formula.

Because the space complexity of the whole algorithm is double exponential in the number of past subformulars (when the number of future- and
propositional nodes are fixed), so it is not meaningful to consider the case where there are really many past subformulars.

So we limit the number of past subformulars to 32.

In this way, many things can be represented as a 32-bit integer (as a bit set), for example, 
one bit in such bitsets can represent whether a formula exists, or whether a formula is weakened, etc.

## Design

### id

Basically we give each **root of** past subformular an id.

For example, in $ψ = (Y a\ S\ (\widetilde{Y} b)) B (Y\ b\ \widetilde{S}\ Y\ a)$, we number the root of subformulas like this:

| PLTL           | id |
| -------------- | --- |
| $\mathbf{Y}\ a$            |  0  |
| $\widetilde{\mathbf{Y}}\ b$           |  1  |
| $Y\ a\ \mathbf{S}\ \widetilde{Y}\ b$ |  2  |
| $\mathbf{Y}\ b$            |  3  |
| $Y\ b\ \widetilde{\mathbf{S}}\ Y\ a$ |  4  |
| $(Y\ a\ S\ \widetilde{Y}\ b) \mathbf{B}\ (Y\ b\ \widetilde{S}\ Y\ a)$ | 5  |

We call the process of numbering the root of subformulas "labeling".

Note we use post-order traversal index to number the root of subformulas, thus, 
all subformulas of a formula are labeled before the formula itself.

### Set representation

We use a 32-bit integer to represent a set of past subformulas.

Each bit in the integer represents whether a formula is in the set.

For example, if the set is $\\{2, 5\\}$, the integer is $100100$.

### Mask & State

Note, in rewriting, we need to know whether the past subformula is in a set.

But subparts of a past subformula can be rewrittern independently, 
for example, say we have $(Y\ a)\ S\ (\widetilde{Y}\ b)$ and its id is 2, 
then by sometime it is rewritten into $(Y\ a)\ S\ (Y\ b)$, if we want to rewrite it further with set 
$0000100=\\{(Y\ a)\ S\ (\widetilde{Y}\ b)\\}$, we cannot weaken it because these two formulas are not exactly the same 
(moreover, the content of the set may got rewritten too, for example when doing $C_i\langle C_j \rangle $).

Checking whether two formulas are the same was necessary to be done in a recursive way, which is not efficient.

We can add some more information to prevent this problem:
- In a formula, use a state to represent which formula is weakened.
- Globally, use a mask to represent which (sub)formulas should be considered when judging whether a formula is in a set.

For example, in $ψ = (Y\ a\ S\ \widetilde{Y} b) B (Y\ b\ \widetilde{S}\ Y\ a)$, which is "labeled" as:

| PLTL           | id |
| -------------- | --- |
| $Y\ a$            |  0  |
| $\widetilde{Y}\ b$  |  1  |
| $(Y\ a)\ S\ (\widetilde{Y}\ b)$ |  2  |
| $Y\ b$            |  3  |
| $Y\ a$ |  4  |
| $Y\ b\ \widetilde{S}\ Y\ a$ |  5  |
| $(Y\ a\ S\ \widetilde{Y} b) B (Y\ b\ \widetilde{S}\ Y\ a)$ | 6  |

The initial state is $0100010$, which means the second and fifth formula are weakened.

And each PLTL's mask:

| PLTL           | mask |
| -------------- | --- |
| $Y\ a$            |  0000001  |
| $\widetilde{Y}\ b$  |  0000010  |
| $(Y\ a)\ S\ (\widetilde{Y}\ b)$ |  0000111  |
| $Y\ b$            |  0001000  |
| $Y\ a$ |  0010000  |
| $Y\ b\ \widetilde{S}\ Y\ a$ |  0111000  |
| $(Y\ a\ S\ \widetilde{Y} b) B (Y\ b\ \widetilde{S}\ Y\ a)$ |  1111111  |

Thus, whether a formula exists in a set can be calculated using bit operations.

For example, if the $Y\ a$ part of formula $2$ is weakened ($(\widetilde{Y}\ a)\ S\ (\widetilde{Y}\ b)$), the state becomes $0100011$,
and the set is $0000010$($\\{2\\}$) (not rewrittened), which state is $0100100$[^1].

For judging whether $2'$ is in the set, we just check whether they have the same state under the mask:

For formula $2'$, we have:

```
  state & mask
= 0100110 & 0000111
= 0000110
```

For set $\\{2\\}$, we have:
```
  set_state & mask
= 0100100 & 0000111
= 0000100
```

Since they are not equal, formula $2'$ is not in the set $\\{2\\}$.

### Handle same shape formulas

There is still problems in the above design:

- Formula $0$ and $4$ are exactly the same, thus $\\{0\\}$, $\\{4\\}$ should be the same set, and a set $\\{0, 4\\}$ should be "invalid".
- Formula $1$ and $3$ are not the same now, but they might got rewritten to the same formula in the future.

To solve these problems, we introduce the concept of "same shape formulas".

Two formulas are said to have the same shape if they are equivalent without considering the strength of the past operators in it.

For example, 
- $Y\ a$ and $\widetilde{Y}\ a$ have the same shape, no matter how are they labeled.
- $(Y\ a)\ S\ (\widetilde{Y}\ b)$ and $(Y\ a)\ \widetilde{S}\ (Y\ b)$ have the same shape, no matter how are they labeled.

For each past subformula, we maintain a bit set of same shape formulas.

For example, in $ψ = (Y\ a\ S\ \widetilde{Y} b) B (Y\ b\ \widetilde{S}\ Y\ a)$:

| PLTL           | id | same shape formulas |
| -------------- | --- | --- |
| $Y\ a$            |  0  | 0010001 |
| $\widetilde{Y}\ b$  |  1  | 0001010 |
| $(Y\ a)\ S\ (\widetilde{Y}\ b)$ |  2  | 0000100 |
| $Y\ b$            |  3  | 0001010 |
| $Y\ a$ |  4  | 0010001 |  
| $Y\ b\ \widetilde{S}\ Y\ a$ |  5  | 0100000 |
| $(Y\ a\ S\ \widetilde{Y} b) B (Y\ b\ \widetilde{S}\ Y\ a)$ | 6  | 1000000 |

Now, to judge whether a formula $a$ is in a set, we need to check any of the same shape formula, with the state of $a$, is in the set.

For example, to judge whether `{psf: 0, state: 0100010}` is in set `{psfs: 10000, state: 0100011}`,

we need to check the same shape formulas, ie. 0 and 4.

For 0, it is not in the set.

For 4, it is in the set, the corresponding state is $0$, which is equal to the state of $0$ in the formula.

Thus, `{psf: 0, state: 0100010}` is in the set `{psfs: 10000, state: 0100011}`.

Note: checking whether a same shape formula has the same state with the other formula can be done by bit operations,
say, we can move the states corresponding to the formulas[^2] to the same position by shift operations, and then use bitwise AND operation to check if they are the same.

### Generate power set of psfs

If we don't consider the same subformulas, the number of possible sets is $2^n$, where $n$ is the number of past subformulas, since we represent each set as a bit set, this is equivalent to the integer range [0, 2^n].

To handle the same subformulas, we only pick the one with the smallest id.

For example, in the above example, we only use (`0000001`)${0}$, but skipping (`0010000`)$\\{4\\}$ and (`0010001`)$\\{0, 4\\}$.

To check whethe two subformula are the same, we just need to check whether they have the same shape and the same "state under mask".

## Summary

In a nutshell:

- A subformula is represented by its id(integer) and state(bit set).
- A set is represented by a bit set of the ids(bit set), and a shared state(bit set).
- In the context, we maintain
  - a bit set of same shape formulas for each subformula.
  - a mask for each subformula.

So that we can:
- Check whether a past subformula, in whatever rewritten form, is in a set, efficiently using bit operations.

[^1]: Note: when rewriting a set, all formulas in that set are rewritten together with same information, 
so we can use the same `state` for the whole set.

[^2]: Use mask to filter out the states corresponding to the formulas. Note the mask of the same shape formulas are also in the same shape: the have same number of 1s.
