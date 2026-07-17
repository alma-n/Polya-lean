import Verso
import VersoManual
import VersoBlueprint
import Polya.RegularizedOccupation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Random walks" =>

:::group "random_walks"
Random walks
:::

:::definition "grid" (parent := "random_walks") (lean := "Grid")
The $`d`-dimensional integer *Grid* is $`\Z^d`
:::

A walk on the *Grid* $`ℤᵈ` is a function $`W : ℕ → ℤᵈ`, denoted $`t ↦ W(t)`. We construct walks from their sequences of steps as follows:

:::definition "walk" (parent := "random_walks") (lean := "walkOfSteps")
A sequence $`(u_s)_{s ∈ ℕ}` of steps in {uses "grid"}[$`ℤᵈ`] determines a *walk* $`W : ℕ → ℤᵈ` by

$$`W(t) = ∑_{0 ≤ s ≤ t} W(s)`
:::

A random walk is constructed from a sequence of random steps.

:::definition "random_walk" (parent := "random_walks") (lean := "RW")
A sequence $`(ξ_s)_{s ∈ ℕ}` of $`ℤᵈ`-valued random variables (on some probability space) determines a *random walk* $`X = (X(t))_{t ∈ ℕ}` by

$$`X(t) = ∑_{0 ≤ s ≤ t} ξ_s`

so a random walk is a {uses "walk"}[walk] determined by a sequence of random variables.
:::

:::lemma_ "random_walk_measurable" (parent := "random_walks") (lean := "RW.measurable")
The position $`X(t)` of a {uses "random_walk"}[random walk] $`X = (X(t))_{t ∈ ℕ}` at any time $`t ∈ ℕ` is a $`ℤᵈ`-valued random variable.
:::

:::definition "iid_random_walk" (parent := "random_walks")
A {uses "random_walk"}[random walk] $`X = (X(t))_{t ∈ ℕ}` on $`ℤᵈ` is said to be *time-homogeneous Markovian*, if its steps are independent and identically distributed.
:::

:::definition "simple_random_walk" (parent := "random_walks")
A random walk $`X = (X(t))_{t ∈ ℕ}` on $`ℤᵈ` is *simple*, if it is {uses "iid_random_walk"}[time-homogeneous Markovian] and its steps are uniformly distributed on nearest neighbors on the grid:

$$`P[X(t + 1) - X(t) = u] = \begin{cases}
                              \frac{1}{2d} & \text{ if } \|u\| = 1 \\
                              0            & \text{ otherwise.}
                            \end{cases}`
:::
