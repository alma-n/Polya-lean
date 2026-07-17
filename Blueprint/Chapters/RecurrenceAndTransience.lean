import Verso
import VersoManual
import VersoBlueprint


open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Recurrence and transience" =>

:::group "RecurrenceAndTransience"
Recurrence and transience of random walks
:::

:::definition "RW_rec_trans" (parent := "RecurrenceAndTransience")
The random walk $`X = (X(t))_{t ∈ ℕ}` is said to be *recurrent*, if

$$`P[X(t) = x₀ \text{ for infinitely many } t ∈ ℕ] = 1`

and transient if

$$`P[X(t) = x₀ \text{ for infinitely many } t ∈ ℕ] = 0`
:::

Usually random walks are taken to be Markov processes (Markovian random walks). Then one can use alternative formulations of recurrence and transience.

:::definition "RW_expect_rec_trans" (parent := "RecurrenceAndTransience")
Denote by $`L = \# \set{t ∈ ℕ | X(t) = x₀}` the number of times the random walk $`X = (X(t))_{t ∈ ℕ}` is at its starting point. The random walk $`X` is said to be *expectation recurrent* if
$$`E[L] = + ∞`
and *expectation transient* if
$$`E[L] < + ∞`
:::

:::lemma_ "recurrent_iff_expectation_recurrent" (parent := "RecurrenceAndTransience")
A {uses "iid_random_walk"}[Markovian random walk] $`X = (X(t))_{t ∈ ℕ}` is {uses "RW_rec_trans"}[recurrent] if and only if it is {uses "RW_expect_rec_trans"}[expectation recurrent].
:::
