import Verso
import VersoManual
import VersoBlueprint
import Polya.RegularizedG

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Occupations and Green's functions of random walks" =>

:::group "Occupation"
Occupations and Green's functions of random walks
:::

:::definition "walkRegularizedOccupation" (parent := "Occupation") (lean := "walkRegularizedOccupation")
Let $`W : ℕ → ℤᵈ` be a {uses "walk"}[walk] and let $`r ≥ 0`. Then the *$`r`-regularized occupation* of $`W` at $`x ∈ ℤᵈ` is

$$`L^W_r (x) = ∑_{t ∈ ℕ} r^t 𝟙_{\set{W(t) = x}}`
:::

:::lemma_ "walkRegularizedOccupation_mono" (parent := "Occupation") (lean := "walkRegularizedOccupation_mono")
The {uses "walkRegularizedOccupation"}[$`r`-regularized occupation] $`L^W_r (x)` of a walk $`W` is an increasing function of $`r`
:::

:::lemma_ "tsum_walkRegularizedOccupation_eq_geom_series" (parent := "Occupation") (lean := "tsum_walkRegularizedOccupation_eq_geom_series")
The sum over all points $`x ∈ ℤᵈ` of the {uses "walkRegularizedOccupation"}[$`r`-regularized occupations] $`L^W_r (x)` of a walk $`W : ℕ → ℤᵈ` is

$$`∑_{x ∈ ℤᵈ} L^W_r (x) = ∑_{t ∈ ℕ} r^t`

(Both sides above are infinite, if $`r ≥ 1`, but the equality nevertheless holds in $`[0, +∞]`.)
:::

:::definition "regularizedOccupation" (parent := "Occupation") (lean := "regularizedOccupation")
Let $`X` be a {uses "random_walk"}[random walk] on $`ℤᵈ` and let $`r ≥ 0`. Then the *$`r`-regularized occupation* of $`X` at $`x ∈ ℤᵈ` is

$$`L_r (x) = L^X_r (x) = ∑_{t ∈ ℕ} r^t 𝟙_{\set{X(t) = x}}`
:::

:::lemma_ "regularizedOccupation_measurable" (parent := "Occupation") (lean := "regularizedOccupation.measurable")
The {uses "regularizedOccupation"}[regularized occupation] $`L_r (x)` of a random walk $`RW` is a $`[0, +∞]`-valued random variable.
:::

:::proof "regularizedOccupation_measurable"
This follows from {uses "random_walk_measurable"}[]
:::

:::lemma_ "regularizedOccupation_mono" (parent := "Occupation") (lean := "regularizedOccupation_mono")
The {uses "regularizedOccupation"}[$`r`-regularized occupation] $`L_r (x)` of a random walk $`X` is increasing in $`r`.
:::

:::proof "regularizedOccupation_mono"
This follows from {uses "walkRegularizedOccupation_mono"}[]
:::

:::lemma_ "regularizedOccupation_le" (parent := "Occupation") (lean := "regularizedOccupation_le")
The {uses "regularizedOccupation"}[$`r`-regularized occupation] $`L_r (x)` of a random walk $`X` at any point $`x ∈ ℤᵈ` satisfies $`L_r (x) ≤ \frac{1}{1 - r}`
:::

:::lemma_ "regularizedOccupation_apply_tendsto_of_monotone" (parent := "Occupation") (lean := "regularizedOccupation_apply_tendsto_of_monotone")
If $`(r_n)_{n ∈ ℕ}` is an increasing sequence with limit $`r = lim_{n → ∞} r_n`, then for any $`x ∈ ℤᵈ` the random variables $`L_{r_n} (x)` have limit $`L_r (x) = lim_{n → ∞} L_{r_n} (x)`, where $`L_r` is the {uses "regularizedOccupation"}[$`r`-regularized occupation] of some random walk.
:::

:::proof "regularizedOccupation_apply_tendsto_of_monotone"
TODO {uses "walkRegularizedOccupation_mono"}[]
:::

:::lemma_ "tsum_regularizedOccupation_eq_geom_series" (parent := "Occupation") (lean := "tsum_regularizedOccupation_eq_geom_series")
The sum over all points $`x ∈ ℤᵈ` of the {uses "regularizedOccupation"}[$`r`-regularized occupations] $`L_r (x)` of a random walk $`X` is

$$`∑_{x ∈ ℤᵈ} L_r (x) = ∑_{t ∈ ℕ} r^t`

(Both sides above are infinite, if $`r ≥ 1`, but the equality nevertheless holds in $`[0, +∞]`.)
:::

:::proof "tsum_regularizedOccupation_eq_geom_series"
TODO {uses "tsum_walkRegularizedOccupation_eq_geom_series"}[]
:::

:::lemma_ "tsum_toReal_regularizedOccupation_eq" (parent := "Occupation") (lean := "tsum_toReal_regularizedOccupation_eq")
If $`r < 1` then the infinite sum in {uses "tsum_regularizedOccupation_eq_geom_series"}[] is convergent in $`ℝ`, and the equality

$$`∑_{x ∈ ℤᵈ} L_r (x) = \frac{1}{1 - r}`

holds in $`ℝ`.
:::

:::lemma_ "tsum_lintegral_norm_regularizedOccupation_le" (parent := "Occupation") (lean := "tsum_lintegral_norm_regularizedOccupation_le")
If $`r < 1` then the sum over the points of the expected absolute values $`|L_r (x)|` of the regularized occupation of a random walk $`X` has the upper bound

$$`∑_{x ∈ ℤᵈ} E[L_r (x)] ≤ \frac{1}{1 - r}`
:::

:::proof "tsum_lintegral_norm_regularizedOccupation_le"
TODO {uses "tsum_toReal_regularizedOccupation_eq"}[] {uses "regularizedOccupation_le"}[] {uses "regularizedOccupation_measurable"}[]
:::

:::definition "regularizedG" (parent := "Occupation") (lean := "regularizedG")
Let $`X` be a random walk on $`ℤᵈ` and let $`0 ≤ r < 1`. Then the *$`r`-regularized Green's function* of $`X` is the function $`G_r : ℤᵈ → ℝ` whose value at $`x ∈ ℤᵈ` is the expected value of the {uses "regularizedOccupation"}[regularized occupation] $`L_r (x)` at $`x`.

$$`G_r (x) = E[L_r (x)]`
:::

:::lemma_ "tsum_regularizedG_eq_lintegral_tsum" (parent := "Occupation") (lean := "tsum_regularizedG_eq_lintegral_tsum")
We have

$$`∑_{x ∈ ℤᵈ} G_r (x) = E[∑_{x ∈ ℤᵈ} L_r (x)]`
:::

:::proof "tsum_regularizedG_eq_lintegral_tsum"
TODO {uses "tsum_lintegral_norm_regularizedOccupation_le"}[]
{uses "regularizedG"}[]
:::

:::lemma_ "tsum_regularizedG_eq" (parent := "Occupation") (lean := "tsum_regularizedG_eq")
We have

$$`∑_{x ∈ ℤᵈ} G_r (x) = \frac{1}{1 - r}`
:::

:::proof "tsum_regularizedG_eq"
TODO {uses "tsum_regularizedG_eq_lintegral_tsum"}[], {uses "tsum_toReal_regularizedOccupation_eq"}[]
:::

:::lemma_ "regularizedG_tendsto" (parent := "Occupation") (lean := "regularizedG_tendsto")
Let $`X = (X(t))_{t ∈ ℕ}` be a random walk starting from the origin $`\vec{0} ∈ ℤᵈ`. Denote by $`L = \# \set{t ∈ ℕ | X(t) = \vec{0}}` the number of times the random walk is at the origin. Then we have

$$`G_r (\vec{0}) ↗ E[L] \qquad \text{ as } r ↗ 1`

where $`G_r` is the {uses "regularizedG"}[$`r`-regularized Green's function].
:::

:::proof "regularizedG_tendsto"
Recall that $`G_r (\vec{0}) = E[L_r(\vec{0})]` by definition, and observe that $`L = L_1(\vec{0})`. Therefore the statement is equivalent to $`G_r (\vec{0}) \nearrow G_1 (\vec{0})` as $`r \nearrow 1`. For this, it suffices to prove that whenever $`(r_n)_{n ∈ ℕ}` is an increasing sequence with limit $`1 = \lim_{n \to \infty} r_n`, then $`G_{r_n} (\vec{0}) \nearrow G_{1}(\vec{0})` as $`n \to \infty`. {uses "regularizedOccupation_apply_tendsto_of_monotone"}[] shows exactly that.
:::
