import Verso
import VersoManual
import VersoBlueprint
import Polya.RegularizedG

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier transform of Green’s function" =>

:::group "GreenFourier"
Fourier transform of Green’s function
:::

:::lemma_ "regularizedG_square_summable" (parent := "GreenFourier") (lean := "regularizedG_square_summable")
For $`0 ≤ r < 1`, the {uses "regularizedG"}[regularized Green's function] $`G_r : ℤᵈ → ℝ` is an element of the Hilbert space $`ℓ²(ℤᵈ, ℂ)` of the complex-valued square-summable functions on $`ℤᵈ`.
:::

:::proof "regularizedG_square_summable"
TODO {uses "tsum_regularizedG_eq"}[]
:::

:::definition "regularizedG_Fourier" (parent := "GreenFourier")
Let $`0 ≤ r < 1`. The *Fourier transform* of the {uses "regularizedG"}[regularized Green's function] $`G_r : ℤᵈ → ℝ` is the function

$$`\hat{G_r} : ℝᵈ → ℂ`

given by

$$`\hat{G_r} (θ) = ∑_{x ∈ ℤᵈ} e^{i x · θ} G_r (x)`

The necessary assumptions for this follow from {uses "regularizedG_square_summable"}[].
:::

:::lemma_ "Markovian_Green_Fourier" (parent := "GreenFourier")
For a {uses "iid_random_walk"}[time homogeneous random walk] $`X = (X(t))_{t ∈ ℕ}` on $`ℤᵈ` with step distribution $`p : ℤᵈ → [0, 1]`, the {uses "regularizedG_Fourier"}[Fourier transform] of the Green's function is

$$`\hat{G_r} (θ) = \frac{1}{1 - r ∑_{u ∈ ℤᵈ} p(u) e^{i u · θ}} = \frac{1}{1 - r \hat{p}(θ)}`
:::

:::lemma_ "SRW_Green_Fourier" (parent := "GreenFourier")
For the {uses "simple_random_walk"}[simple random walk] $`X = (X(t))_{t ∈ ℕ}` on $`ℤᵈ`, the Fourier tarnsform of the Green's function is

$$`\hat{G_r} (θ) = \frac{1}{1 - \frac{r}{d} ∑_{j = 1}^d cos(θ_j)}`
:::

:::proof "SRW_Green_Fourier"
TODO {uses "Markovian_Green_Fourier"}[]
:::

:::lemma_ "regularizedG_eq_integral_regularizedGFourier" (parent := "GreenFourier")
For any $`x ∈ ℤᵈ` and $`0 ≤ r < 1`, we have

$$`G_r (x) = \frac{1}{(2π)ᵈ} \iint_{[-π, π]ᵈ} (e^{-i x · θ} \hat{G_r} (θ)) dᵈ θ`
:::

:::proof "regularizedG_eq_integral_regularizedGFourier"
TODO {uses "regularizedG_Fourier"}[]
:::

:::lemma_ "regularizedG_eq_real_integral_regularizedGFourier" (parent := "GreenFourier")
For any $`x ∈ ℤᵈ` and $`0 ≤ r < 1`, we have

$$`G_r (x) = \frac{1}{(2π)ᵈ} \iint_{[-π, π]ᵈ} ℜ \mathfrak{e} (e^{-i x · θ} \hat{G_r} (θ)) dᵈ θ`
:::

:::proof "regularizedG_eq_real_integral_regularizedGFourier"
The integral of the real part is the real part of the integral so this is obvious from {uses "regularizedG_eq_integral_regularizedGFourier"}[]. The left hand side is real to start with, so equal to its own real part.
:::

Recall that we are interested in $`E[L]`, where $`L` is the number of visits to the origin by the random walk. {bpref "regularizedG_tendsTo"}[] states that $`E[L]` is the increasing limit of $`G_r (\vec{0})` as $`r \nearrow 1`, and {bpref "regularizedG_eq_real_integral_regularizedGFourier"}[] gives a formula rof $`G_r (\vec{0})` as the integral of the real part of the Fourier transform:

$$`G_r (\vec{0}) = \frac{1}{(2 π)^d} I_r`

where

$$`I_r = \iint_{[-π, π]^d} ℜ \mathfrak{e} (\hat{G_r} (θ)) d^d θ`

:::corollary "integral_regularizedGFourier_tendsto_iff" (parent := "GreenFourier")
A random walk $`X = (X(t))_{t ∈ ℕ}` on $`ℤᵈ` is {uses "RW_expect_rec_trans"}[expectation recurrent] if and only if

$$`lim_{r ↗ 1} I_r = +∞`

In other words, $`X` is {uses "RW_expect_rec_trans"}[expectation transient] if and only if

$$`lim_{r ↗ 1} I_r < +∞`
:::

:::proof "integral_regularizedGFourier_tendsto_iff"
TODO
{uses "regularizedG_eq_real_integral_regularizedGFourier"}[]
{uses "regularizedG_Fourier"}[]
{uses "regularizedG_tendsTo"}[]
:::
