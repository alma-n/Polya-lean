import Verso
import VersoManual
import VersoBlueprint
import Polya.RegularizedOccupation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Treatment of the integral in the Fourier inversion" =>

:::group "fourier_integral"
Treatment of the integral in the Fourier inversion
:::

In this part, we analyze the integral

$$`I_r = \iint_{[-π, π]ᵈ} ℜ \mathfrak{e} (\hat{G}_r (θ)) dᵈ θ`

where $`\hat{G}_r : ℝⁿ → ℂ` is the fourier transform of the regularized Green's function of a random walk $`X` on $`ℤᵈ`. By {bpref "integral_regularizedGFourier_tendsto_iff"}[], the finiteness of this integral in the limit $`r ↗ 1` characterized expectation transience of $`X`.

The main integral $`I_r` can be decomposed into two parts: an easy "high frequency part", which contains the contributions of $`θ` away from $`0`, and a more interesting "low frequency part", which contains the contributions of $`θ` near $`0`.

:::definition "frequency_decomp" (parent := "fourier_integral")
For any $`0 < \delta`, define the integrals

$$`J_r^{(\delta)} = \iint_{[-π, π]ᵈ \setminus B_δ} ℜ \mathfrak{e} (\hat{G}_r (θ)) dᵈ θ`
$$`K_r^{(\delta)} = \iint_{B_δ} ℜ \mathfrak{e} (\hat{G}_r (θ)) dᵈ θ`

where $`B_δ := {θ ∈ ℝᵈ | ‖θ‖ < δ}` is the ball of the radius $`\delta` centered at $`\vec{0} ∈ ℝᵈ` and $`I_r` is the integral from {uses "integral_regularizedGFourier_tendsto_iff"}[].
:::

:::lemma_ "decomp_eq_integral" (parent := "fourier_integral")
For any $`0 < δ ≤ π`, we can write

$$`I_r = J^{(δ)}_r + K^{(δ)}_r`

where $`J^{(δ)}_r` and $`K^{(δ)}_r` are the integrals from {uses "frequency_decomp"}[].
:::

:::lemma_ "highFreq_limit" (parent := "fourier_integral")

TODO {uses "frequency_decomp"}[]
:::
:::lemma_ "lowFreq_limit" (parent := "fourier_integral")
TODO {uses "frequency_decomp"}[]
:::

We can now rephrase the recurrence criterion in terms of only the low frequency integral.

:::lemma_ "expect_reccurent_iff_lowFrec_eq" (parent := "fourier_integral")
TODO {uses "highFreq_limit"}[], {uses "integral_regularizedGFourier_tendsto_iff"}[]
:::
