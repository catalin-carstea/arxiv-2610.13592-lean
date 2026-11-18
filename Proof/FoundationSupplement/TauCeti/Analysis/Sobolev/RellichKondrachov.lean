/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Local Leanflow adaptation of the pinned Tau Ceti source.
The private zero-extension and restriction constructions and proof organization
below were changed to avoid expensive kernel conversion. The public theorem
statement is unchanged. Original copyright and license remain in force;
see the accompanying source-adoption manifest for the revision and patch. -/
module

public import Proof.FoundationSupplement.TauCeti.Analysis.Sobolev.Translation
public import Proof.FoundationSupplement.TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import Proof.FoundationSupplement.TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rellich--Kondrachov for zero-boundary first-order Sobolev spaces

This file proves that the canonical value map

`W^{1,p}_0(Ω) → Lᵖ(Ω)`

is a compact operator, for `1 ≤ p < ∞` and a bounded open subset `Ω` of a finite-dimensional real
inner-product space.  No regularity of the boundary is needed: a zero-boundary Sobolev function
extends by zero to a whole-space Sobolev function, and the extension is supported in `Ω`.

The proof applies the Fréchet--Kolmogorov criterion to the zero-extended values of the open unit
ball.  Their `Lᵖ` norms are uniformly bounded by their Sobolev norms, their supports lie in the
fixed bounded set `Ω`, and the whole-space Sobolev translation estimate bounds every translation
increment by `‖h‖ ‖∇u‖ₚ`.  Restriction back to `Ω` then gives compactness of the canonical value
map `TauCeti.W1p0.valueL`.

The corresponding statement for all of `W^{1,p}(Ω)` requires a boundary-regular extension
operator; for bounded Lipschitz domains it is
`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`.

## Main declaration

* `TauCeti.W1p0.isCompactOperator_valueL`: Rellich--Kondrachov for `W^{1,p}_0(Ω)`.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Corollary 9.16; L. C. Evans, *Partial Differential Equations*, Section 5.7.  The compactness
criterion used here is the Kolmogorov--Riesz form proved in
`TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal

private theorem norm_cast_value {A : Type*} [MeasurableSpace A]
    {nu eta : Measure A} {r : ENNReal} [Fact (1 ≤ r)] (h : nu = eta) (v : Lp ℝ r nu) :
    ‖cast (congrArg (fun m : Measure A => (Lp ℝ r m : Type _)) h) v‖ = ‖v‖ := by
  subst h
  rfl

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Restricting to `⊤` leaves a measure unchanged; this identifies the whole-space `Lᵖ` space in
which the zero extension takes its values with `Lᵖ(mu)`. -/
private theorem restrict_coe_top (nu : Measure E) :
    nu.restrict ((⊤ : Opens E) : Set E) = nu := by
  rw [Opens.coe_top, Measure.restrict_univ]

private def restrictionL : Lp ℝ p mu →L[ℝ] Lp ℝ p (mu.restrict (Omega : Set E)) :=
  LpToLpRestrictCLM E ℝ ℝ mu p (Omega : Set E)

private def restrictionValue : Lp ℝ p mu → Lp ℝ p (mu.restrict (Omega : Set E)) :=
  restrictionL

private theorem restriction_continuous :
    Continuous (restrictionValue (mu := mu) (Omega := Omega) (p := p)) :=
  (restrictionL (mu := mu) (Omega := Omega) (p := p)).continuous

private theorem restriction_coeFn (v : Lp ℝ p mu) :
    (restrictionValue (Omega := Omega) v : E → ℝ) =ᵐ[mu.restrict (Omega : Set E)] (v : E → ℝ) :=
  LpToLpRestrictCLM_coeFn ℝ (Omega : Set E) v

section PrivateExtension

variable (hsub : Omega ≤ (⊤ : Opens E))

private def extendedSobolev (u : W1p0 mu Omega p) : W1p0 mu (⊤ : Opens E) p :=
  W1p0.extendByZeroL hsub u

private def extendedValue (u : W1p0 mu Omega p) : Lp ℝ p (mu.restrict (⊤ : Opens E)) :=
  W1p.value (extendedSobolev hsub u : W1p mu (⊤ : Opens E) p)

private def zeroValue (u : W1p0 mu Omega p) : Lp ℝ p mu :=
  cast (congrArg (fun m : Measure E => (Lp ℝ p m : Type _)) (restrict_coe_top mu))
    (extendedValue hsub u)

private theorem norm_zeroValue (u : W1p0 mu Omega p) :
    ‖zeroValue hsub u‖ = ‖extendedValue hsub u‖ :=
  norm_cast_value (restrict_coe_top mu) (extendedValue hsub u)

private theorem norm_extendedValue (u : W1p0 mu Omega p) :
    ‖extendedValue hsub u‖ ≤ ‖extendedSobolev hsub u‖ :=
  W1p.norm_value_le _

private theorem norm_extendedSobolev (u : W1p0 mu Omega p) :
    ‖extendedSobolev hsub u‖ = ‖u‖ :=
  W1p0.norm_extendByZeroL hsub u

private theorem norm_zeroValue_le (u : W1p0 mu Omega p) :
    ‖zeroValue hsub u‖ ≤ ‖u‖ := by
  rw [norm_zeroValue]
  exact (norm_extendedValue hsub u).trans_eq (norm_extendedSobolev hsub u)

/-- The isometric cast does not move representatives, so the zero-extended value is represented
by the value of the whole-space Sobolev extension. -/
private theorem coeFn_zeroValue (u : W1p0 mu Omega p) :
    (zeroValue hsub u : E → ℝ) = (extendedValue hsub u : E → ℝ) :=
  funext fun x => coeFn_cast_Lp (restrict_coe_top mu) (extendedValue hsub u) x

private theorem extendedValue_zero_compl (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu, x ∉ (Omega : Set E) → extendedValue hsub u x = 0 :=
  W1p0.value_extendByZeroL_ae_eq_zero_compl u

private theorem extendedValue_eq (u : W1p0 mu Omega p) :
    extendedValue hsub u =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.value (u : W1p mu Omega p)) :=
  W1p0.value_extendByZeroL hsub u

private theorem exists_translation_bound {S : Set (W1p0 mu Omega p)} {C : ℝ}
    (hS : ∀ u ∈ S, ‖u‖ ≤ C) {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ u ∈ S, ∀ h : E, ‖h‖ < delta →
      eLpNorm (fun x => extendedValue hsub u (x + h) - extendedValue hsub u x) p mu
        ≤ epsilon :=
  W1p0.exists_pos_forall_eLpNorm_value_extendByZeroL_comp_add_sub_le_of_norm_le hS hepsilon

private def zeroImage : Set (Lp ℝ p mu) :=
  (zeroValue (mu := mu) (p := p) hsub) '' ball (0 : W1p0 mu Omega p) 1

private theorem zeroImage_supported : ∀ f ∈ zeroImage (mu := mu) (p := p) hsub,
    ∀ᵐ x ∂mu, x ∉ (Omega : Set E) → f x = 0 := by
  intro f hf
  obtain ⟨u, _, rfl⟩ := hf
  rw [coeFn_zeroValue]
  exact extendedValue_zero_compl hsub u

private theorem zeroImage_bounded : ∀ f ∈ zeroImage (mu := mu) (p := p) hsub,
    eLpNorm f p mu ≤ 1 := by
  intro f hf
  obtain ⟨u, hu, rfl⟩ := hf
  rw [mem_ball, dist_zero_right] at hu
  rw [← Lp.eNorm_def]
  calc
    ‖zeroValue hsub u‖ₑ ≤ ‖(1 : ℝ)‖ₑ := eNorm_le_iff_norm_le.mpr
      ((norm_zeroValue_le hsub u).trans (by simpa using hu.le))
    _ = 1 := by simp

private theorem zeroImage_translated : ∀ epsilon : ENNReal, 0 < epsilon →
    ∃ delta > 0, ∀ f ∈ zeroImage (mu := mu) (p := p) hsub, ∀ h : E,
      ‖h‖ < delta → eLpNorm (fun x => f (x + h) - f x) p mu ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := exists_translation_bound hsub
    (S := ball (0 : W1p0 mu Omega p) 1) (C := 1)
    (fun u hu => (mem_ball_zero_iff.1 hu).le) hepsilon
  refine ⟨delta, hdelta, fun f hf h hh => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hf
  rw [coeFn_zeroValue]
  exact hbound u hu h hh

private theorem zeroImage_compact (hp : p ≠ ∞) (hOmega : IsBounded (Omega : Set E)) :
    IsCompact (closure (zeroImage (mu := mu) (p := p) hsub)) :=
  isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl
    (E := E) (F := ℝ) (mu := mu) (p := p) (S := zeroImage hsub)
    (s := (Omega : Set E)) (M := 1) hp hOmega (zeroImage_supported hsub)
    ENNReal.one_ne_top (zeroImage_bounded hsub) (zeroImage_translated hsub)

private theorem W1p0.isCompactOperator_valueExtendByZero (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator (zeroValue (mu := mu) (p := p) hsub) := by
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (zeroValue (mu := mu) (p := p) hsub)).2
  refine ⟨ball 0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  exact zeroImage_compact hsub hp hOmega

private theorem zeroValue_restrict_ae (u : W1p0 mu Omega p) :
    (zeroValue hsub u : E → ℝ) =ᵐ[mu.restrict (Omega : Set E)]
      (W1p0.valueL u : E → ℝ) := by
  rw [coeFn_zeroValue, extendedValue_eq, W1p0.valueL_apply]
  exact coeFn_extendByZeroLpₗᵢ_restrict ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub) (W1p.value (u : W1p mu Omega p))

private theorem restricted_zeroValue_eq :
    (restrictionValue (mu := mu) (Omega := Omega) (p := p)) ∘ zeroValue hsub =
      (W1p0.valueL (mu := mu) (Omega := Omega) (p := p) :
        W1p0 mu Omega p → Lp ℝ p (mu.restrict (Omega : Set E))) := by
  funext u
  apply Lp.ext
  filter_upwards [restriction_coeFn (Omega := Omega) (zeroValue hsub u),
    zeroValue_restrict_ae hsub u] with x hx hvaluex
  exact hx.trans hvaluex

private theorem compact_restricted (hp : p ≠ ∞) (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator ((restrictionValue (mu := mu) (Omega := Omega) (p := p)) ∘ zeroValue hsub) :=
  (W1p0.isCompactOperator_valueExtendByZero (mu := mu) (p := p) hsub hp hOmega).continuous_comp
    (restriction_continuous (mu := mu) (Omega := Omega) (p := p))

include hsub in
private theorem compact_valueL (hp : p ≠ ∞) (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator (W1p0.valueL (mu := mu) (Omega := Omega) (p := p)) := by
  rw [← restricted_zeroValue_eq hsub]
  exact compact_restricted hsub hp hOmega

end PrivateExtension

/-- **Rellich--Kondrachov for zero-boundary Sobolev spaces.**  If `Ω` is bounded and
`1 ≤ p < ∞`, the canonical value map `W^{1,p}_0(Ω) → Lᵖ(Ω)` is a compact operator.

No boundary regularity is assumed.  The zero-boundary condition is what permits extension by zero
without creating a distributional boundary term. -/
theorem W1p0.isCompactOperator_valueL (hp : p ≠ ∞)
    (hOmega : IsBounded (Omega : Set E)) :
    IsCompactOperator (W1p0.valueL (mu := mu) (Omega := Omega) (p := p)) := by
  exact compact_valueL (le_top : Omega ≤ (⊤ : Opens E)) hp hOmega

end TauCeti
