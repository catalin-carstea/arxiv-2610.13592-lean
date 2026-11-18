module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.Metrizable
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Sequences
public import TauCeti.Analysis.Analytic.ContinuousMap
public import TauCeti.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Analysis.ODE.InitialCondition
public import TauCeti.Analysis.ODE.LocalFlow
public import TauCeti.Analysis.ODE.SmoothParameter
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Boundary.TransitionNormal
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.RPow
public import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Unit
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VariationField
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-! Meaning-bearing interface preparation. Selected theorem remains OPEN.
The following closed support code is retained from the project preparation
with exact provenance; it defines the original geometry and approved inputs.
No no-escape, seed or global-continuation producer is included. -/

/- Interface support: NativeDefinitions.lean, SHA256 2b957dcb6454e259448b743fe7d1dee9fc9d4b166985c39b7c91e03c10c772d8 -/
noncomputable section RefPart_NativeDefinitions

/-!
Concrete geometric interfaces being tested before preparation of the reference.
The Laplacian has the sign used in the selected paper.
-/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

abbrev Metric (k : ℕ∞ω := ∞) :=
  ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M => TangentSpace (𝓡∂ (n + 1)) x)

/-- The real vector space of smooth boundary functions with compact support in Γ. -/
def boundaryDatumSubmodule (Γ : Set ((𝓡∂ (n + 1)).boundary M)) :
    Submodule ℝ (((𝓡∂ (n + 1)).boundary M) → ℝ) where
  carrier := {f | ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Γ}
  zero_mem' := ⟨contMDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' hf hg :=
    ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add _ _).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' a f hf :=
    ⟨contMDiff_const.smul (I := 𝓘(ℝ)) hf.1, hf.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => a) f).trans hf.2.2⟩

abbrev BoundaryDatum (Γ : Set ((𝓡∂ (n + 1)).boundary M)) :=
  boundaryDatumSubmodule Γ

/-- The nonnegative Laplace–Beltrami operator plus an independent real potential. -/
def schrodinger (g : Metric (n := n) (M := M)) (q u : M → ℝ) (x : M) : ℝ :=
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩;
  letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide);
  -TauCeti.Manifold.laplaceBeltrami (𝓡∂ (n + 1)) u x + q x * u x

/-- A smooth solution on the whole manifold with the stated full boundary trace. -/
def IsDirichletSolution (g : Metric (n := n) (M := M)) (q : M → ℝ)
    (f : ((𝓡∂ (n + 1)).boundary M) → ℝ) (u : M → ℝ) : Prop :=
  ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u ∧
    (∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q u x = 0) ∧
    (∀ x : (𝓡∂ (n + 1)).boundary M, u x = f x)

/-- The smooth zero-boundary kernel is trivial; elliptic Fredholm theory supplies the inverse. -/
def Nonresonant (g : Metric (n := n) (M := M)) (q : M → ℝ) : Prop :=
  ∀ u : M → ℝ, IsDirichletSolution g q 0 u → u = 0

/-- Outward direction, unit length and orthogonality to the intrinsic boundary tangent. -/
def IsOutwardUnitNormal (g : Metric (n := n) (M := M))
    (x : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (x : M)) :
    Prop :=
  TauCeti.IsOutwardPointing (x : M) v ∧
    g.inner x v v = 1 ∧
    ∀ w : TangentSpace (𝓡 n) x,
      g.inner x v (mfderiv (𝓡 n) (𝓡∂ (n + 1))
        (fun y : (𝓡∂ (n + 1)).boundary M => (y : M)) x w) = 0

/-- Normal differentiation acts on the same solution used for the Dirichlet problem. -/
def normalDerivative (ν : (x : (𝓡∂ (n + 1)).boundary M) →
    TangentSpace (𝓡∂ (n + 1)) (x : M)) (u : M → ℝ)
    (x : (𝓡∂ (n + 1)).boundary M) : ℝ :=
  mvfderiv (𝓡∂ (n + 1)) u x (ν x)

end ConformalPoisson

end RefPart_NativeDefinitions

/- Interface support: ObservedDomain.lean, SHA256 9c7bc069a29368555579a49666e665208d9a0cac4c4dccda768f9e3a5e05ddce -/
noncomputable section RefPart_ObservedDomain

/-! Native observed domains for the boundary geometry of Theorem 1.1. -/

open Set

namespace ConformalPoisson

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]

/-- An ambient open set represents an arbitrary relatively open boundary patch. -/
noncomputable def observedDomain (V : TopologicalSpace.Opens M) : TopologicalSpace.Opens M :=
  ⟨I.interior M ∪ V, (I.isOpen_interior one_ne_zero).union V.isOpen⟩

theorem observedDomain_eq_interior_union_patch (V : TopologicalSpace.Opens M) :
    (observedDomain I V : Set M) = I.interior M ∪ (I.boundary M ∩ V) := by
  change I.interior M ∪ V = I.interior M ∪ (I.boundary M ∩ V)
  rw [Set.union_inter_distrib_left, I.interior_union_boundary_eq_univ, Set.univ_inter]

theorem boundary_inter_observedDomain (V : TopologicalSpace.Opens M) :
    I.boundary M ∩ (observedDomain I V : Set M) = I.boundary M ∩ V := by
  change I.boundary M ∩ (I.interior M ∪ V) = _
  rw [Set.inter_union_distrib_left,
    (I.disjoint_interior_boundary.symm).inter_eq, Set.empty_union]

end ConformalPoisson

end RefPart_ObservedDomain

/- Interface support: Conclusion.lean, SHA256 cb544f8982f671c4aa07808740d94032b83c22eaa2d7901ddbe14b4c07b5fb99 -/
noncomputable section RefPart_Conclusion

/-! The full geometric conclusion of the selected Theorem 1.1, before its proof assignment. -/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M M₁ M₂ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

def observedPatch (V : TopologicalSpace.Opens M) :
    Set ((𝓡∂ (n + 1)).boundary M) :=
  {x | (x : M) ∈ V}

/-- Extension by zero is used only through its germ at points of the open domain. -/
def extendFromOpen (U : TopologicalSpace.Opens M) (c : U → ℝ) : M → ℝ := by
  classical
  exact fun x => if hx : x ∈ U then c ⟨x, hx⟩ else 0

@[simp]
theorem extendFromOpen_apply (U : TopologicalSpace.Opens M) (c : U → ℝ) (x : U) :
    extendFromOpen U c x = c x := by
  classical
  simp [extendFromOpen, x.property]

/-- A specified solver must solve the concrete operator for every smooth full boundary datum. -/
structure DirichletSolver (g : Metric (n := n) (M := M)) (q : M → ℝ) where
  solve : (((𝓡∂ (n + 1)).boundary M) → ℝ) → M → ℝ
  correct : ∀ f, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f →
    IsDirichletSolution g q f (solve f)

/-- A common analytic map and multiplier on the interior together with the observed patch. -/
structure GaugePair (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂) where
  map : Diffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
    (observedDomain (𝓡∂ (n + 1)) V₁) (observedDomain (𝓡∂ (n + 1)) V₂) ω
  multiplier : (observedDomain (𝓡∂ (n + 1)) V₁) → ℝ
  analytic : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω multiplier
  positive : ∀ x, 0 < multiplier x

variable (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)

/-- The local measurements use the fixed analytic identification of the entire boundaries. -/
def LocalDNMapsEqual
    (β : Diffeomorph (𝓡 n) (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (g₁ : Metric (n := n) (M := M₁)) (g₂ : Metric (n := n) (M := M₂))
    (q₁ : M₁ → ℝ) (q₂ : M₂ → ℝ)
    (S₁ : DirichletSolver g₁ q₁) (S₂ : DirichletSolver g₂ q₂)
    (ν₁ : (x : (𝓡∂ (n + 1)).boundary M₁) →
      TangentSpace (𝓡∂ (n + 1)) (x : M₁))
    (ν₂ : (x : (𝓡∂ (n + 1)).boundary M₂) →
      TangentSpace (𝓡∂ (n + 1)) (x : M₂)) : Prop :=
  ∀ f : BoundaryDatum (observedPatch (n := n) V₁),
    ∀ x : (𝓡∂ (n + 1)).boundary M₁, (x : M₁) ∈ V₁ →
      normalDerivative ν₁ (S₁.solve f.val) x =
        normalDerivative ν₂ (S₂.solve (f.val ∘ β.symm)) (β x)

/-- Every identity is a property of one shared pair, including its boundary values. -/
def GaugePair.RealizesTheorem
    (P : GaugePair (n := n) V₁ V₂)
    (β : Diffeomorph (𝓡 n) (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (g₁ : Metric (n := n) (M := M₁)) (g₂ : Metric (n := n) (M := M₂))
    (q₁ : M₁ → ℝ) (q₂ : M₂ → ℝ)
    (S₁ : DirichletSolver g₁ q₁) (S₂ : DirichletSolver g₂ q₂)
    (ν₁ : (x : (𝓡∂ (n + 1)).boundary M₁) →
      TangentSpace (𝓡∂ (n + 1)) (x : M₁)) : Prop :=
  (∀ x : (𝓡∂ (n + 1)).boundary M₁, ∀ hx : (x : M₁) ∈ V₁,
    let z : observedDomain (𝓡∂ (n + 1)) V₁ := ⟨x, Or.inr hx⟩
    (P.map z : M₂) = (β x : M₂) ∧ P.multiplier z = 1 ∧
      normalDerivative ν₁
        (extendFromOpen (observedDomain (𝓡∂ (n + 1)) V₁) P.multiplier) x = 0) ∧
  (∀ x : observedDomain (𝓡∂ (n + 1)) V₁,
    ∀ v w : TangentSpace (𝓡∂ (n + 1)) x,
      g₂.inner (P.map x)
          (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
            (fun z => (P.map z : M₂)) x v)
          (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
            (fun z => (P.map z : M₂)) x w) =
        Real.rpow (P.multiplier x) (4 / ((n + 1 : ℝ) - 2)) *
          g₁.inner x
            (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
              (fun z : observedDomain (𝓡∂ (n + 1)) V₁ => (z : M₁)) x v)
            (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
              (fun z : observedDomain (𝓡∂ (n + 1)) V₁ => (z : M₁)) x w)) ∧
  (∀ x : observedDomain (𝓡∂ (n + 1)) V₁,
    q₂ (P.map x) =
      Real.rpow (P.multiplier x) (-((n + 1 : ℝ) + 2) / ((n + 1 : ℝ) - 2)) *
        schrodinger g₁ q₁
          (extendFromOpen (observedDomain (𝓡∂ (n + 1)) V₁) P.multiplier) x) ∧
  (∀ f : BoundaryDatum (observedPatch (n := n) V₁),
    ∀ x : observedDomain (𝓡∂ (n + 1)) V₁,
      S₁.solve f.val x =
        P.multiplier x * S₂.solve (f.val ∘ β.symm) (P.map x))

end ConformalPoisson

end RefPart_Conclusion

/- Interface support: MainData.lean, SHA256 573d46f2d87cf75e43f91f68c1feb14c5b89782d00726fa9cb66e39690804766 -/
noncomputable section RefPart_MainData

/-! The original analytic problems and the full target proposition. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M M₁ M₂ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

/-- The coefficients of the original nonresonant analytic boundary problem. -/
structure AnalyticProblem where
  metric : Metric (n := n) (M := M) ω
  potential : M → ℝ
  analytic_potential : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω potential
  nonresonant : Nonresonant (metric.ofLE (by decide)) potential

def AnalyticProblem.smoothMetric (A : AnalyticProblem (n := n) (M := M)) :
    Metric (n := n) (M := M) :=
  A.metric.ofLE (by decide)

variable (A₁ : AnalyticProblem (n := n) (M := M₁))
  (A₂ : AnalyticProblem (n := n) (M := M₂))
  (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)

/-- Exactly the shared analytic boundary, arbitrary nonempty patch and matching observations. -/
structure MatchingMeasurements where
  boundaryIdentification : Diffeomorph (𝓡 n) (𝓡 n)
    ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω
  patches_match : ∀ x : (𝓡∂ (n + 1)).boundary M₁,
    (x : M₁) ∈ V₁ ↔ (boundaryIdentification x : M₂) ∈ V₂
  patch_nonempty : (observedPatch (n := n) V₁).Nonempty
  solver₁ : DirichletSolver A₁.smoothMetric A₁.potential
  solver₂ : DirichletSolver A₂.smoothMetric A₂.potential
  normal₁ : (x : (𝓡∂ (n + 1)).boundary M₁) →
    TangentSpace (𝓡∂ (n + 1)) (x : M₁)
  normal₂ : (x : (𝓡∂ (n + 1)).boundary M₂) →
    TangentSpace (𝓡∂ (n + 1)) (x : M₂)
  normal₁_spec : ∀ x, IsOutwardUnitNormal A₁.smoothMetric x (normal₁ x)
  normal₂_spec : ∀ x, IsOutwardUnitNormal A₂.smoothMetric x (normal₂ x)
  local_DN_equal : LocalDNMapsEqual V₁ boundaryIdentification
    A₁.smoothMetric A₂.smoothMetric A₁.potential A₂.potential
    solver₁ solver₂ normal₁ normal₂

/-- The conclusion sought under compactness, connectedness, n ≥ 2 and the analytical premises.
Here n is the boundary dimension, so the manifolds have dimension n + 1 ≥ 3. -/
def TheoremOneOneResult (D : MatchingMeasurements A₁ A₂ V₁ V₂) : Prop :=
  ∃! P : GaugePair (n := n) V₁ V₂,
    P.RealizesTheorem V₁ V₂ D.boundaryIdentification
      A₁.smoothMetric A₂.smoothMetric A₁.potential A₂.potential
      D.solver₁ D.solver₂ D.normal₁

end ConformalPoisson

end RefPart_MainData

/- Interface support: ForwardInputs.lean, SHA256 27b4c6809ac42a754195e9548f450248c6648bceaccffa0e3ec59b4f999df705 -/
noncomputable section RefPart_ForwardInputs

/-!
Proposed analytical hypotheses on the concrete operator. These propositions are intended
to be parameters of the selected theorem when the corresponding literature result is used.
They do not provide proof terms for those literature results.
-/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- Smooth Dirichlet solvability for a nonresonant operator on the compact manifold. -/
def ForwardDirichletAssumption [T2Space M] : Prop :=
  IsCompact (univ : Set M) →
    ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q → Nonresonant g q →
        Nonempty (DirichletSolver g q)

/-- Interior analytic regularity for a solution of an operator with analytic coefficients. -/
def InteriorAnalyticRegularityAssumption : Prop :=
  ∀ (g : Metric (n := n) (M := M) ω) (q : M → ℝ),
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω q →
    ∀ (U : TopologicalSpace.Opens M), (U : Set M) ⊆ (𝓡∂ (n + 1)).interior M →
      ∀ u : M → ℝ, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u U →
        (∀ x ∈ U, schrodinger (g.ofLE (by decide)) q u x = 0) →
          ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω u U

/-- Local analyticity up to a boundary patch whose Dirichlet values are locally analytic. -/
def BoundaryAnalyticRegularityAssumption : Prop :=
  ∀ (g : Metric (n := n) (M := M) ω) (q : M → ℝ),
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω q →
    ∀ (f : ((𝓡∂ (n + 1)).boundary M) → ℝ) (u : M → ℝ),
      IsDirichletSolution (g.ofLE (by decide)) q f u →
      ∀ V : TopologicalSpace.Opens M,
        ContMDiffOn (𝓡 n) 𝓘(ℝ) ω f (observedPatch (n := n) V) →
          ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω u V

/-- Weak unique continuation from an open subset of a connected interior domain. -/
def InteriorUniqueContinuationAssumption : Prop :=
  ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q →
    ∀ (U : TopologicalSpace.Opens M), (U : Set M) ⊆ (𝓡∂ (n + 1)).interior M →
      IsConnected (U : Set M) →
      ∀ u : M → ℝ, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u U →
        (∀ x ∈ U, schrodinger g q u x = 0) →
        ∀ W : TopologicalSpace.Opens M, (W : Set M).Nonempty →
          (W : Set M) ⊆ U → EqOn u 0 W → EqOn u 0 U

/-- Zero Cauchy data on a relatively open boundary patch force local vanishing. -/
def BoundaryCauchyUniquenessAssumption : Prop :=
  ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q →
    ∀ (ν : (x : (𝓡∂ (n + 1)).boundary M) →
        TangentSpace (𝓡∂ (n + 1)) (x : M)),
      (∀ x, IsOutwardUnitNormal g x (ν x)) →
      ∀ (V : TopologicalSpace.Opens M)
          (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M)),
        (∀ x ∈ Γ, (x : M) ∈ V) →
        ∀ u : M → ℝ, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u V →
          (∀ x ∈ V, x ∈ (𝓡∂ (n + 1)).interior M → schrodinger g q u x = 0) →
          (∀ x ∈ Γ, u x = 0 ∧ normalDerivative ν u x = 0) →
          ∀ x ∈ Γ, ∃ W : TopologicalSpace.Opens M,
            (x : M) ∈ W ∧ (W : Set M) ⊆ V ∧ EqOn u 0 W

end ConformalPoisson

end RefPart_ForwardInputs

/- Interface support: ForwardProperties.lean, SHA256 b6e66d05f4b9bed62c8d6ff7232c78cc21d3fe1f7771bc7b277e03ffac1eeaf6 -/
noncomputable section RefPart_ForwardProperties

/-! The trivial Dirichlet kernel supplies uniqueness and linearity of the concrete solver. -/


open Set Bundle
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

variable (g : Metric (n := n) (M := M)) (q : M → ℝ)

theorem schrodinger_add {u v : M → ℝ}
    (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    schrodinger g q (u + v) x = schrodinger g q u x + schrodinger g q v x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  dsimp only [schrodinger]
  rw [TauCeti.Manifold.laplaceBeltrami_add (𝓡∂ (n + 1))
    (hu.of_le (by decide)) (hv.of_le (by decide))]
  simp only [Pi.add_apply]
  ring

theorem schrodinger_sub {u v : M → ℝ}
    (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    schrodinger g q (u - v) x = schrodinger g q u x - schrodinger g q v x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  dsimp only [schrodinger]
  rw [TauCeti.Manifold.laplaceBeltrami_sub (𝓡∂ (n + 1))
    (hu.of_le (by decide)) (hv.of_le (by decide))]
  simp only [Pi.sub_apply]
  ring

theorem schrodinger_smul (a : ℝ) {u : M → ℝ}
    (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u) (x : M) :
    schrodinger g q (a • u) x = a * schrodinger g q u x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  dsimp only [schrodinger]
  rw [TauCeti.Manifold.laplaceBeltrami_smul (𝓡∂ (n + 1)) a (hu.of_le (by decide))]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The operator in the potential formula depends only on the germ of the multiplier. -/
theorem schrodinger_eq_of_eventuallyEq {u v : M → ℝ} {x : M}
    (hu : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 u x)
    (hv : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 v x)
    (h : Filter.EventuallyEq (nhds x) u v) :
    schrodinger g q u x = schrodinger g q v x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  have hgrad : ∀ᶠ y in nhds x,
      TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) u y =
        TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) v y := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    simp only [TauCeti.Manifold.mgradient_def, hy.mvfderiv_eq]
  have hgu := (TauCeti.Manifold.contMDiffAt_mgradient (I := 𝓡∂ (n + 1))
    (n := 1) (by simpa only [one_add_one_eq_two] using hu)).mdifferentiableAt (by decide)
  have hgv := (TauCeti.Manifold.contMDiffAt_mgradient (I := 𝓡∂ (n + 1))
    (n := 1) (by simpa only [one_add_one_eq_two] using hv)).mdifferentiableAt (by decide)
  have hcov := (CovariantDerivative.leviCivitaConnection
    (𝓡∂ (n + 1)) M).isCovariantDerivativeOnUniv
  have hconnection := hcov.congr_of_eventuallyEq hgu hgv Filter.univ_mem hgrad
  dsimp only [schrodinger]
  simp only [TauCeti.Manifold.laplaceBeltrami_def, TauCeti.Manifold.divergence_def]
  rw [hconnection, h.eq_of_nhds]

theorem Nonresonant.solution_unique (hNR : Nonresonant g q)
    {f : ((𝓡∂ (n + 1)).boundary M) → ℝ} {u v : M → ℝ}
    (hu : IsDirichletSolution g q f u) (hv : IsDirichletSolution g q f v) : u = v := by
  have hzero : IsDirichletSolution g q 0 (u - v) := by
    refine ⟨hu.1.sub hv.1, ?_, ?_⟩
    · intro x hx
      rw [schrodinger_sub g q hu.1 hv.1, hu.2.1 x hx, hv.2.1 x hx, sub_self]
    · intro x
      simp only [Pi.sub_apply, hu.2.2 x, hv.2.2 x, sub_self, Pi.zero_apply]
  exact sub_eq_zero.mp (hNR (u - v) hzero)

theorem DirichletSolver.solve_add (S : DirichletSolver g q) (hNR : Nonresonant g q)
    {f h : ((𝓡∂ (n + 1)).boundary M) → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f) (hh : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ h) :
    S.solve (f + h) = S.solve f + S.solve h := by
  have hsf := S.correct f hf
  have hsh := S.correct h hh
  apply Nonresonant.solution_unique g q hNR (S.correct (f + h) (hf.add hh))
  refine ⟨hsf.1.add hsh.1, ?_, ?_⟩
  · intro x hx
    rw [schrodinger_add g q hsf.1 hsh.1, hsf.2.1 x hx, hsh.2.1 x hx, add_zero]
  · intro x
    simp only [Pi.add_apply, hsf.2.2 x, hsh.2.2 x]

theorem DirichletSolver.solve_smul (S : DirichletSolver g q) (hNR : Nonresonant g q)
    (a : ℝ) {f : ((𝓡∂ (n + 1)).boundary M) → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f) :
    S.solve (a • f) = a • S.solve f := by
  have hsf := S.correct f hf
  apply Nonresonant.solution_unique g q hNR
    (S.correct (a • f) (contMDiff_const.smul (I := 𝓘(ℝ)) hf))
  refine ⟨contMDiff_const.smul (I := 𝓘(ℝ)) hsf.1, ?_, ?_⟩
  · intro x hx
    rw [schrodinger_smul g q a hsf.1, hsf.2.1 x hx, mul_zero]
  · intro x
    simp only [Pi.smul_apply, hsf.2.2 x]

/-- The solution map on the test-data vector space used by the simultaneous jet argument. -/
def DirichletSolver.linearMap (S : DirichletSolver g q) (hNR : Nonresonant g q)
    (Γ : Set ((𝓡∂ (n + 1)).boundary M)) :
    BoundaryDatum Γ →ₗ[ℝ] (M → ℝ) where
  toFun f := S.solve f.val
  map_add' f h := S.solve_add g q hNR f.property.1 h.property.1
  map_smul' a f := S.solve_smul g q hNR a f.property.1

end ConformalPoisson

end RefPart_ForwardProperties

/- Interface support: Jets.lean, SHA256 c7a494c060fcbf8592a5863b978858d39dad83c13ea375d1d0247ec3d646cf49 -/
noncomputable section RefPart_Jets

/-!
Second-order jets in the native tangent spaces. The Hessian is stored with one index raised
by the metric, as the covariant derivative of the gradient. Its trace is minus the paper's
nonnegative Laplacian. Lowering that index recovers the symmetric covariant Hessian.
-/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- The metric parameter determines the norm used on the covector and raised Hessian. -/
def JetSpace (_g : Metric (n := n) (M := M)) (x : M) : Type :=
  ℝ × (TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] ℝ) ×
    (TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] TangentSpace (𝓡∂ (n + 1)) x)

instance (g : Metric (n := n) (M := M)) (x : M) :
    AddCommGroup (JetSpace g x) := by
  unfold JetSpace
  infer_instance

instance (g : Metric (n := n) (M := M)) (x : M) :
    Module ℝ (JetSpace g x) := by
  unfold JetSpace
  infer_instance

instance (g : Metric (n := n) (M := M)) (x : M) :
    NormedAddCommGroup (JetSpace g x) := by
  letI : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  unfold JetSpace
  infer_instance

instance (g : Metric (n := n) (M := M)) (x : M) :
    NormedSpace ℝ (JetSpace g x) := by
  letI : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  unfold JetSpace
  infer_instance

instance (g : Metric (n := n) (M := M)) (x : M) :
    FiniteDimensional ℝ (JetSpace g x) := by
  unfold JetSpace
  infer_instance

def secondJet (g : Metric (n := n) (M := M)) (u : M → ℝ) (x : M) :
    JetSpace g x :=
  letI : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩;
  letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide);
  ⟨u x, mvfderiv (𝓡∂ (n + 1)) u x,
    CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M
      (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) u) x⟩

/-- The homogeneous equation imposes one linear trace constraint on the jet. -/
def jetEquation (g : Metric (n := n) (M := M)) (q : M → ℝ) (x : M) :
    JetSpace g x →ₗ[ℝ] ℝ where
  toFun j := -LinearMap.trace ℝ (TangentSpace (𝓡∂ (n + 1)) x) j.2.2.toLinearMap +
    q x * j.1
  map_add' j k := by
    change -LinearMap.trace ℝ _ (j.2.2 + k.2.2).toLinearMap + q x * (j.1 + k.1) = _
    rw [ContinuousLinearMap.toLinearMap_add, map_add]
    ring
  map_smul' a j := by
    change -LinearMap.trace ℝ _ (a • j.2.2).toLinearMap + q x * (a * j.1) = _
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

theorem jetEquation_secondJet (g : Metric (n := n) (M := M)) (q u : M → ℝ) (x : M) :
    jetEquation g q x (secondJet g u x) = schrodinger g q u x := by
  let : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  dsimp only [jetEquation, secondJet, LinearMap.coe_mk, AddHom.coe_mk, schrodinger]
  rw [TauCeti.Manifold.laplaceBeltrami_def, TauCeti.Manifold.divergence_def]

/-- Symmetry of the covariant Hessian, expressed for its metric-raised endomorphism. -/
def symmetricJetSubmodule (g : Metric (n := n) (M := M)) (x : M) :
    Submodule ℝ (JetSpace g x) where
  carrier := {j | ∀ v w, g.inner x (j.2.2 v) w = g.inner x v (j.2.2 w)}
  zero_mem' := by
    intro v w
    change g.inner x (0 : TangentSpace (𝓡∂ (n + 1)) x) w = g.inner x v 0
    simp only [map_zero, zero_apply]
  add_mem' hj hk := by
    intro v w
    change g.inner x (_ + _) w = g.inner x v (_ + _)
    simp only [map_add, add_apply]
    exact congrArg₂ (· + ·) (hj v w) (hk v w)
  smul_mem' a j hj := by
    intro v w
    change g.inner x (a • j.2.2 v) w = g.inner x v (a • j.2.2 w)
    simp only [map_smul, smul_apply, smul_eq_mul, hj v w]

def compatibleJetSubmodule (g : Metric (n := n) (M := M)) (q : M → ℝ) (x : M) :
    Submodule ℝ (JetSpace g x) :=
  symmetricJetSubmodule g x ⊓ (jetEquation g q x).ker

theorem secondJet_mem_symmetricJetSubmodule
    (g : Metric (n := n) (M := M)) {u : M → ℝ} {x : M}
    (hu : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 u x) :
    secondJet g u x ∈ symmetricJetSubmodule g x := by
  let : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  intro v w
  change inner ℝ
      (CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M
        (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) u) x v) w =
    inner ℝ v
      (CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M
        (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) u) x w)
  have hs := TauCeti.Manifold.hessian_symm (I := 𝓡∂ (n + 1)) x hu v w
  simp only [TauCeti.Manifold.hessian_def] at hs
  exact hs.trans (real_inner_comm _ _)

theorem secondJet_mem_compatibleJetSubmodule
    (g : Metric (n := n) (M := M)) (q : M → ℝ) {u : M → ℝ} {x : M}
    (hu : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 u x) (hLu : schrodinger g q u x = 0) :
    secondJet g u x ∈ compatibleJetSubmodule g q x := by
  refine ⟨secondJet_mem_symmetricJetSubmodule g hu, ?_⟩
  change jetEquation g q x (secondJet g u x) = 0
  rw [jetEquation_secondJet, hLu]

theorem secondJet_add (g : Metric (n := n) (M := M)) {u v : M → ℝ}
    (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    secondJet g (u + v) x = secondJet g u x + secondJet g v x := by
  let : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · change mvfderiv (𝓡∂ (n + 1)) (u + v) x = _
    exact mvfderiv_add (hu.mdifferentiable (by decide) x)
      (hv.mdifferentiable (by decide) x)
  · change CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M
      (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) (u + v)) x = _
    rw [TauCeti.Manifold.mgradient_add (hu.mdifferentiable (by decide))
      (hv.mdifferentiable (by decide))]
    exact (CovariantDerivative.leviCivitaConnection
      (𝓡∂ (n + 1)) M).isCovariantDerivativeOnUniv.add
        (TauCeti.Manifold.mdifferentiable_mgradient (I := 𝓡∂ (n + 1))
          (hu.of_le (by decide)) x)
        (TauCeti.Manifold.mdifferentiable_mgradient (I := 𝓡∂ (n + 1))
          (hv.of_le (by decide)) x)

theorem secondJet_smul (g : Metric (n := n) (M := M)) (a : ℝ) {u : M → ℝ}
    (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u) (x : M) :
    secondJet g (a • u) x = a • secondJet g u x := by
  let : RiemannianBundle (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun y : M => TangentSpace (𝓡∂ (n + 1)) y) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (n' := 1) (by decide)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · change mvfderiv (𝓡∂ (n + 1)) (a • u) x =
      a • mvfderiv (𝓡∂ (n + 1)) u x
    simp
  · change CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M
      (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) (a • u)) x = _
    rw [TauCeti.Manifold.mgradient_smul]
    exact (CovariantDerivative.leviCivitaConnection
      (𝓡∂ (n + 1)) M).isCovariantDerivativeOnUniv.smul_const a
        (TauCeti.Manifold.mdifferentiable_mgradient (I := 𝓡∂ (n + 1))
          (hu.of_le (by decide)) x)

end ConformalPoisson

end RefPart_Jets

/- Interface support: JetEvaluation.lean, SHA256 891c63e8c9fa934d0f045615c6cd84c661b2fbf26ee5f2fb2c9196a159ac84fd -/
noncomputable section RefPart_JetEvaluation

/-! One datum supplies the simultaneous compatible jets at all selected interior points. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  (g : Metric (n := n) (M := M)) (q : M → ℝ)

def DirichletSolver.jetLinearMap (S : DirichletSolver g q) (hNR : Nonresonant g q)
    (Γ : Set ((𝓡∂ (n + 1)).boundary M)) (x : M) :
    BoundaryDatum Γ →ₗ[ℝ] JetSpace g x where
  toFun f := secondJet g (S.solve f.val) x
  map_add' f h := by
    change secondJet g (S.solve (f.val + h.val)) x = _
    rw [S.solve_add g q hNR f.property.1 h.property.1]
    exact secondJet_add g (S.correct _ f.property.1).1 (S.correct _ h.property.1).1 x
  map_smul' a f := by
    change secondJet g (S.solve (a • f.val)) x = _
    rw [S.solve_smul g q hNR a f.property.1]
    exact secondJet_smul g a (S.correct _ f.property.1).1 x

def DirichletSolver.compatibleJetLinearMap
    (S : DirichletSolver g q) (hNR : Nonresonant g q)
    (Γ : Set ((𝓡∂ (n + 1)).boundary M)) (x : M)
    (hx : x ∈ (𝓡∂ (n + 1)).interior M) :
    BoundaryDatum Γ →ₗ[ℝ] compatibleJetSubmodule g q x :=
  (S.jetLinearMap g q hNR Γ x).codRestrict (compatibleJetSubmodule g q x) fun f =>
    secondJet_mem_compatibleJetSubmodule g q
      ((S.correct _ f.property.1).1.of_le (by decide)).contMDiffAt
      ((S.correct _ f.property.1).2.1 x hx)

def DirichletSolver.simultaneousJetLinearMap
    (S : DirichletSolver g q) (hNR : Nonresonant g q)
    (Γ : Set ((𝓡∂ (n + 1)).boundary M)) {ι : Type*}
    (points : ι → M) (hpoints : ∀ i, points i ∈ (𝓡∂ (n + 1)).interior M) :
    BoundaryDatum Γ →ₗ[ℝ] ((i : ι) → compatibleJetSubmodule g q (points i)) :=
  LinearMap.pi fun i => S.compatibleJetLinearMap g q hNR Γ (points i) (hpoints i)

end ConformalPoisson

end RefPart_JetEvaluation

/- Interface support: RungeInput.lean, SHA256 67ea4796452f3988f992f796de2f1daf8aa097ab1115af4d4878ba855ae533d2 -/
noncomputable section RefPart_RungeInput

/-!
The finite-point C² specialization of qualitative partial-boundary Runge approximation.
The local solutions are inputs. The compatible-jet realization theorem remains a proof
obligation, including construction of those local solutions.

The source is Lassas–Liimatainen–Salo, Proposition A.2, applied to finitely many small disjoint
interior balls with connected exterior, followed by interior regularity. The selected paper
records the finite-union application in Proposition 3.3 and Appendix A.
-/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- Approximation at finitely many points of local homogeneous solutions by one family of
global Dirichlet solutions whose data are all supported in the observed patch. -/
def RungeJetApproximationAssumption [T2Space M] : Prop :=
  2 ≤ n → IsCompact (univ : Set M) →
    IsConnected ((𝓡∂ (n + 1)).interior M) →
    ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q → Nonresonant g q →
      ∀ S : DirichletSolver g q,
        ∀ Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M),
          (Γ : Set ((𝓡∂ (n + 1)).boundary M)).Nonempty →
          ∀ (N : ℕ) (points : Fin N → M),
            Function.Injective points →
            (∀ i, points i ∈ (𝓡∂ (n + 1)).interior M) →
            ∀ (U : Fin N → TopologicalSpace.Opens M),
              (∀ i, points i ∈ U i) →
              (∀ i, (U i : Set M) ⊆ (𝓡∂ (n + 1)).interior M) →
              ∀ v : Fin N → M → ℝ,
                (∀ i, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (v i) (U i)) →
                (∀ i, ∀ x ∈ U i, schrodinger g q (v i) x = 0) →
                ∃ f : ℕ → BoundaryDatum (Γ : Set ((𝓡∂ (n + 1)).boundary M)),
                  Filter.Tendsto
                    (fun m i => secondJet g (S.solve (f m).val) (points i))
                    Filter.atTop
                    (nhds (fun i => secondJet g (v i) (points i)))

end ConformalPoisson

end RefPart_RungeInput

/- Interface support: SchauderInput.lean, SHA256 c78e2ec05f610899cc093f918810d8952fe9572eb5e7a90d15e1f7adb8e1ad5e -/
noncomputable section RefPart_SchauderInput

/-!
A quantitative local Dirichlet input on the Euclidean unit ball. This is classical forward
Schauder theory, in the small perturbation form used after rescaling in Appendix A. It solves
arbitrary smooth forcing with zero boundary values, with a uniform C^{2,α} bound. It neither
constructs prescribed jets nor asserts surjectivity of any jet evaluation map.

Analytical provenance: the Dirichlet Laplacian Schauder estimate and solvability on a smooth
ball (Gilbarg–Trudinger, Chapter 6), followed by the Banach inverse perturbation theorem. The
smallness constant depends on the dimension and exponent. The perturbation formulation is a
consequence of those results, rather than a literal statement of one cited theorem. Its precise
source applicability still requires the pre-contract reading.
-/


open Set Metric
open scoped NNReal ContDiff

namespace ConformalPoisson

variable {d : ℕ}

/-- A max-type C^{0,α} bound: both the supremum norm and the Hölder constant are at most K. -/
def holderBound {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    (α : ℝ≥0) (U : Set E) (f : E → F) (K : ℝ≥0) : Prop :=
  (∀ x ∈ U, ‖f x‖ ≤ K) ∧ HolderOnWith K α f U

/-- A max-type C^{2,α} bound on an open Euclidean region, using actual Fréchet derivatives. -/
def secondOrderHolderBound (α : ℝ≥0) (U : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0) : Prop :=
  (∀ x ∈ U, ‖u x‖ ≤ K ∧ ‖fderiv ℝ u x‖ ≤ K ∧
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) ∧
    HolderOnWith K α (fun x => fderiv ℝ (fderiv ℝ u) x) U

/-- Coordinate form of the paper's sign convention, with an arbitrary first-order drift. -/
def coordinateSchrodinger
    (a : EuclideanSpace ℝ (Fin d) →
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q u : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∑ i, fderiv ℝ (fderiv ℝ u) z
    (EuclideanSpace.single i 1) (a z (EuclideanSpace.single i 1))) +
    fderiv ℝ u z (b z) + q z * u z

/-- The forward estimate at one fixed exponent and pair of uniform constants. -/
def SchauderDirichletEstimate (d : ℕ) (α δ C : ℝ≥0) : Prop :=
  ∀ (a : EuclideanSpace ℝ (Fin d) →
  (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin d) → ℝ),
    ContDiffOn ℝ ∞ a (closedBall 0 1) →
    ContDiffOn ℝ ∞ b (closedBall 0 1) →
    ContDiffOn ℝ ∞ q (closedBall 0 1) →
    holderBound α (closedBall 0 1) (fun z => a z - ContinuousLinearMap.id ℝ _) δ →
    holderBound α (closedBall 0 1) b δ →
    holderBound α (closedBall 0 1) q δ →
    ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (K : ℝ≥0),
      ContDiffOn ℝ ∞ F (closedBall 0 1) →
      holderBound α (closedBall 0 1) F K →
      ∃ u : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiffOn ℝ ∞ u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
        EqOn u 0 (sphere 0 1) ∧
        (∀ z ∈ ball 0 1, coordinateSchrodinger a b q u z = F z) ∧
        secondOrderHolderBound α (ball 0 1) u (C * K)


/-- Uniform forward solvability and a Schauder bound for operators sufficiently close to -Δ.
The constants are chosen before coefficients, forcing, and polynomial jet parameters. -/
def LocalSchauderDirichletAssumption (d : ℕ) : Prop :=
  0 < d → ∀ α : ℝ≥0, 0 < α → α < 1 →
    ∃ δ C : ℝ≥0, 0 < δ ∧ 0 < C ∧ SchauderDirichletEstimate d α δ C

theorem secondOrderHolderBound_at_center {α K : ℝ≥0}
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : secondOrderHolderBound α (ball 0 1) u K) :
    ‖u 0‖ ≤ K ∧ ‖fderiv ℝ u 0‖ ≤ K ∧ ‖fderiv ℝ (fderiv ℝ u) 0‖ ≤ K := by
  exact hu.1 0 (mem_ball_self (by norm_num))

end ConformalPoisson

end RefPart_SchauderInput

/- Interface support: NativeMeasures.lean, SHA256 822e16fc09a4ae11432eb442c7bacc63cf0a1e346b3a13a7567629144df509f8 -/
noncomputable section RefPart_NativeMeasures

/-!
The volume and boundary surface measures of the actual native metric. Both are
orientation-free Riemannian densities. The boundary metric is the pullback by
the actual boundary inclusion, rather than a separately chosen metric.
-/


open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

local instance ref_NativeMeasures_boundaryAnalyticManifold : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := ω) M (by decide)

/-- Compactness supplies the boundary Lindelöf instance needed by its volume density. -/
theorem compactSpace_nativeBoundary [CompactSpace M] :
    CompactSpace ((𝓡∂ (n + 1)).boundary M) :=
  isCompact_iff_compactSpace.mp ((𝓡∂ (n + 1)).isClosed_boundary (n := ω) (by decide)).isCompact

def boundaryMetric (g : Metric (n := n) (M := M)) :
    ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M => TangentSpace (𝓡 n) x) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M (by decide)
  have hι := TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := ω) M (by decide)
  exact g.pullback Subtype.val (hι.contMDiff.of_le (by decide)) (hι.mfderiv_injective (by decide))

theorem boundaryMetric_inner (g : Metric (n := n) (M := M))
    (x : (𝓡∂ (n + 1)).boundary M) (v w : TangentSpace (𝓡 n) x) :
    (boundaryMetric g).inner x v w =
      g.inner (x : M) (mfderiv (𝓡 n) (𝓡∂ (n + 1)) Subtype.val x v)
        (mfderiv (𝓡 n) (𝓡∂ (n + 1)) Subtype.val x w) := by
  unfold boundaryMetric
  apply ContMDiffRiemannianMetric.pullback_inner

def nativeVolume [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    (g : Metric (n := n) (M := M)) : Measure M := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact TauCeti.riemannianVolume (𝓡∂ (n + 1)) M

def nativeSurfaceMeasure [MeasurableSpace ((𝓡∂ (n + 1)).boundary M)]
    [BorelSpace ((𝓡∂ (n + 1)).boundary M)] [LindelofSpace ((𝓡∂ (n + 1)).boundary M)]
    (g : Metric (n := n) (M := M)) : Measure ((𝓡∂ (n + 1)).boundary M) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M (by decide)
  let : RiemannianBundle (fun x : (𝓡∂ (n + 1)).boundary M => TangentSpace (𝓡 n) x) :=
    ⟨(boundaryMetric g).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M => TangentSpace (𝓡 n) x) :=
    ⟨⟨(boundaryMetric g).inner, (boundaryMetric g).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact TauCeti.riemannianVolume (𝓡 n) ((𝓡∂ (n + 1)).boundary M)

end ConformalPoisson

end RefPart_NativeMeasures

/- Interface support: GreenInputs.lean, SHA256 3db63a596f523d77cbbd5b597692a5cfcd8181764d811eb7b9b77e206bf3d1ba -/
noncomputable section RefPart_GreenInputs

/-!
Green-kernel literature inputs for the actual native nonresonant operator.
The real kernel, native normal derivatives and metric volume/surface measures
are explicit. In particular, nonvanishing of its Poisson sections is NOT assumed.
The source-applicability intake reading is ../green-input-intake-reading/findings.md.
The manifold package combines localization/Fredholm inversion and smooth boundary
bootstrap with ter Elst--Ouhabaz, Theorem 5.2, Propositions 6.1/6.2,
Lemma 6.4 and Theorem 6.5 (arXiv:2404.18272v1). It is not a verbatim
manifold theorem from that Euclidean-domain source. No positivity of q is used.
-/


open Bundle Set MeasureTheory
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- The boundary-pole Poisson section is a derivative of the same actual Green kernel. -/
def boundaryPoissonSection
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (G : M → M → ℝ) (y : (𝓡∂ (n + 1)).boundary M) (x : M) : ℝ :=
  -normalDerivative ν (fun z => G x z) y

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [MeasurableSpace ((𝓡∂ (n + 1)).boundary M)] [BorelSpace ((𝓡∂ (n + 1)).boundary M)]
  [LindelofSpace ((𝓡∂ (n + 1)).boundary M)]

/-- Green and Poisson representation consequences needed at the remote-normal argument.
All identities use this same kernel and the same native metric and outward normal. -/
structure DirichletGreenKernel (g : Metric (n := n) (M := M)) (q : M → ℝ)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (S : DirichletSolver g q) where
  kernel : M → M → ℝ
  symmetric : ∀ x z, x ≠ z → kernel x z = kernel z x
  smooth_off_diagonal : ContMDiffOn ((𝓡∂ (n + 1)).prod (𝓡∂ (n + 1))) 𝓘(ℝ) ∞
    (fun p : M × M => kernel p.1 p.2) {p | p.1 ≠ p.2}
  zero_boundary : ∀ x ∈ (𝓡∂ (n + 1)).interior M,
    ∀ z : (𝓡∂ (n + 1)).boundary M, kernel x z = 0
  poisson_section_smooth : ∀ y : (𝓡∂ (n + 1)).boundary M,
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (boundaryPoissonSection ν kernel y) ({(y : M)}ᶜ)
  poisson_section_equation : ∀ y : (𝓡∂ (n + 1)).boundary M,
    ∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q (boundaryPoissonSection ν kernel y) x = 0
  poisson_section_zero_boundary : ∀ y z : (𝓡∂ (n + 1)).boundary M,
    z ≠ y → boundaryPoissonSection ν kernel y z = 0
  poisson_representation : ∀ f : ((𝓡∂ (n + 1)).boundary M) → ℝ,
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f → ∀ x ∈ (𝓡∂ (n + 1)).interior M,
      Integrable (fun z => boundaryPoissonSection ν kernel z x * f z) (nativeSurfaceMeasure g) ∧
      S.solve f x = ∫ z, boundaryPoissonSection ν kernel z x * f z ∂nativeSurfaceMeasure g
  mixed_normal_representation : ∀ f : ((𝓡∂ (n + 1)).boundary M) → ℝ,
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f → ∀ y : (𝓡∂ (n + 1)).boundary M, y ∉ tsupport f →
      Integrable (fun z => normalDerivative ν (boundaryPoissonSection ν kernel y) z * f z)
        (nativeSurfaceMeasure g) ∧
      normalDerivative ν (S.solve f) y =
        ∫ z, normalDerivative ν (boundaryPoissonSection ν kernel y) z * f z ∂nativeSurfaceMeasure g
  forcing_representation : ∀ F : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ F →
    HasCompactSupport F → tsupport F ⊆ (𝓡∂ (n + 1)).interior M →
    ∀ w : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ w →
      (∀ x : (𝓡∂ (n + 1)).boundary M, w x = 0) →
      (∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q w x = F x) →
      ∀ x ∈ (𝓡∂ (n + 1)).interior M,
        Integrable (fun z => kernel x z * F z) (nativeVolume g) ∧
        w x = ∫ z, kernel x z * F z ∂nativeVolume g
  forcing_normal_representation : ∀ F : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ F →
    HasCompactSupport F → tsupport F ⊆ (𝓡∂ (n + 1)).interior M →
    ∀ w : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ w →
      (∀ x : (𝓡∂ (n + 1)).boundary M, w x = 0) →
      (∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q w x = F x) →
      ∀ y : (𝓡∂ (n + 1)).boundary M,
        Integrable (fun z => boundaryPoissonSection ν kernel y z * F z) (nativeVolume g) ∧
        normalDerivative ν w y = -∫ z, boundaryPoissonSection ν kernel y z * F z ∂nativeVolume g

def GreenKernelAssumption [T2Space M] : Prop :=
  IsCompact (univ : Set M) →
    ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q → Nonresonant g q →
      ∀ (S : DirichletSolver g q)
        (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M)),
        (∀ y, IsOutwardUnitNormal g y (ν y)) → Nonempty (DirichletGreenKernel g q ν S)

end ConformalPoisson

end RefPart_GreenInputs

/- Interface support: InverseInputs.lean, SHA256 dced85ed1145cdf0e3a4cf76d1bfc2fe9c11151a2afe5a8574906396f313690e -/
noncomputable section RefPart_InverseInputs

/-!
Forward inhomogeneous Dirichlet and inverse normal-trace literature inputs.
The trace estimate is the consequence of L^r -> W^(2,r) -> C^1 used by Lemma 3.6.
The source-applicability intake reading is ../green-input-intake-reading/findings.md.
Global localization and Fredholm inversion remove the lower-order L^r term
by nonresonance; Sobolev--Morrey embedding gives the displayed normal bound.
The Euclidean source locators are ter Elst--Ouhabaz, Propositions 6.1/6.2;
the complete manifold consequence is not attributed verbatim to those statements.
-/


open Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def IsZeroDirichletSolution (g : Metric (n := n) (M := M)) (q F w : M → ℝ) : Prop :=
  ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ w ∧
    (∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q w x = F x) ∧
    (∀ x : (𝓡∂ (n + 1)).boundary M, w x = 0)

structure ZeroDirichletSolver (g : Metric (n := n) (M := M)) (q : M → ℝ) where
  solve : (M → ℝ) → M → ℝ
  correct : ∀ F : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ F →
    IsZeroDirichletSolution g q F (solve F)

/-- Smooth forcing has a unique zero-boundary inverse under the same nonresonance condition.
Uniqueness is a project consequence of Nonresonant; only existence is postulated here. -/
def ForwardInhomogeneousAssumption [T2Space M] : Prop :=
  IsCompact (univ : Set M) →
    ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q → Nonresonant g q →
        Nonempty (ZeroDirichletSolver g q)

/-- The boundary-normal consequence of the nonresonant L^r Dirichlet inverse estimate,
for real r greater than the full dimension n+1. One bound works for all forcings and points. -/
def NormalTraceInverseEstimateAssumption [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [LindelofSpace M] : Prop :=
  IsCompact (univ : Set M) →
    ∀ (g : Metric (n := n) (M := M)) (q : M → ℝ),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q → Nonresonant g q →
      ∀ (ν : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M)),
        (∀ x, IsOutwardUnitNormal g x (ν x)) →
        ∀ r : ℝ, (n + 1 : ℝ) < r → ∃ C : ℝ≥0,
          ∀ F w : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ F →
            IsZeroDirichletSolution g q F w →
            ∀ y : (𝓡∂ (n + 1)).boundary M,
              |normalDerivative ν w y| ≤ (C : ℝ) *
                (eLpNorm F (ENNReal.ofReal r) (nativeVolume g)).toReal

end ConformalPoisson

end RefPart_InverseInputs

/- Interface support: PositiveBilinearForms.lean, SHA256 f132bb20545e51aadd992630463a1054cc7a558cb96f312741b34340d75348ea -/
noncomputable section RefPart_PositiveBilinearForms
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see External/LICENSE.tauceti.

The compact-unit-sphere argument is adapted to continuous bilinear forms from
TauCeti/Analysis/Matrix/PosDef.lean at commit
4d91513e4d30746eb1fa96658c18e051c772e55e.
-/
open Filter Metric Set Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Strict positivity of a finite-dimensional real bilinear form is open.
Symmetry is not needed for this openness assertion. -/
theorem isOpen_setOf_positive_bilinearForm :
    IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ v : E, v ≠ 0 → 0 < B v v} := by
  rw [isOpen_iff_mem_nhds]
  intro B hB
  have key : ∀ᶠ C : E →L[ℝ] E →L[ℝ] ℝ in 𝓝 B,
      ∀ v ∈ sphere (0 : E) 1, 0 < C v v := by
    refine (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
      fun v hv => ?_
    have hcont : Continuous (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × E => z.1 z.2 z.2) := by
      exact (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
    exact (hcont.tendsto (B, v)).eventually_const_lt
      (hB v (ne_zero_of_mem_sphere one_ne_zero ⟨v, hv⟩))
  filter_upwards [key] with C hC v hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := hC (‖v‖⁻¹ • v) (by simp [norm_smul, hvpos.ne'])
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hvpos)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hvpos)).mp h)

end ConformalPoisson

end RefPart_PositiveBilinearForms

/- Interface support: AnalyticBilinearExtension.lean, SHA256 7b09cb761732e687bd59bee2e05859fce4522f0cd25d7d42263be1c54f66f8f4 -/
noncomputable section RefPart_AnalyticBilinearExtension

/-! Actual analytic extensions of positive symmetric tensor functions from a
relative chart domain. Symmetrization retains their original values, and the
positive cone is open in the finite-dimensional bilinear-form space. -/


open Filter Set Topology

namespace ConformalPoisson

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def symmetrizeBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (B + B.flip)

omit [FiniteDimensional ℝ E] in
theorem symmetrizeBilinear_symmetric (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    symmetrizeBilinear B v w = symmetrizeBilinear B w v := by
  simp only [symmetrizeBilinear, smul_apply, add_apply,
    smul_eq_mul, ContinuousLinearMap.flip_apply]
  rw [add_comm]

omit [FiniteDimensional ℝ E] in
theorem symmetrizeBilinear_eq (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) : symmetrizeBilinear B = B := by
  ext v w
  simp only [symmetrizeBilinear, smul_apply, add_apply,
    smul_eq_mul, ContinuousLinearMap.flip_apply, hB w v]
  ring

omit [FiniteDimensional ℝ E] in
theorem analyticAt_symmetrizeBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) :
    AnalyticAt ℝ (symmetrizeBilinear (E := E)) B := by
  have hflip : AnalyticAt ℝ (fun C : E →L[ℝ] E →L[ℝ] ℝ => C.flip) B := by
    exact LinearIsometryEquiv.analyticAt (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) B
  let S : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ _
  have hS := ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
    (F := E →L[ℝ] E →L[ℝ] ℝ) S (B + B.flip)
  exact hS.comp (f := fun C : E →L[ℝ] E →L[ℝ] ℝ => C + C.flip)
    (x := B) (analyticAt_id.add hflip)

/-- Extend the actual analytic-within tensor, retaining all original-domain
values and positive definiteness on one full open ambient neighborhood. -/
theorem exists_analytic_positive_symmetric_extension
    {G : D → E →L[ℝ] E →L[ℝ] ℝ} {s : Set D} {x : D}
    (hG : AnalyticWithinAt ℝ G s x)
    (hsymm : ∀ y ∈ insert x s, ∀ v w, G y v w = G y w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ∃ (H : D → E →L[ℝ] E →L[ℝ] ℝ) (U : Set D),
      IsOpen U ∧ x ∈ U ∧ AnalyticOnNhd ℝ H U ∧ EqOn G H (insert x s) ∧
      (∀ y v w, H y v w = H y w v) ∧
      ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < H y v v := by
  obtain ⟨H₀, hx, heq, hH₀⟩ := hG.exists_analyticAt
  let H : D → E →L[ℝ] E →L[ℝ] ℝ := fun y => symmetrizeBilinear (H₀ y)
  have hagree : EqOn G H (insert x s) := by
    intro y hy
    dsimp only [H]
    rw [← heq hy, symmetrizeBilinear_eq _ (hsymm y hy)]
  have han : AnalyticAt ℝ H x := (analyticAt_symmetrizeBilinear _).comp hH₀
  have hbasepos : ∀ v : E, v ≠ 0 → 0 < H x v v := by
    rw [← hagree (mem_insert x s)]
    exact hpos
  have hnearpos : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < H y v v :=
    han.continuousAt.eventually
      (isOpen_setOf_positive_bilinearForm.mem_nhds hbasepos)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp
    (hnearpos.and han.eventually_analyticAt)
  refine ⟨H, U, hU, hxU, fun y hy => (hUsub hy).2, hagree, ?_, ?_⟩
  · exact fun y v w => symmetrizeBilinear_symmetric (H₀ y) v w
  · exact fun y hy => (hUsub hy).1

end ConformalPoisson

end RefPart_AnalyticBilinearExtension

/- Interface support: GaugeProduct.lean, SHA256 998b84e8cfc4f3cdc6a7ff8d7802d599fdbddbd0abf8f48a8d066537026b0c87 -/
noncomputable section RefPart_GaugeProduct

/-! Native product and power-derivative identities used by the conformal gauge. -/


open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def nativeGradientPairing (g : Metric (n := n) (M := M)) (f h : M → ℝ) (x : M) : ℝ :=
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩;
  ⟪TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) f x,
    TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) h x⟫_ℝ

/-- Multiplication intertwines the actual scalar operators with its explicit first-order term. -/
theorem schrodinger_mul (g : Metric (n := n) (M := M)) (q c v : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    schrodinger g q (c * v) x = c x * schrodinger g 0 v x +
      v x * schrodinger g q c x - 2 * nativeGradientPairing g c v x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1))) (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)
  dsimp only [schrodinger, nativeGradientPairing]
  rw [TauCeti.Manifold.laplaceBeltrami_mul (𝓡∂ (n + 1))
    (hc.of_le (by decide)) (hv.of_le (by decide))]
  simp only [Pi.zero_apply, Pi.mul_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The metric gradient pairing of a positive power has its actual chain-rule coefficient. -/
theorem nativeGradientPairing_rpow_left (g : Metric (n := n) (M := M))
    (c v : M → ℝ) (s : ℝ) (x : M)
    (hc : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) c x) (hcx : 0 < c x) :
    nativeGradientPairing g (fun z => Real.rpow (c z) s) v x =
      (s * Real.rpow (c x) (s - 1)) * nativeGradientPairing g c v x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  dsimp only [nativeGradientPairing]
  rw [TauCeti.Manifold.inner_mgradient, TauCeti.Manifold.inner_mgradient]
  have hφ := Real.hasDerivAt_rpow_const (p := s) (Or.inl hcx.ne')
  have hchain := TauCeti.mvfderiv_scalar_comp hc hφ.differentiableAt
  change mvfderiv (𝓡∂ (n + 1)) ((fun r : ℝ => r ^ s) ∘ c) x _ = _
  rw [hchain, hφ.deriv, smul_apply, smul_eq_mul]
  rfl

end ConformalPoisson

end RefPart_GaugeProduct

/- Interface support: ConformalOperator.lean, SHA256 b011f7d7567b437a85a0ac4c63fb87cd1c17451ce7df93a0ec8718f321500f45 -/
noncomputable section RefPart_ConformalOperator

/-! The native scalar operator under an actual positive conformal metric rescaling. -/


open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem schrodinger_rescale_zero
    (g : Metric (n := n) (M := M)) (a v : M → ℝ)
    (ha : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ a) (hapos : ∀ x, 0 < a x)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    schrodinger (g.rescale a ha hapos) 0 v x = (a x)⁻¹ *
      (schrodinger g 0 v x - ((n + 1 : ℝ) - 2) / (2 * a x) * nativeGradientPairing g a v x) := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1))) (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)
  have hL := g.laplaceBeltrami_rescale (by decide : (1 : ℕ∞ω) ≤ ∞) ha hapos
    ((hv.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).contMDiffAt (x := x))
  dsimp only [schrodinger, nativeGradientPairing]
  rw [hL]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  simp only [hdim, Nat.cast_add, Nat.cast_one,
    Pi.zero_apply, zero_mul, add_zero]
  ring

end ConformalPoisson

end RefPart_ConformalOperator

/- Interface support: ConformalGauge.lean, SHA256 4e04f3f92e335c2828476d3b7343293d428beed06e7e0a2a3af4fade7cbddca6 -/
noncomputable section RefPart_ConformalGauge

/-! The conformal gauge of the actual metric and independent potential. -/


open Bundle
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def conformalGaugeExponent (n : ℕ) : ℝ := 4 / ((n + 1 : ℝ) - 2)

def conformalGaugeMetric (g : Metric (n := n) (M := M)) (c : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x) :
    Metric (n := n) (M := M) :=
  g.rescale (fun x => c x ^ conformalGaugeExponent n)
    (hc.rpow_const_of_ne (fun x => (hcpos x).ne') _)
    (fun x => Real.rpow_pos_of_pos (hcpos x) _)

/-- This inverse-product form is subsequently identified with the paper's power formula. -/
def conformalGaugePotential (g : Metric (n := n) (M := M)) (q c : M → ℝ) : M → ℝ :=
  fun x => (c x * c x ^ conformalGaugeExponent n)⁻¹ * schrodinger g q c x

theorem schrodinger_eq_zero_potential_add (g : Metric (n := n) (M := M))
    (q v : M → ℝ) (x : M) :
    schrodinger g q v x = schrodinger g 0 v x + q x * v x := by
  dsimp only [schrodinger]
  simp only [Pi.zero_apply, zero_mul, add_zero]

/-- Exact native intertwining; no potential sign or nonresonance hypothesis is used. -/
theorem schrodinger_conformalGauge
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c v : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (x : M) :
    schrodinger (conformalGaugeMetric g c hc hcpos) (conformalGaugePotential g q c) v x =
      (c x * c x ^ conformalGaugeExponent n)⁻¹ * schrodinger g q (c * v) x := by
  let a : M → ℝ := fun z => c z ^ conformalGaugeExponent n
  have ha : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ a :=
    hc.rpow_const_of_ne (fun z => (hcpos z).ne') _
  have hapos : ∀ z, 0 < a z := fun z => Real.rpow_pos_of_pos (hcpos z) _
  rw [schrodinger_eq_zero_potential_add]
  change schrodinger (g.rescale a ha hapos) 0 v x +
    (c x * a x)⁻¹ * schrodinger g q c x * v x = _
  rw [schrodinger_rescale_zero g a v ha hapos hv x]
  have hpair : nativeGradientPairing g a v x =
      (conformalGaugeExponent n * c x ^ (conformalGaugeExponent n - 1)) *
        nativeGradientPairing g c v x := by
    simpa only [a, Real.rpow_eq_pow] using nativeGradientPairing_rpow_left g c v
      (conformalGaugeExponent n) x (hc.mdifferentiableAt (by decide)) (hcpos x)
  rw [hpair, schrodinger_mul g q c v hc hv x]
  have hpower : c x ^ (conformalGaugeExponent n - 1) = a x / c x := by
    rw [Real.rpow_sub (hcpos x), Real.rpow_one]
  rw [hpower]
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hdim
  have hd : ((n + 1 : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  have hc0 := (hcpos x).ne'
  have ha0 := (hapos x).ne'
  change (a x)⁻¹ * (schrodinger g 0 v x - ((n + 1 : ℝ) - 2) / (2 * a x) *
    ((4 / ((n + 1 : ℝ) - 2) * (a x / c x)) * nativeGradientPairing g c v x)) +
    (c x * a x)⁻¹ * schrodinger g q c x * v x =
    (c x * a x)⁻¹ * (c x * schrodinger g 0 v x +
      v x * schrodinger g q c x - 2 * nativeGradientPairing g c v x)
  field_simp
  ring

/-- The inverse-product potential is exactly the power and exponent in Theorem 1.1. -/
theorem conformalGaugePotential_eq_paper
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c : M → ℝ)
    (x : M) (hcpos : 0 < c x) :
    conformalGaugePotential g q c x =
      Real.rpow (c x) (-((n + 1 : ℝ) + 2) / ((n + 1 : ℝ) - 2)) * schrodinger g q c x := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hdim
  have hd : ((n + 1 : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  have hexp : -((n + 1 : ℝ) + 2) / ((n + 1 : ℝ) - 2) =
      -(1 + conformalGaugeExponent n) := by
    unfold conformalGaugeExponent
    field_simp
    ring
  rw [hexp, Real.rpow_eq_pow, Real.rpow_neg hcpos.le, Real.rpow_add hcpos, Real.rpow_one]
  rfl

end ConformalPoisson

end RefPart_ConformalGauge

/- Interface support: LocalMetricAnalyticity.lean, SHA256 5a8843706119f113a9d0292a41766f1b29a1aac8e417edf7567b4e72e4ec84b8 -/
noncomputable section RefPart_LocalMetricAnalyticity

/-! Local analyticity of an actual smooth metric and its conformal gauge. -/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def MetricAnalyticOn (g : Metric (n := n) (M := M)) (U : Set M) : Prop :=
  ContMDiffOn (𝓡∂ (n + 1))
    ((𝓡∂ (n + 1)).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ]
      (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ)) ω
    (fun x => TotalSpace.mk' ((EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ]
      (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ) x (g.inner x)) U

theorem metricAnalyticOn_of_analytic (g : Metric (n := n) (M := M) ω) (U : Set M) :
    MetricAnalyticOn (g.ofLE (by decide)) U := by
  simpa only [MetricAnalyticOn, ContMDiffRiemannianMetric.ofLE_inner] using g.contMDiff.contMDiffOn (s := U)

theorem MetricAnalyticOn.conformalGauge
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M) (hg : MetricAnalyticOn g U)
    (c : M → ℝ) (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hpos : ∀ x, 0 < c x)
    (hcanalytic : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω c U) :
    MetricAnalyticOn (conformalGaugeMetric g c hc hpos) U := by
  have hpow : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω
      (fun z => c z ^ conformalGaugeExponent n) U := by
    intro z hz
    exact (((hcanalytic z hz).contMDiffAt (U.isOpen.mem_nhds hz)).rpow_const_of_ne
      (hpos z).ne' _).contMDiffWithinAt
  have hfield : ContMDiffOn (𝓡∂ (n + 1))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ)) ω
      (fun z => TotalSpace.mk' ((EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ]
        (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ) z
          (c z ^ conformalGaugeExponent n • g.inner z)) U := hpow.smul_section hg
  unfold MetricAnalyticOn
  apply hfield.congr
  intro z hz
  congr 1
  ext v w
  simp only [conformalGaugeMetric, ContMDiffRiemannianMetric.rescale_inner,
    smul_apply, smul_eq_mul]

end ConformalPoisson

end RefPart_LocalMetricAnalyticity

/- Interface support: AnalyticMetricCoordinates.lean, SHA256 d05f3cc121661c65778e2872ca2bc6fd8455ba4adf3ca8364c88331c9d2530dc -/
noncomputable section RefPart_AnalyticMetricCoordinates

/-! Read the actual native analytic metric section in its tangent-bundle tensor
trivialization and then in the boundary chart. This fixes the coordinate tensor
whose ambient extension is used later. -/


open Bundle Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

abbrev CoordinateBilinear (n : ℕ) :=
  (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ]
    (EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ

def metricTensorRead (g : Metric (n := n) (M := M)) (α y : M) : CoordinateBilinear n :=
  (trivializationAt (CoordinateBilinear n)
    (fun x : M => TangentSpace (𝓡∂ (n + 1)) x →L[ℝ]
      TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] ℝ) α
    (TotalSpace.mk' (CoordinateBilinear n) y (g.inner y))).2

theorem metricTensorRead_apply (g : Metric (n := n) (M := M)) (α : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v w : EuclideanSpace ℝ (Fin (n + 1))) :
    metricTensorRead g α y v w =
      g.inner y
        ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
          (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ y v)
        ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
          (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ y w) := by
  have hb : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  simp only [metricTensorRead, hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hb hb (by simp)]
  simp [Trivialization.symmL_apply _ hb]

theorem metricTensorRead_symmetric (g : Metric (n := n) (M := M)) (α : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v w : EuclideanSpace ℝ (Fin (n + 1))) :
    metricTensorRead g α y v w = metricTensorRead g α y w v := by
  rw [metricTensorRead_apply g α hy, metricTensorRead_apply g α hy]
  exact g.symm y _ _

theorem metricTensorRead_pos (g : Metric (n := n) (M := M)) (α : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    0 < metricTensorRead g α y v v := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
    (TangentSpace (𝓡∂ (n + 1))) α
  have hb : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  let C := e.continuousLinearEquivAt ℝ y hb
  have heq : (C.symm : EuclideanSpace ℝ (Fin (n + 1)) →
      TangentSpace (𝓡∂ (n + 1)) y) = e.symmL ℝ y :=
    e.symm_continuousLinearEquivAt_eq hb
  rw [metricTensorRead_apply g α hy]
  apply g.pos y _
  change e.symmL ℝ y v ≠ 0
  rw [← heq]
  exact C.symm.map_ne_zero_iff.mpr hv

theorem metricTensorRead_contMDiffAt
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : M} (hα : α ∈ U) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, CoordinateBilinear n) ω
      (metricTensorRead g α) α := by
  have hs := (hg α hα).contMDiffAt (U.isOpen.mem_nhds hα)
  exact (contMDiffAt_section_iff α).mp hs

theorem metricTensorRead_analyticWithinAt_chart
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : M} (hα : α ∈ U) :
    AnalyticWithinAt ℝ
      (metricTensorRead g α ∘ (extChartAt (𝓡∂ (n + 1)) α).symm)
      (range (𝓡∂ (n + 1))) (extChartAt (𝓡∂ (n + 1)) α α) := by
  have hread := metricTensorRead_contMDiffAt g U hg hα
  have hcoord := contMDiffAt_iff_source.mp hread
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcoord
  exact hcoord.analyticWithinAt

end ConformalPoisson

end RefPart_AnalyticMetricCoordinates

/- Interface support: NativeMetricExtension.lean, SHA256 1906b61b6c5a99ab444857ed3b3dcf19329806291e6b538241a585806ece3809 -/
noncomputable section RefPart_NativeMetricExtension

/-! A positive symmetric analytic extension of the SAME native coordinate metric
from its actual boundary chart target to a full ambient neighborhood. -/


open Bundle Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem exists_native_metric_tensor_extension
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : M} (hα : α ∈ U) :
    ∃ (H : EuclideanSpace ℝ (Fin (n + 1)) → CoordinateBilinear n)
      (V : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      IsOpen V ∧ extChartAt (𝓡∂ (n + 1)) α α ∈ V ∧ AnalyticOnNhd ℝ H V ∧
      EqOn (metricTensorRead g α ∘ (extChartAt (𝓡∂ (n + 1)) α).symm) H
        (extChartAt (𝓡∂ (n + 1)) α).target ∧
      (∀ z v w, H z v w = H z w v) ∧
      ∀ z ∈ V, ∀ v : EuclideanSpace ℝ (Fin (n + 1)), v ≠ 0 → 0 < H z v v := by
  let e := extChartAt (𝓡∂ (n + 1)) α
  have hcenter : e α ∈ e.target := e.map_source (by
    rw [extChartAt_source]
    exact mem_chart_source _ _)
  have hwithin : AnalyticWithinAt ℝ (metricTensorRead g α ∘ e.symm) e.target (e α) :=
    (metricTensorRead_analyticWithinAt_chart g U hg hα).mono (extChartAt_target_subset_range α)
  have hsymm : ∀ z ∈ insert (e α) e.target, ∀ v w,
      (metricTensorRead g α ∘ e.symm) z v w =
        (metricTensorRead g α ∘ e.symm) z w v := by
    intro z hz v w
    have hz' : z ∈ e.target := (insert_eq_of_mem hcenter ▸ hz)
    have hy : e.symm z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
      simpa only [e, extChartAt_source] using e.map_target hz'
    exact metricTensorRead_symmetric g α hy v w
  have hpos : ∀ v : EuclideanSpace ℝ (Fin (n + 1)), v ≠ 0 →
      0 < (metricTensorRead g α ∘ e.symm) (e α) v v := by
    intro v hv
    dsimp only [Function.comp_apply]
    rw [e.left_inv (by rw [extChartAt_source]; exact mem_chart_source _ _)]
    exact metricTensorRead_pos g α (mem_chart_source _ _) v hv
  obtain ⟨H, V, hV, hcV, hH, heq, hsymmH, hposH⟩ :=
    exists_analytic_positive_symmetric_extension hwithin hsymm hpos
  exact ⟨H, V, hV, hcV, hH, heq.mono (subset_insert _ _), hsymmH, hposH⟩

end ConformalPoisson

end RefPart_NativeMetricExtension

/- Interface support: AnalyticAmbientMetric.lean, SHA256 41b5004974d5b77e3f9d7ccd801e7349c4040f439aae10f9501261c39ac4188f -/
noncomputable section RefPart_AnalyticAmbientMetric

/-! Turn a positive symmetric analytic tensor on an open model-space domain into
an actual analytic native Riemannian metric on that boundaryless open manifold. -/


open Bundle Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def modelTensorNative (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  (NormedSpace.fromTangentSpace x).symm.arrowCongr
    ((NormedSpace.fromTangentSpace x).symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (H x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem modelTensorNative_apply (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    modelTensorNative H x v w =
      H x (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := rfl

omit [FiniteDimensional ℝ E] in
theorem analytic_tensor_contMDiffAt_section
    {H : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hH : AnalyticAt ℝ H x) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ω
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : E => TangentSpace 𝓘(ℝ, E) z →L[ℝ]
          TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) y (modelTensorNative H y)) x := by
  rw [contMDiffAt_section_iff]
  convert hH.contDiffAt.contMDiffAt using 1
  funext y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  simp only [ContinuousLinearMap.comp]
  change H y v w = H y v w
  rfl

/-- The actual analytic ambient metric obtained from the extended tensor. -/
def analyticAmbientMetric
    (V : TopologicalSpace.Opens E) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : AnalyticOnNhd ℝ H V) (hsymm : ∀ x ∈ V, ∀ v w, H x v w = H x w v)
    (hpos : ∀ x ∈ V, ∀ v : E, v ≠ 0 → 0 < H x v v) :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) ω E (fun x : V => TangentSpace 𝓘(ℝ, E) x) where
  inner := TauCeti.Manifold.restrictOpenTangentSpaceBilinear (modelTensorNative H) V
  symm x v w := by
    simp only [TauCeti.Manifold.restrictOpenTangentSpaceBilinear_apply, modelTensorNative_apply]
    exact hsymm x x.property _ _
  pos x v hv := by
    simp only [TauCeti.Manifold.restrictOpenTangentSpaceBilinear_apply, modelTensorNative_apply]
    exact hpos x x.property _
      ((NormedSpace.fromTangentSpace (x : E)).map_ne_zero_iff.mpr
        ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x).map_ne_zero_iff.mpr hv))
  isVonNBounded x := by
    let A := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x).trans
      (NormedSpace.fromTangentSpace (x : E))
    have heq : {v | TauCeti.Manifold.restrictOpenTangentSpaceBilinear
        (modelTensorNative H) V x v v < 1} = A.symm '' {v : E | H x v v < 1} := by
      rw [ContinuousLinearEquiv.image_symm_eq_preimage]
      ext v
      simp only [mem_ofPred_eq, mem_preimage,
        TauCeti.Manifold.restrictOpenTangentSpaceBilinear_apply, modelTensorNative_apply]
      rfl
    rw [heq]
    exact ((H x).isVonNBounded_setOf_lt_one_of_pos (hpos x x.property)).image
      A.symm.toContinuousLinearMap
  contMDiff x := TauCeti.Manifold.contMDiffAt_restrictOpenTangentSpaceBilinear
    (analytic_tensor_contMDiffAt_section (hH x x.property))

theorem analyticAmbientMetric_inner
    (V : TopologicalSpace.Opens E) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : AnalyticOnNhd ℝ H V) (hsymm : ∀ x ∈ V, ∀ v w, H x v w = H x w v)
    (hpos : ∀ x ∈ V, ∀ v : E, v ≠ 0 → 0 < H x v v)
    (x : V) (v w : TangentSpace 𝓘(ℝ, E) x) :
    (analyticAmbientMetric V H hH hsymm hpos).inner x v w =
      H x (NormedSpace.fromTangentSpace (x : E)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x v))
        (NormedSpace.fromTangentSpace (x : E)
          (TauCeti.Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x w)) := by
  exact TauCeti.Manifold.restrictOpenTangentSpaceBilinear_apply (modelTensorNative H) V x v w

end ConformalPoisson

end RefPart_AnalyticAmbientMetric

/- Interface support: NativeAmbientMetric.lean, SHA256 9eee525918ca31c94e74d031ba29d8935070be4700bfeb3dc6c54d71f69ac7bf -/
noncomputable section RefPart_NativeAmbientMetric

/-! Bind one actual native analytic ambient metric to the original boundary
metric in its actual tangent coordinates. -/


open Bundle Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

structure NativeMetricAmbientExtension (g : Metric (n := n) (M := M)) (α : M) where
  domain : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))
  base_mem : extChartAt (𝓡∂ (n + 1)) α α ∈ domain
  tensor : EuclideanSpace ℝ (Fin (n + 1)) → CoordinateBilinear n
  analytic : AnalyticOnNhd ℝ tensor domain
  symmetric : ∀ z v w, tensor z v w = tensor z w v
  positive : ∀ z ∈ domain, ∀ v : EuclideanSpace ℝ (Fin (n + 1)), v ≠ 0 → 0 < tensor z v v
  agrees : EqOn (metricTensorRead g α ∘ (extChartAt (𝓡∂ (n + 1)) α).symm) tensor
    (extChartAt (𝓡∂ (n + 1)) α).target

def NativeMetricAmbientExtension.metric
    {g : Metric (n := n) (M := M)} {α : M} (R : NativeMetricAmbientExtension g α) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun z : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) z) :=
  analyticAmbientMetric R.domain R.tensor R.analytic (fun z _ => R.symmetric z) R.positive

theorem NativeMetricAmbientExtension.inner_agrees
    {g : Metric (n := n) (M := M)} {α : M} (R : NativeMetricAmbientExtension g α)
    (z : R.domain) (hz : (z : EuclideanSpace ℝ (Fin (n + 1))) ∈
      (extChartAt (𝓡∂ (n + 1)) α).target)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) z) :
    R.metric.inner z v w =
      g.inner ((extChartAt (𝓡∂ (n + 1)) α).symm z)
        ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
          (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ
          ((extChartAt (𝓡∂ (n + 1)) α).symm z)
          (NormedSpace.fromTangentSpace (z : EuclideanSpace ℝ (Fin (n + 1)))
            (TauCeti.Manifold.tangentSpaceOpenEquiv z v)))
        ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
          (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ
          ((extChartAt (𝓡∂ (n + 1)) α).symm z)
          (NormedSpace.fromTangentSpace (z : EuclideanSpace ℝ (Fin (n + 1)))
            (TauCeti.Manifold.tangentSpaceOpenEquiv z w))) := by
  rw [NativeMetricAmbientExtension.metric, analyticAmbientMetric_inner, ← R.agrees hz]
  exact metricTensorRead_apply g α
    (by simpa only [extChartAt_source] using (extChartAt (𝓡∂ (n + 1)) α).map_target hz) _ _

theorem exists_native_metric_ambient_extension
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : M} (hα : α ∈ U) :
    Nonempty (NativeMetricAmbientExtension g α) := by
  obtain ⟨H, V, hV, hcV, hH, heq, hsymm, hpos⟩ :=
    exists_native_metric_tensor_extension g U hg hα
  exact ⟨⟨⟨V, hV⟩, hcV, H, hH, hsymm, hpos, heq⟩⟩

end ConformalPoisson

end RefPart_NativeAmbientMetric

/- Interface support: AmbientCoordinateNormal.lean, SHA256 133b0c3073e1e46259455175808a237cd126e07493daea4d9f6f0a2665a6eb25 -/
noncomputable section RefPart_AmbientCoordinateNormal

/-! The actual analytic inward unit gradient of the zeroth ambient coordinate. -/


open Bundle Set TauCeti.Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ}

def ambientBoundaryFunction
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))) : V → ℝ :=
  EuclideanSpace.proj (0 : Fin (n + 1)) ∘ (Subtype.val : V → EuclideanSpace ℝ (Fin (n + 1)))

theorem contMDiff_ambientBoundaryFunction
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ) ω (ambientBoundaryFunction V) :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff.comp contMDiff_subtype_val

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_ambientBoundaryFunction
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))) (x : V)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (ambientBoundaryFunction V) x v =
      (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
        (tangentSpaceOpenEquiv x v)) 0 := by
  unfold ambientBoundaryFunction
  rw [(EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).mvfderiv_comp_apply
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      ((contMDiff_subtype_val (n := ω)).mdifferentiable (by decide) x) v]
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_subtype_val]
  rfl

theorem mvfderiv_ambientBoundaryFunction_ne_zero
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))) (x : V) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (ambientBoundaryFunction V) x ≠ 0 := by
  let A := (tangentSpaceOpenEquiv (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) x).trans
    (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1))))
  let e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  intro h
  have heval := congrArg (fun L => L (A.symm e₀)) h
  rw [mvfderiv_ambientBoundaryFunction] at heval
  have hround : NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
      (tangentSpaceOpenEquiv x (A.symm e₀)) = e₀ := A.apply_symm_apply e₀
  rw [hround] at heval
  simp [e₀] at heval

section NativeNormal

variable (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]


def ambientInwardNormal (x : V) : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x :=
  NormedSpace.normalize (mgradient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (ambientBoundaryFunction V) x)

theorem ambientBoundaryGradient_ne_zero (x : V) :
    mgradient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (ambientBoundaryFunction V) x ≠ 0 :=
  mt mgradient_eq_zero_iff.mp (mvfderiv_ambientBoundaryFunction_ne_zero V x)

theorem contMDiff_ambientInwardNormal
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))).tangent ω
      (fun x => (⟨x, ambientInwardNormal V x⟩ : TangentBundle
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) V)) := by
  apply contMDiff_normalize_mgradient (n := ω)
  · simpa using contMDiff_ambientBoundaryFunction V
  · exact ambientBoundaryGradient_ne_zero V

theorem ambientInwardNormal_unit (x : V) : ‖ambientInwardNormal V x‖ = 1 :=
  NormedSpace.norm_normalize (ambientBoundaryGradient_ne_zero V x)

theorem ambientInwardNormal_coordinate_pos (x : V) :
    0 < (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
      (tangentSpaceOpenEquiv x (ambientInwardNormal V x))) 0 := by
  rw [← mvfderiv_ambientBoundaryFunction]
  rw [ambientInwardNormal, mvfderiv_normalize_mgradient]
  exact norm_pos_iff.mpr (ambientBoundaryGradient_ne_zero V x)

theorem ambientInwardNormal_orthogonal (x : V)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)
    (hv : (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin (n + 1)))
      (tangentSpaceOpenEquiv x v)) 0 = 0) :
    inner ℝ (ambientInwardNormal V x) v = 0 := by
  rw [ambientInwardNormal, inner_normalize_mgradient, mvfderiv_ambientBoundaryFunction, hv,
    mul_zero]

end NativeNormal

end ConformalPoisson

end RefPart_AmbientCoordinateNormal

/- Interface support: ContinuousMultilinearPaths.lean, SHA256 d8f0f6912a28bb33325be3121f265dd489a7e2160ca51456b197e270a563ffd8 -/
noncomputable section RefPart_ContinuousMultilinearPaths

/-!
Pointwise lifting of an actual continuous multilinear map to continuous paths,
with the operator-norm bound needed for an analytic power-series lift.
-/


open scoped BigOperators

namespace ConformalPoisson

variable {𝕜 E F K ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace K] [CompactSpace K] [Fintype ι] [DecidableEq ι]

omit [CompactSpace K] [Fintype ι] in
private theorem eval_update_paths (u : ι → C(K, E)) (i : ι) (f : C(K, E)) (t : K) :
    (fun j => Function.update u i f j t) = Function.update (fun j => u j t) i (f t) := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj]

def multilinearPaths (B : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    (ι → C(K, E)) →ₘₗ[𝕜] C(K, F) where
  toFun u := ⟨fun t => B (fun i => u i t), B.cont.comp (continuous_pi fun i => (u i).continuous)⟩
  map_update_add' u i f g := by
    apply ContinuousMap.ext
    intro t
    change B (fun j => Function.update u i (f + g) j t) =
      B (fun j => Function.update u i f j t) + B (fun j => Function.update u i g j t)
    rw [eval_update_paths, eval_update_paths, eval_update_paths]
    exact B.map_update_add _ _ _ _
  map_update_smul' u i a f := by
    apply ContinuousMap.ext
    intro t
    change B (fun j => Function.update u i (a • f) j t) =
      a • B (fun j => Function.update u i f j t)
    rw [eval_update_paths, eval_update_paths]
    exact B.map_update_smul _ _ _ _

omit [DecidableEq ι] in
theorem norm_multilinearPaths_le (B : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)
    (u : ι → C(K, E)) : ‖multilinearPaths B u‖ ≤ ‖B‖ * ∏ i, ‖u i‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro t
  apply (B.le_opNorm _).trans
  gcongr with i
  exact ContinuousMap.norm_coe_le_norm (u i) t

def continuousMultilinearPaths (B : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => C(K, E)) C(K, F) :=
  (multilinearPaths B).mkContinuous ‖B‖ (norm_multilinearPaths_le B)

omit [DecidableEq ι] in
@[simp] theorem continuousMultilinearPaths_apply
    (B : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (u : ι → C(K, E)) (t : K) :
    continuousMultilinearPaths B u t = B (fun i => u i t) := rfl

omit [DecidableEq ι] in
theorem norm_continuousMultilinearPaths_le
    (B : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    ‖continuousMultilinearPaths (K := K) B‖ ≤ ‖B‖ := by
  change ‖(multilinearPaths (K := K) B).mkContinuous ‖B‖
    (norm_multilinearPaths_le (K := K) B)‖ ≤ ‖B‖
  exact (multilinearPaths (K := K) B).mkContinuous_norm_le (norm_nonneg B)
    (norm_multilinearPaths_le (K := K) B)

end ConformalPoisson

end RefPart_ContinuousMultilinearPaths

/- Interface support: AnalyticPaths.lean, SHA256 942f4ee4eb2caac182fd56adb71318b8d7f4369fac42ac925f948ef3e974b418 -/
noncomputable section RefPart_AnalyticPaths

/-!
An analytic germ lifts to an analytic superposition germ at a constant continuous
path. Norm control of the lifted coefficients preserves the convergence radius;
the existing compact-family series theorem supplies uniform-norm convergence.
-/


open Filter
open scoped Topology ENNReal NNReal

namespace ConformalPoisson

variable {𝕜 E F K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace K] [CompactSpace K]

def pathPowerSeries (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 C(K, E) C(K, F) :=
  fun n => continuousMultilinearPaths (p n)

theorem radius_le_pathPowerSeries (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius ≤ (pathPowerSeries (K := K) p).radius :=
  FormalMultilinearSeries.radius_le_of_le fun n => norm_continuousMultilinearPaths_le (p n)

variable [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
theorem HasFPowerSeriesOnBall.paths_at_constant
    {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fun u : C(K, E) => ContinuousMap.mkD (fun t => f (u t)) 0)
      (pathPowerSeries p) (ContinuousMap.const K x) r := by
  refine ⟨hf.r_le.trans (radius_le_pathPowerSeries p), hf.r_pos, ?_⟩
  intro h hh
  have hs : (‖h‖₊ : ℝ≥0∞) < r := by
    simpa only [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm] using hh
  let g := ContinuousMap.const K x + h
  have hg : ∀ t, ‖g t - x‖ ≤ ‖h‖₊ := by
    intro t
    simpa only [g, ContinuousMap.add_apply, ContinuousMap.const_apply, add_sub_cancel_left, coe_nnNorm]
      using ContinuousMap.norm_coe_le_norm h t
  have hct : Continuous (fun t => f (g t)) :=
    hf.continuousOn.comp_continuous g.continuous (fun t => by
      rw [Metric.mem_eball, eDist_eq_eNorm_sub]
      exact lt_of_le_of_lt (by exact_mod_cast hg t) hs)
  have hsum := hf.hasSum_compact g hs hg
  convert hsum using 1
  · funext n
    apply ContinuousMap.ext
    intro t
    simp only [pathPowerSeries, continuousMultilinearPaths_apply, g,
      ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.coe_mk, add_sub_cancel_left]
  · exact ContinuousMap.mkD_of_continuous hct

theorem analyticAt_paths_at_constant {f : E → F} {x : E} (hf : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fun u : C(K, E) => ContinuousMap.mkD (fun t => f (u t)) 0)
      (ContinuousMap.const K x) := by
  obtain ⟨p, r, hp⟩ := hf
  exact ⟨pathPowerSeries p, r, ConformalPoisson.HasFPowerSeriesOnBall.paths_at_constant hp⟩

end ConformalPoisson

end RefPart_AnalyticPaths

/- Interface support: AnalyticImplicitRegularity.lean, SHA256 907e167cc67c2c4c1904bf7184a3a46117d62d3915cc7272e45665142d0ba573 -/
noncomputable section RefPart_AnalyticImplicitRegularity

/-!
A continuous solution of an analytic implicit equation with invertible partial
derivative inherits analyticity. This upgrades an already existing smooth Picard
solution family without constructing a second ODE solution or changing its data.
-/


open Filter
open scoped Topology ContDiff

namespace ConformalPoisson

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem analyticAt_of_implicit_equation
    (R : E × F → F) (g : E → F) (p₀ : E)
    (hR : AnalyticAt ℝ R (p₀, g p₀)) (hg : ContinuousAt g p₀)
    (hinv : (fderiv ℝ R (p₀, g p₀) ∘L ContinuousLinearMap.inr ℝ E F).IsInvertible)
    (heq : ∀ᶠ p in 𝓝 p₀, R (p, g p) = R (p₀, g p₀)) :
    AnalyticAt ℝ g p₀ := by
  have hω : ContDiffAt ℝ ω R (p₀, g p₀) := hR.contDiffAt
  have hφ := (hω.contDiffAt_implicitFunction (by decide) hinv).analyticAt
  have hnear := (continuousAt_id.prodMk hg).eventually
    (hω.eventually_apply_eq_iff_implicitFunction (by decide) hinv)
  apply hφ.congr
  filter_upwards [hnear, heq] with p hp heqp
  exact hp.mp heqp

end ConformalPoisson

end RefPart_AnalyticImplicitRegularity

/- Interface support: AnalyticPicardResidual.lean, SHA256 9c814c9f9f00c84d13a3c8872d7c83f19260628fc4bb351ee6009d413cc12e13 -/
noncomputable section RefPart_AnalyticPicardResidual
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see External/LICENSE.tauceti.

The parameter/path map and residual derivative argument are adapted from
TauCeti/Analysis/ODE/SmoothParameter.lean at Tau Ceti commit
4d91513e4d30746eb1fa96658c18e051c772e55e. Its helpers are private and its public
parameter-dependence theorem excludes analytic omega. The analytic residual proof
below instead uses the project's constant-path power-series lift.
-/
open Filter Set Topology
open scoped ContDiff

namespace ConformalPoisson

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parameter and state path, as one bounded linear input path. -/
def picardParameterPath : E × C(Icc (0 : ℝ) 1, F) →L[ℝ] C(Icc (0 : ℝ) 1, E × F) :=
  (((ContinuousLinearMap.inl ℝ E F).compLeftContinuous ℝ _).comp
    (ContinuousLinearMap.const ℝ _)).coprod
      ((ContinuousLinearMap.inr ℝ E F).compLeftContinuous ℝ _)

@[simp] theorem picardParameterPath_apply (p : E × C(Icc (0 : ℝ) 1, F)) (t : Icc (0 : ℝ) 1) :
    picardParameterPath p t = (p.1, p.2 t) := by
  simp [picardParameterPath]

/-- The actual Picard residual, totalized outside the continuous-composition domain. -/
def analyticPicardResidual (f : E × F → F) (x₀ : F)
    (p : E × C(Icc (0 : ℝ) 1, F)) : C(Icc (0 : ℝ) 1, F) :=
  p.2 - ContinuousMap.const _ x₀ - ContinuousMap.unitIntervalIntegral
    (ContinuousMap.mkD (fun t => f (picardParameterPath p t)) 0)

theorem analyticAt_picardResidual [CompleteSpace F]
    (f : E × F → F) (p₀ : E) (x₀ : F) (hf : AnalyticAt ℝ f (p₀, x₀)) :
    AnalyticAt ℝ (analyticPicardResidual f x₀) (p₀, ContinuousMap.const _ x₀) := by
  have hinput : picardParameterPath (p₀, ContinuousMap.const (Icc (0 : ℝ) 1) x₀) =
      ContinuousMap.const _ (p₀, x₀) := by
    apply ContinuousMap.ext
    intro t
    rw [picardParameterPath_apply]
    rfl
  have hcomp := (analyticAt_paths_at_constant (K := Icc (0 : ℝ) 1) hf).comp_of_eq
    ((picardParameterPath (E := E) (F := F)).analyticAt _) hinput
  exact (analyticAt_snd.sub analyticAt_const).sub
    ((ContinuousMap.unitIntervalIntegral (E := F)).analyticAt _ |>.comp hcomp)

theorem hasStrictFDerivAt_picardResidual_path (f : E × F → F) (p₀ : E) (x₀ : F)
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    HasStrictFDerivAt (fun q : C(Icc (0 : ℝ) 1, F) => analyticPicardResidual f x₀ (p₀, q))
      (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) 1, F)) (ContinuousMap.const _ x₀) := by
  obtain ⟨U, hUsub, hUopen, hx₀U⟩ := mem_nhds_iff.mp hzero
  have heq : (fun q : C(Icc (0 : ℝ) 1, F) => q - ContinuousMap.const _ x₀) =ᶠ[
      𝓝 (ContinuousMap.const _ x₀)] (fun q => analyticPicardResidual f x₀ (p₀, q)) := by
    filter_upwards [ContinuousMap.eventually_mapsTo isCompact_univ hUopen (fun _ _ => hx₀U)] with q hq
    have hfun : (fun t : Icc (0 : ℝ) 1 => f (picardParameterPath (p₀, q) t)) = 0 := by
      funext t
      rw [picardParameterPath_apply]
      change f (p₀, q t) = 0
      exact hUsub (hq (mem_univ t))
    have hcomp : ContinuousMap.mkD (fun t => f (picardParameterPath (p₀, q) t)) 0 = 0 := by
      rw [hfun, ← ContinuousMap.coe_zero, ContinuousMap.mkD_eq_self]
    simp only [analyticPicardResidual, hcomp, map_zero, sub_zero]
  exact (hasStrictFDerivAt_sub_const (ContinuousMap.const _ x₀)).congr_of_eventuallyEq heq

theorem isInvertible_fderiv_picardResidual_path
    (f : E × F → F) (p₀ : E) (x₀ : F)
    (hR : DifferentiableAt ℝ (analyticPicardResidual f x₀) (p₀, ContinuousMap.const _ x₀))
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    (fderiv ℝ (analyticPicardResidual f x₀) (p₀, ContinuousMap.const _ x₀) ∘L
      ContinuousLinearMap.inr ℝ E C(Icc (0 : ℝ) 1, F)).IsInvertible := by
  have hpartial := hasStrictFDerivAt_picardResidual_path f p₀ x₀ hzero
  have heq := (hR.hasFDerivAt.comp (ContinuousMap.const _ x₀)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p₀ (ContinuousMap.const _ x₀))).unique hpartial.hasFDerivAt
  rw [heq]
  exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

end ConformalPoisson

end RefPart_AnalyticPicardResidual

/- Interface support: AnalyticPicardSolutions.lean, SHA256 edc9d0d660ea1f36d64c0842265dbb9568aa266b49bce885a0491658669de366 -/
noncomputable section RefPart_AnalyticPicardSolutions

/-!
Analytic parameter dependence for the SAME actual Picard solutions supplied by
Tau Ceti's smooth theorem. The analytic residual and implicit uniqueness upgrade
that existing family, preserving its domain, initial values and ODE equations.
-/


open Filter Set Topology
open scoped ContDiff

universe u

namespace ConformalPoisson

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem picardResidual_eq_zero_of_solution
    (f : E × F → F) {W : Set (E × F)} (hf : ContinuousOn f W)
    (p : E) (x₀ : F) (γ : C(Icc (0 : ℝ) 1, F))
    (hpath : ∀ t, (p, γ t) ∈ W)
    (hpicard : ∀ t : Icc (0 : ℝ) 1,
      γ t = x₀ + ∫ s in (0 : ℝ)..t, f (p, γ (projIcc 0 1 zero_le_one s))) :
    analyticPicardResidual f x₀ (p, γ) = 0 := by
  have hcont : Continuous (fun t => f (p, γ t)) :=
    hf.comp_continuous (by fun_prop) hpath
  simp only [analyticPicardResidual, picardParameterPath_apply]
  rw [ContinuousMap.mkD_of_continuous hcont]
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.zero_apply,
    ContinuousMap.unitIntervalIntegral_apply, ContinuousMap.coe_mk]
  rw [sub_sub, sub_eq_zero]
  exact hpicard t

set_option maxHeartbeats 400000 in
theorem exists_analytic_picard_solution
    (f : E × F → F) (p₀ : E) (x₀ : F) (W : Set (E × F))
    (hW : IsOpen W) (hbase : (p₀, x₀) ∈ W) (hf : AnalyticOnNhd ℝ f W)
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    ∃ (γ : E → C(Icc (0 : ℝ) 1, F)) (U : Set E),
      IsOpen U ∧ p₀ ∈ U ∧ AnalyticOnNhd ℝ γ U ∧
      γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ p ∈ U,
        (∀ t : Icc (0 : ℝ) 1, (p, γ p t) ∈ W) ∧
        (∀ t : Icc (0 : ℝ) 1, γ p t = x₀ + ∫ s in (0 : ℝ)..t,
          f (p, γ p (projIcc 0 1 zero_le_one s))) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
          (fun s => γ p (projIcc 0 1 zero_le_one s))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt
          (fun s => γ p (projIcc 0 1 zero_le_one s))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) (Ici t) t := by
  obtain ⟨γ, U, hU, hpU, hγ, hγbase, hsol⟩ := ODE.exists_contDiffOn_picard_solution
    (n := (⊤ : ℕ∞)) f p₀ x₀ hW hbase (hf.contDiffOn hW.uniqueDiffOn) hzero
  let R := analyticPicardResidual f x₀
  have hR : AnalyticAt ℝ R (p₀, γ p₀) := by
    rw [hγbase]
    exact analyticAt_picardResidual f p₀ x₀ (hf (p₀, x₀) hbase)
  have hInv : (fderiv ℝ R (p₀, γ p₀) ∘L
      ContinuousLinearMap.inr ℝ E C(Icc (0 : ℝ) 1, F)).IsInvertible := by
    rw [hγbase]
    exact isInvertible_fderiv_picardResidual_path f p₀ x₀
      (by simpa only [hγbase] using hR.differentiableAt) hzero
  have hres (p : E) (hp : p ∈ U) : R (p, γ p) = 0 :=
    picardResidual_eq_zero_of_solution f hf.continuousOn p x₀ (γ p) (hsol p hp).1 (hsol p hp).2.1
  have hγan : AnalyticAt ℝ γ p₀ := analyticAt_of_implicit_equation R γ p₀ hR
    (hγ.contDiffAt (hU.mem_nhds hpU)).continuousAt hInv (by
      filter_upwards [hU.mem_nhds hpU] with p hp
      rw [hres p hp, hres p₀ hpU])
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hγan.eventually_analyticAt
  exact ⟨γ, U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, fun p hp => hVsub hp.2,
    hγbase, fun p hp => hsol p hp.1⟩

end ConformalPoisson

end RefPart_AnalyticPicardSolutions

/- Interface support: AnalyticGlobalSolution.lean, SHA256 52a903a5e0880064955f9fe14a88127b4541ed5a334d754d33c798f49f203c2d -/
noncomputable section RefPart_AnalyticGlobalSolution
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see External/LICENSE.tauceti.

Time rescaling and the endpoint identification are adapted from
TauCeti/Analysis/ODE/InitialCondition.lean at commit
4d91513e4d30746eb1fa96658c18e051c772e55e. The new analytic regularity input
is the project's proved analytic Picard theorem.
-/
open Filter Set Topology
open scoped ContDiff NNReal

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_globalSolution_of_smul_path [CompleteSpace E] (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (x : E) (ε : ℝ) {u : ℝ → E} (hu₀ : u 0 = x)
    (hu : ContinuousOn u (Icc 0 1))
    (hu' : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u (ε • v (u s)) (Ici s) s) :
    u 1 = ODE.globalSolution v hv x ε := by
  have hflow : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ ODE.globalSolution v hv x (ε * r))
      (ε • v (ODE.globalSolution v hv x (ε * s))) s := fun s ↦ by
    simpa [Function.comp_def, mul_comm] using
      (ODE.hasDerivAt_globalSolution v hv x (ε * s)).scomp s ((hasDerivAt_id s).const_mul ε)
  have heq := ODE_solution_unique (v := fun _ z ↦ ε • v z) (K := ‖ε‖₊ * K)
    (a := 0) (b := 1) (f := u) (g := fun r ↦ ODE.globalSolution v hv x (ε * r))
    (fun _ ↦ (lipschitzWith_smul ε).comp hv) hu hu'
    (((ODE.continuous_globalSolution_apply v hv x).comp
      (continuous_const.mul continuous_id)).continuousOn)
    (fun s _ ↦ (hflow s).hasDerivWithinAt)
    (by simp [hu₀])
  simpa using heq (right_mem_Icc.2 zero_le_one)


/-- Joint analyticity of the actual globally Lipschitz flow near time zero.
Only the germ of the field at the chosen state must be analytic. -/
theorem analyticAt_globalSolution [CompleteSpace E]
    (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    {a : E} {s : Set E} (hvs : AnalyticOnNhd ℝ v s) (hs : s ∈ 𝓝 a) :
    AnalyticAt ℝ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) (a, 0) := by
  let S : Set ((E × ℝ) × E) := (fun q => q.1.1 + q.2) ⁻¹' interior s
  have hS : IsOpen S := isOpen_interior.preimage (by fun_prop)
  have hbase : ((a, (0 : ℝ)), (0 : E)) ∈ S := by
    simpa [S] using mem_interior_iff_mem_nhds.mpr hs
  have hf : AnalyticOnNhd ℝ
      (fun q : (E × ℝ) × E => q.1.2 • v (q.1.1 + q.2)) S := by
    intro q hq
    have hsum : AnalyticAt ℝ (fun r : (E × ℝ) × E => r.1.1 + r.2) q :=
      (analyticAt_fst.comp analyticAt_fst).add analyticAt_snd
    have hvcomp : AnalyticAt ℝ (fun r : (E × ℝ) × E => v (r.1.1 + r.2)) q :=
      (hvs _ (interior_subset hq)).comp (f := fun r : (E × ℝ) × E => r.1.1 + r.2) (x := q) hsum
    exact (analyticAt_snd.comp analyticAt_fst).smul hvcomp
  obtain ⟨γ, U, hU, hpU, hγU, -, hprop⟩ := exists_analytic_picard_solution
    (fun q : (E × ℝ) × E => q.1.2 • v (q.1.1 + q.2)) (a, (0 : ℝ)) (0 : E)
    S hS hbase hf (.of_forall fun _ => zero_smul ℝ _)
  have hγ : AnalyticAt ℝ γ (a, 0) := hγU _ hpU
  have hendpoint : AnalyticAt ℝ
      (fun p : E × ℝ => p.1 + γ p ⟨1, by norm_num⟩) (a, 0) := by
    have heval := ((ContinuousMap.evalCLM (R := ℝ)
      (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hγ
    exact analyticAt_fst.add (by simpa only [Function.comp_def, ContinuousMap.evalCLM_apply] using heval)
  apply hendpoint.congr
  filter_upwards [hU.mem_nhds hpU] with p hp
  obtain ⟨hpicard, -, hright⟩ := (hprop p hp).2
  have hbase : γ p ⟨0, by norm_num⟩ = 0 := by
    simpa using hpicard ⟨0, by norm_num⟩
  have hcont : ContinuousOn (fun s : ℝ => p.1 + γ p (projIcc 0 1 zero_le_one s))
      (Icc 0 1) := Continuous.continuousOn (by fun_prop)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ => p.1 + γ p (projIcc 0 1 zero_le_one r))
        (p.2 • v (p.1 + γ p (projIcc 0 1 zero_le_one s))) (Ici s) s :=
    fun s hs => (hright s hs).const_add p.1
  have heq := eq_globalSolution_of_smul_path v hv p.1 p.2
    (u := fun s : ℝ => p.1 + γ p (projIcc 0 1 zero_le_one s))
    (by simpa [projIcc_left] using congrArg (fun w : E => p.1 + w) hbase) hcont hderiv
  simpa [projIcc_right] using heq

end ConformalPoisson

end RefPart_AnalyticGlobalSolution

/- Interface support: AnalyticLocalFlow.lean, SHA256 105c2780644d905657b567bba68e7620c3283db9d5a70afe581efc91e81511ee -/
noncomputable section RefPart_AnalyticLocalFlow
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see External/LICENSE.tauceti.

The Lipschitz extension and flow totalization are adapted from
TauCeti/Analysis/ODE/LocalFlow.lean at commit
4d91513e4d30746eb1fa96658c18e051c772e55e. Joint analyticity is supplied by
the project's analytic Picard and signed-time endpoint proofs.
-/
open Filter Metric Set Topology
open scoped ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An analytic field has an actual jointly analytic local flow for both signs
of time. The globally totalized flow agrees with the field on one neighborhood. -/
theorem exists_analyticAt_localFlow (v : E → E) {a : E}
    {s : Set E} (hv : AnalyticOnNhd ℝ v s) (hs : s ∈ 𝓝 a) :
    ∃ Φ : E → ℝ → E, AnalyticAt ℝ (fun p : E × ℝ => Φ p.1 p.2) (a, 0) ∧
      (∀ x, Φ x 0 = x) ∧ (∀ x t u, Φ x (t + u) = Φ (Φ x t) u) ∧
      ∀ᶠ p in 𝓝 ((a, 0) : E × ℝ), HasDerivAt (Φ p.1) (v (Φ p.1 p.2)) p.2 := by
  have hv₁ : ContDiffAt ℝ 1 v a :=
    (hv a (mem_of_mem_nhds hs)).contDiffAt
  obtain ⟨K, t, ht, hvt⟩ := hv₁.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp (inter_mem ht hs)
  let g := v ∘ TauCeti.centeredRadialRetraction a r
  have hgK : LipschitzWith (K * 2) g :=
    (hvt.mono (fun x hx ↦ (hrt hx).1)).comp_centeredRadialRetraction hr.le
  have hgv : EqOn g v (ball a r) := fun x hx ↦ by
    simp only [g, Function.comp_apply,
      TauCeti.centeredRadialRetraction_of_mem_closedBall (ball_subset_closedBall hx)]
  have hgs : AnalyticOnNhd ℝ g (ball a r) := by
    intro x hx
    apply (hv x (hrt (ball_subset_closedBall hx)).2).congr
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (hgv hy).symm
  have hga : AnalyticAt ℝ
      (fun p : E × ℝ ↦ ODE.globalSolution g hgK p.1 p.2) (a, 0) :=
    analyticAt_globalSolution g hgK hgs (ball_mem_nhds a hr)
  refine ⟨ODE.globalSolution g hgK, hga, fun x ↦ ODE.globalSolution_zero g hgK x,
    fun x t u ↦ ODE.globalSolution_add g hgK x t u, ?_⟩
  have htends : Tendsto (fun p : E × ℝ ↦ ODE.globalSolution g hgK p.1 p.2)
      (nhds ((a, 0) : E × ℝ)) (nhds a) := by
    simpa only [ContinuousAt, ODE.globalSolution_zero] using hga.continuousAt
  filter_upwards [htends.eventually (ball_mem_nhds a hr)] with p hp
  rw [← hgv hp]
  exact ODE.hasDerivAt_globalSolution g hgK p.1 p.2

end ConformalPoisson

end RefPart_AnalyticLocalFlow

/- Interface support: AnalyticFlowDerivative.lean, SHA256 013757efc89dfb41e670ea2fd9d4393d4d90e2f886d4a45d9cc5aef3625c1a0f -/
noncomputable section RefPart_AnalyticFlowDerivative

/-! The actual initial-state and time derivatives of the analytic local flow. -/


open Filter Set Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At time zero, the joint flow derivative is the initial-state identity plus
initial velocity. This uses the actual ODE, rather than analyticity alone. -/
theorem fderiv_localFlow_zero (v : E → E) (Φ : E → ℝ → E) (a : E)
    (hΦ : DifferentiableAt ℝ (fun p : E × ℝ => Φ p.1 p.2) (a, 0))
    (hzero : ∀ x, Φ x 0 = x) (hode : HasDerivAt (Φ a) (v a) 0) (w : E × ℝ) :
    fderiv ℝ (fun p : E × ℝ => Φ p.1 p.2) (a, 0) w = w.1 + w.2 • v a := by
  rw [TauCeti.fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hΦ w]
  have hid : (fun x => Φ x 0) = id := funext hzero
  rw [hid, fderiv_id, hode.hasFDerivAt.fderiv]
  simp

end ConformalPoisson

end RefPart_AnalyticFlowDerivative

/- Interface support: AnalyticManifoldFlow.lean, SHA256 1dee07823afecaea65c4d1c99c340fd8fccf444d5df64a9e916c58c9e3bb1e60 -/
noncomputable section RefPart_AnalyticManifoldFlow
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see External/LICENSE.tauceti.

The coordinate transport and common-domain argument are adapted from
TauCeti/Geometry/Manifold/IntegralCurve/SmoothFlow.lean at commit
4d91513e4d30746eb1fa96658c18e051c772e55e. The analytic model-space flow
is the project's proved theorem, rather than an assumed analytic ODE result.
-/
open Bundle Filter Function Manifold Set Topology TauCeti TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Actual analytic local integral curves on a boundaryless analytic manifold,
with one common time domain and the same local flow law. -/
theorem exists_contMDiffAt_analytic_localFlow [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ω M] (v : (x : M) → TangentSpace I x) (a : M) {V : Set M}
    (hv : ContMDiffOn I I.tangent ω (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) V)
    (hV : V ∈ nhds a) :
    ∃ U ∈ nhds a, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧ ∃ Φ : M → ℝ → M,
      ContMDiffAt (I.prod 𝓘(ℝ)) I ω (fun p : M × ℝ ↦ Φ p.1 p.2) (a, 0) ∧
        ∀ x ∈ U, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) v s ∧
          ∀ t ∈ s, ∀ u, Φ x (t + u) = Φ (Φ x t) u := by
  let w : E → E := fun z ↦ (trivializationAt E (TangentSpace I) a
    (⟨(extChartAt I a).symm z, v ((extChartAt I a).symm z)⟩ : TangentBundle I M)).2
  let W := interior (extChartAt I a).target ∩ (extChartAt I a).symm ⁻¹' V
  have hws : ContDiffOn ℝ ω w W :=
    haveI : IsManifold I (ω + 1) M := inferInstanceAs (IsManifold I ω M)
    contDiffOn_trivializationAt_extChartAt_symm (n := ω) v a hv
  have haTarget : extChartAt I a a ∈ (extChartAt I a).target := mem_extChartAt_target a
  have hsymmV : (extChartAt I a).symm ⁻¹' V ∈ nhds (extChartAt I a a) := by
    apply (continuousAt_extChartAt_symm'' haTarget).preimage_mem_nhds
    simpa only [(extChartAt I a).left_inv (mem_extChartAt_source a)] using hV
  have hatarget : W ∈ nhds (extChartAt I a a) := inter_mem
    (isOpen_interior.mem_nhds
      (I.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (I := I)))) hsymmV
  have hwan : AnalyticAt ℝ w (extChartAt I a a) :=
    (hws.contDiffAt hatarget).analyticAt
  obtain ⟨φ, hφ, hφ0, hφadd, hφderiv⟩ :=
    ConformalPoisson.exists_analyticAt_localFlow w
      (s := {x | AnalyticAt ℝ w x}) (fun _ hx => hx) hwan.eventually_analyticAt
  have hφ' : ContDiffAt ℝ ω (fun p : E × ℝ ↦ φ p.1 p.2) (extChartAt I a a, 0) :=
    hφ.contDiffAt
  have htarget : ∀ᶠ p in nhds ((extChartAt I a a, 0) : E × ℝ),
      φ p.1 p.2 ∈ interior (extChartAt I a).target := by
    have hmem : extChartAt I a a ∈ interior (extChartAt I a).target :=
      I.isInteriorPoint_iff.mp (BoundarylessManifold.isInteriorPoint (I := I))
    apply hφ.continuousAt.eventually
    apply isOpen_interior.mem_nhds
    simpa only [hφ0] using hmem
  rw [nhds_prod_eq, eventually_prod_iff] at hφderiv htarget
  obtain ⟨u₁, hu₁, t₁, ht₁, hderiv⟩ := hφderiv
  obtain ⟨u₂, hu₂, t₂, ht₂, hmem⟩ := htarget
  let U := (extChartAt I a) ⁻¹' {z | u₁ z ∧ u₂ z} ∩ (extChartAt I a).source
  have hU : U ∈ nhds a := inter_mem
    ((continuousAt_extChartAt a).preimage_mem_nhds (inter_mem hu₁ hu₂))
    (extChartAt_source_mem_nhds (I := I) a)
  obtain ⟨s, hst, hsopen, hs0⟩ := mem_nhds_iff.mp (inter_mem ht₁ ht₂)
  refine ⟨U, hU, s, hsopen.mem_nhds hs0, hsopen,
    fun x t ↦ (extChartAt I a).symm (φ (extChartAt I a x) t),
    contMDiffAt_extChartAt_symm_comp_extChartAt_prod a hφ' (hφ0 _), ?_⟩
  intro x hx
  have hxcoord : u₁ (extChartAt I a x) ∧ u₂ (extChartAt I a x) := hx.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [hφ0]
    exact (extChartAt I a).left_inv hx.2
  · exact isMIntegralCurveOn_extChartAt_symm_comp v a hsopen
      (fun t ht ↦ hmem hxcoord.2 (hst ht).2) fun t ht ↦ hderiv hxcoord.1 (hst ht).1
  · intro t ht u
    have hφtarget : φ (extChartAt I a x) t ∈ (extChartAt I a).target :=
      interior_subset (hmem hxcoord.2 (hst ht).2)
    simp only
    rw [(extChartAt I a).right_inv hφtarget, hφadd]

end ConformalPoisson

end RefPart_AnalyticManifoldFlow

/- Interface support: AnalyticGeodesicFlow.lean, SHA256 4d37cec36894ca49c0afa30e034b086ff44a6af416909cd4033f7062ad54676c -/
noncomputable section RefPart_AnalyticGeodesicFlow

/-! The actual native geodesic spray has a jointly analytic local flow. -/


open Bundle Filter Set Topology TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ω E (fun x : M => TangentSpace I x)]

theorem exists_analytic_geodesicSpray_flow (a : TangentBundle I M) :
    ∃ U ∈ nhds a, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧
      ∃ Φ : TangentBundle I M → ℝ → TangentBundle I M,
        ContMDiffAt (I.tangent.prod 𝓘(ℝ)) I.tangent ω
          (fun p : TangentBundle I M × ℝ => Φ p.1 p.2) (a, 0) ∧
        ∀ x ∈ U, Φ x 0 = x ∧ IsMIntegralCurveOn (Φ x) (geodesicSpray I M) s ∧
          ∀ t ∈ s, ∀ u, Φ x (t + u) = Φ (Φ x t) u := by
  have hspray : ContMDiff I.tangent I.tangent.tangent ω
      (fun z : TangentBundle I M => TotalSpace.mk' (E × E) z (geodesicSpray I M z)) :=
    contMDiff_geodesicSpray (n := ω) (m := ω) (k := ω) (by simp) (by simp)
  exact exists_contMDiffAt_analytic_localFlow (geodesicSpray I M) a hspray.contMDiffOn univ_mem

/-- Jointly analytic actual geodesics with varying initial point and velocity,
on one common open time neighborhood, for the same native metric. -/
theorem exists_analytic_geodesic_family (a : TangentBundle I M) :
    ∃ U ∈ nhds a, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧
      ∃ γ : TangentBundle I M → ℝ → M,
        ContMDiffAt (I.tangent.prod 𝓘(ℝ)) I ω
          (fun p : TangentBundle I M × ℝ => γ p.1 p.2) (a, 0) ∧
        ∀ x ∈ U, IsGeodesicCurveOnFrom I (γ x) s x.proj x.2 := by
  let : IsContMDiffRiemannianBundle I 2 E (fun x : M => TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
  obtain ⟨U, hU, s, hs, hsopen, Φ, hΦ, hprop⟩ := exists_analytic_geodesicSpray_flow a
  refine ⟨U, hU, s, hs, hsopen, fun x t => (Φ x t).proj, ?_, ?_⟩
  · exact (Bundle.contMDiff_proj (fun x : M => TangentSpace I x)
      (IB := I) (n := ω)).contMDiffAt.comp (a, 0) hΦ
  · intro x hx
    exact (hprop x hx).2.1.isGeodesicCurveOnFrom_proj hsopen.uniqueDiffOn
      (mem_of_mem_nhds hs) (hprop x hx).1

end ConformalPoisson

end RefPart_AnalyticGeodesicFlow

/- Interface support: AnalyticNormalGeodesics.lean, SHA256 b076ca7d1c9db5bfa9d9dde56fb1e00c09ed1200ae81cb6d7613479326e8c199 -/
noncomputable section RefPart_AnalyticNormalGeodesics

/-! Compose the actual analytic geodesic family with the actual inward unit
normal field of the same native ambient metric. -/


open Bundle Filter Set Topology TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem exists_analytic_normal_geodesic_family (z₀ : V) :
    ∃ (U : Set V) (s : Set ℝ) (γ : V → ℝ → V),
      IsOpen U ∧ z₀ ∈ U ∧ IsOpen s ∧ (0 : ℝ) ∈ s ∧
      ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
        (fun p : V × ℝ => γ p.1 p.2) (z₀, 0) ∧
      ∀ x ∈ U, IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (γ x) s x (ambientInwardNormal V x) := by
  let N : V → TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) V :=
    fun x => ⟨x, ambientInwardNormal V x⟩
  have hN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))).tangent ω N :=
    contMDiff_ambientInwardNormal V
  obtain ⟨W, hW, s, hs, hsopen, γ, hγ, hprop⟩ := exists_analytic_geodesic_family (N z₀)
  have hpre : N ⁻¹' W ∈ nhds z₀ := hN.continuous.continuousAt.preimage_mem_nhds hW
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hpre
  refine ⟨U, s, fun x t => γ (N x) t, hU, hzU, hsopen, mem_of_mem_nhds hs, ?_, ?_⟩
  · exact hγ.comp (z₀, 0) ((hN.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
  · exact fun x hx => hprop (N x) (hUsub hx)

end ConformalPoisson

end RefPart_AnalyticNormalGeodesics

/- Interface support: BoundaryHyperplaneParam.lean, SHA256 e69798d534f2dac9f7d0e8809eeee3ce90a4cb239686e3c466f67468da22de4c -/
noncomputable section RefPart_BoundaryHyperplaneParam

/-! The actual analytic coordinate-hyperplane parameterization into the extended
metric domain, with its actual tangent differential. -/


open Bundle Set TauCeti TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ}

local notation "E₀" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F₀" => EuclideanSpace ℝ (Fin n)
local notation "I₀" => 𝓘(ℝ, E₀)
local notation "J₀" => 𝓘(ℝ, F₀)

def boundaryParameterDomain (V : TopologicalSpace.Opens E₀) : TopologicalSpace.Opens F₀ :=
  ⟨euclideanHalfSpaceBoundaryParam n ⁻¹' V, V.isOpen.preimage
    (euclideanHalfSpaceBoundaryParam n).continuous⟩

def boundaryParameter (V : TopologicalSpace.Opens E₀) (x : boundaryParameterDomain V) : V :=
  ⟨euclideanHalfSpaceBoundaryParam n (x : F₀), x.property⟩

@[simp] theorem boundaryParameter_val (V : TopologicalSpace.Opens E₀)
    (x : boundaryParameterDomain V) :
    (boundaryParameter V x : E₀) = euclideanHalfSpaceBoundaryParam n (x : F₀) := rfl

theorem contMDiff_boundaryParameter (V : TopologicalSpace.Opens E₀) :
    ContMDiff J₀ I₀ ω (boundaryParameter V) := by
  apply (TauCeti.ContMDiff.subtypeVal_comp_iff V _).mp
  exact (euclideanHalfSpaceBoundaryParam n).contMDiff.comp contMDiff_subtype_val

@[simp] theorem ambientBoundaryFunction_boundaryParameter (V : TopologicalSpace.Opens E₀)
    (x : boundaryParameterDomain V) :
    ambientBoundaryFunction V (boundaryParameter V x) = 0 := by
  simp [ambientBoundaryFunction, boundaryParameter]

theorem boundaryParameter_tangent (V : TopologicalSpace.Opens E₀)
    (x : boundaryParameterDomain V) (v : TangentSpace J₀ x) :
    NormedSpace.fromTangentSpace (boundaryParameter V x : E₀)
      (tangentSpaceOpenEquiv (boundaryParameter V x)
        (mfderiv J₀ I₀ (boundaryParameter V) x v)) =
      euclideanHalfSpaceBoundaryParam n
        (NormedSpace.fromTangentSpace (x : F₀) (tangentSpaceOpenEquiv x v)) := by
  have hB := (contMDiff_boundaryParameter V).mdifferentiable (by decide : (ω : ℕ∞ω) ≠ 0) x
  have hval := (contMDiff_subtype_val (I := I₀) (n := ω)).mdifferentiable
    (by decide : (ω : ℕ∞ω) ≠ 0) (boundaryParameter V x)
  have hleft := mvfderiv_comp_apply x hval hB v
  have hright := (euclideanHalfSpaceBoundaryParam n).mvfderiv_comp_apply
    (I := J₀) ((contMDiff_subtype_val (n := ω)).mdifferentiable
      (by decide : (ω : ℕ∞ω) ≠ 0) x) v
  rw [mvfderiv_subtype_val_apply] at hleft hright
  rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := E₀),
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := F₀),
    tangentSpaceOpenEquiv_apply, tangentSpaceOpenEquiv_apply]
  exact hleft.symm.trans hright

end ConformalPoisson

end RefPart_BoundaryHyperplaneParam

/- Interface support: BoundaryNormalMap.lean, SHA256 de28fbbe01cb13ed95e5471c9dc1279cdbd4a3d6b5e14ee5e64d13b21b19654e -/
noncomputable section RefPart_BoundaryNormalMap

/-! The actual analytic boundary normal map from the coordinate hyperplane,
formed using the same native metric and its actual normal geodesics. -/


open Bundle Filter Set Topology TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}


variable (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem exists_analytic_boundary_normal_map (x₀ : boundaryParameterDomain V) :
    ∃ (U : Set (boundaryParameterDomain V)) (s : Set ℝ)
      (Φ : boundaryParameterDomain V → ℝ → V),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen s ∧ (0 : ℝ) ∈ s ∧
      ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
        (fun p : boundaryParameterDomain V × ℝ => Φ p.1 p.2) (x₀, 0) ∧
      ∀ x ∈ U, IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Φ x) s
        (boundaryParameter V x) (ambientInwardNormal V (boundaryParameter V x)) := by
  obtain ⟨W, s, γ, hW, hxW, hs, h0s, hγ, hprop⟩ :=
    exists_analytic_normal_geodesic_family V (boundaryParameter V x₀)
  let U : Set (boundaryParameterDomain V) := boundaryParameter V ⁻¹' W
  have hU : IsOpen U := hW.preimage (contMDiff_boundaryParameter V).continuous
  have hinput : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) ((𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))).prod 𝓘(ℝ)) ω
      (fun p : boundaryParameterDomain V × ℝ => (boundaryParameter V p.1, p.2)) :=
    ((contMDiff_boundaryParameter V).comp contMDiff_fst).prodMk contMDiff_snd
  have han : ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (fun p : boundaryParameterDomain V × ℝ => γ (boundaryParameter V p.1) p.2)
      (x₀, 0) := hγ.comp (x₀, 0) hinput.contMDiffAt
  exact ⟨U, s, fun x t => γ (boundaryParameter V x) t, hU, hxW, hs, h0s, han,
    fun x hx => hprop (boundaryParameter V x) hx⟩

end ConformalPoisson

end RefPart_BoundaryNormalMap

/- Interface support: GeodesicInitialDerivative.lean, SHA256 9d18bdfaf35ccc24919a1a206f6ee53b0e06c1bf8a3e6651e36dbe232cedb36d -/
noncomputable section RefPart_GeodesicInitialDerivative

/-! The actual initial derivative of a native geodesic in an open model domain,
read in the ambient normed vector space. -/


open Bundle Filter Set Topology TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : TopologicalSpace.Opens E}
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) 1 E (fun x : V => TangentSpace 𝓘(ℝ, E) x)]

set_option backward.isDefEq.respectTransparency false in
theorem geodesic_hasDerivAt_ambient_zero
    {γ : ℝ → V} {s : Set ℝ} {x : V} {v : TangentSpace 𝓘(ℝ, E) x}
    (h : IsGeodesicCurveOnFrom 𝓘(ℝ, E) γ s x v) (hs : s ∈ nhds (0 : ℝ)) :
    HasDerivAt (fun t => (γ t : E))
      (NormedSpace.fromTangentSpace (x : E) (tangentSpaceOpenEquiv x v)) 0 := by
  have hbase := h.base_eq
  subst x
  have hc := h.hasMFDerivAt_zero hs
  have hi := ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ω)).mdifferentiable
    (by decide : (ω : ℕ∞ω) ≠ 0) (γ 0)).hasMFDerivAt
  have hF := (hi.comp 0 hc).hasFDerivAt
  have hD := (hasFDerivAt_iff_hasDerivAt (𝕜 := ℝ) (F := E)).mp hF
  convert hD using 1
  · rfl
  · simp [ContinuousLinearMap.comp, ContinuousLinearMap.smulRight,
      mfderiv_subtype_val, tangentSpaceOpenEquiv_apply,
      NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := E)]
    change (show E from v) = (show E from tangentSpaceOpenEquiv (γ 0) ((1 : ℝ) • v))
    rw [one_smul, tangentSpaceOpenEquiv_apply]

end ConformalPoisson

end RefPart_GeodesicInitialDerivative

/- Interface support: BoundaryNormalDifferential.lean, SHA256 706f13de8f375e6ad2e310eef39bd1d91e67288d5665bb53c8c24e679152ee58 -/
noncomputable section RefPart_BoundaryNormalDifferential

/-! The actual differential of the boundary normal map at time zero, from its
actual geodesic initial data and its actual time-zero boundary parameterization. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

set_option backward.isDefEq.respectTransparency false in
theorem boundaryNormalMap_mfderiv_zero
    (Φ : boundaryParameterDomain V → ℝ → V) {U : Set (boundaryParameterDomain V)}
    {s : Set ℝ} {x₀ : boundaryParameterDomain V} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hs : s ∈ nhds (0 : ℝ))
    (hΦ : ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (fun p : boundaryParameterDomain V × ℝ => Φ p.1 p.2) (x₀, 0))
    (hgeo : ∀ x ∈ U, IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Φ x) s (boundaryParameter V x) (ambientInwardNormal V (boundaryParameter V x)))
    (v : TangentSpace ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) (x₀, 0)) :
    (show EuclideanSpace ℝ (Fin (n + 1)) from
      mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (fun p : boundaryParameterDomain V × ℝ => Φ p.1 p.2) (x₀, 0) v) =
      euclideanHalfSpaceBoundaryParam n (show EuclideanSpace ℝ (Fin n) from v.1) +
        (show ℝ from v.2) • (show EuclideanSpace ℝ (Fin (n + 1)) from
          ambientInwardNormal V (boundaryParameter V x₀)) := by
  have hdΦ := hΦ.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)
  have hIncl := (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (n := ω)).mdifferentiable (by decide : (ω : ℕ∞ω) ≠ 0) (Φ x₀ 0)
  have hd := hIncl.comp (x₀, 0) hdΦ
  have hsplit := hd.mvfderiv_prod_eq_add_apply v
  have heq : (fun x : boundaryParameterDomain V => (Φ x 0 : EuclideanSpace ℝ (Fin (n + 1))))
      =ᶠ[nhds x₀] (fun x => euclideanHalfSpaceBoundaryParam n (x : EuclideanSpace ℝ (Fin n))) := by
    filter_upwards [hU.mem_nhds hx₀] with x hx
    exact congrArg Subtype.val (hgeo x hx).base_eq
  have hleft := congrArg (fun L => L v.1) (heq.mvfderiv_eq (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
  have hparam := (euclideanHalfSpaceBoundaryParam n).mvfderiv_comp_apply
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    ((contMDiff_subtype_val (n := ω)).mdifferentiable
      (by decide : (ω : ℕ∞ω) ≠ 0) x₀) v.1
  rw [mvfderiv_subtype_val_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) x₀] at hparam
  have htime := geodesic_hasDerivAt_ambient_zero (hgeo x₀ hx₀) hs
  have hright : mvfderiv 𝓘(ℝ) (fun t => (Φ x₀ t : EuclideanSpace ℝ (Fin (n + 1)))) 0 v.2 =
      (show ℝ from v.2) • (show EuclideanSpace ℝ (Fin (n + 1)) from
        ambientInwardNormal V (boundaryParameter V x₀)) := by
    rw [mvfderiv_eq_fderiv_apply, htime.hasFDerivAt.fderiv]
    simp only [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))]
    exact congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => (show ℝ from v.2) • w)
      (tangentSpaceOpenEquiv_apply (boundaryParameter V x₀)
        (ambientInwardNormal V (boundaryParameter V x₀)))
  have hchain := mvfderiv_comp_apply (x₀, 0) hIncl hdΦ v
  rw [mvfderiv_subtype_val_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1))) (Φ x₀ 0)] at hchain
  have hleft' := hleft.trans hparam
  have hsides := congrArg₂ (fun a b : EuclideanSpace ℝ (Fin (n + 1)) => a + b) hleft' hright
  exact hchain.symm.trans (hsplit.trans hsides)

end ConformalPoisson

end RefPart_BoundaryNormalDifferential

/- Interface support: BoundaryNormalLinear.lean, SHA256 be72fdabd0d34b0ab5ce756ec34a752a63df1820107e7a3153fb7f40f2ae1438 -/
noncomputable section RefPart_BoundaryNormalLinear

/-! A tangential coordinate frame together with any transverse vector is invertible. -/


open TauCeti

namespace ConformalPoisson

variable {n : ℕ}

def boundaryNormalLinear (N : EuclideanSpace ℝ (Fin (n + 1))) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanHalfSpaceBoundaryParam n).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight N)

@[simp] theorem boundaryNormalLinear_apply (N : EuclideanSpace ℝ (Fin (n + 1)))
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    boundaryNormalLinear N p = euclideanHalfSpaceBoundaryParam n p.1 + p.2 • N := by
  simp [boundaryNormalLinear]

theorem boundaryNormalLinear_injective (N : EuclideanSpace ℝ (Fin (n + 1))) (hN : N 0 ≠ 0) :
    Function.Injective (boundaryNormalLinear N) := by
  intro a b hab
  rw [boundaryNormalLinear_apply, boundaryNormalLinear_apply] at hab
  have hnormal : a.2 * N 0 = b.2 * N 0 := by
    simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) hab
  have ht : a.2 = b.2 := mul_right_cancel₀ hN hnormal
  have hb : euclideanHalfSpaceBoundaryParam n a.1 = euclideanHalfSpaceBoundaryParam n b.1 :=
    add_right_cancel (by simpa only [ht] using hab)
  have hs : a.1 = b.1 := by
    simpa using congrArg (euclideanHalfSpaceBoundaryProj n) hb
  exact Prod.ext hs ht

end ConformalPoisson

end RefPart_BoundaryNormalLinear

/- Interface support: BoundaryNormalInverse.lean, SHA256 8d3d0f31f27b2fe736dc828fb53eb2bd7c0eae6b66ed52f03856b6643f306ceb -/
noncomputable section RefPart_BoundaryNormalInverse

/-! The actual boundary normal map is an analytic local diffeomorphism at time
zero. Transversality is proved from the inward unit normal, rather than assumed. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

structure BoundaryNormalMapData (x₀ : boundaryParameterDomain V) where
  map : boundaryParameterDomain V → ℝ → V
  source : Set (boundaryParameterDomain V)
  time : Set ℝ
  source_open : IsOpen source
  base_mem : x₀ ∈ source
  time_open : IsOpen time
  zero_mem : (0 : ℝ) ∈ time
  analytic : ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
    (fun p : boundaryParameterDomain V × ℝ => map p.1 p.2) (x₀, 0)
  geodesic : ∀ x ∈ source, IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (map x) time (boundaryParameter V x) (ambientInwardNormal V (boundaryParameter V x))

set_option backward.isDefEq.respectTransparency false in
theorem BoundaryNormalMapData.differential_injective
    {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) :
    Function.Injective (mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) (x₀, 0)) := by
  let N : EuclideanSpace ℝ (Fin (n + 1)) := ambientInwardNormal V (boundaryParameter V x₀)
  have hN : N 0 ≠ 0 := by
    have hpos := ambientInwardNormal_coordinate_pos V (boundaryParameter V x₀)
    rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1))),
      tangentSpaceOpenEquiv_apply] at hpos
    exact hpos.ne'
  intro v w hvw
  have hv := boundaryNormalMap_mfderiv_zero V R.map R.source_open R.base_mem
    (R.time_open.mem_nhds R.zero_mem) R.analytic R.geodesic v
  have hw := boundaryNormalMap_mfderiv_zero V R.map R.source_open R.base_mem
    (R.time_open.mem_nhds R.zero_mem) R.analytic R.geodesic w
  have heq : boundaryNormalLinear N (show EuclideanSpace ℝ (Fin n) × ℝ from v) =
      boundaryNormalLinear N (show EuclideanSpace ℝ (Fin n) × ℝ from w) := by
    rw [boundaryNormalLinear_apply, boundaryNormalLinear_apply]
    exact hv.symm.trans (hvw.trans hw)
  exact boundaryNormalLinear_injective N hN heq

theorem BoundaryNormalMapData.isLocalDiffeomorphAt
    {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) (x₀, 0) := by
  obtain ⟨S, hS, hreg⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (by decide : (ω : ℕ∞ω) ≠ ∞)).mp R.analytic
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hS
  exact isLocalDiffeomorphAt_of_injective_mfderiv (hreg.mono hOsub) hO hxO
    (BoundarylessManifold.isInteriorPoint (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)))
    (by decide : (1 : ℕ∞ω) ≤ ω) (R.differential_injective V) (by simp)

theorem exists_boundaryNormalMapData
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
    (x₀ : boundaryParameterDomain V) : Nonempty (BoundaryNormalMapData V x₀) := by
  obtain ⟨U, s, Φ, hU, hx₀, hs, h0s, hΦ, hgeo⟩ := exists_analytic_boundary_normal_map V x₀
  exact ⟨⟨Φ, U, s, hU, hx₀, hs, h0s, hΦ, hgeo⟩⟩

end ConformalPoisson

end RefPart_BoundaryNormalInverse

/- Interface support: PartialTimeDerivative.lean, SHA256 f76b43aa03af5593e7743aa7a62bfba4fb57b7abc21ed5a2ab029ffdb60343e4 -/
noncomputable section RefPart_PartialTimeDerivative

/-! Joint continuity and the actual one-variable meaning of the time derivative
of an analytic scalar family on a parameter manifold times real time. -/


open Bundle Filter Set Topology TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J ω P]

def partialTimeDerivative (f : P × ℝ → ℝ) (p : P × ℝ) : ℝ :=
  mvfderiv 𝓘(ℝ) (fun t => f (p.1, t)) p.2 ((NormedSpace.fromTangentSpace p.2).symm 1)

omit [TopologicalSpace P] in
theorem partialTimeDerivative_eq_deriv (f : P × ℝ → ℝ) (p : P × ℝ) :
    partialTimeDerivative f p = deriv (fun t => f (p.1, t)) p.2 := by
  rw [partialTimeDerivative, mvfderiv_eq_fderiv_apply]
  change fderiv ℝ (fun t => f (p.1, t)) p.2 1 = deriv (fun t => f (p.1, t)) p.2
  rfl

omit [IsManifold J ω P] in
theorem hasDerivAt_partialTimeDerivative {f : P × ℝ → ℝ} {p : P × ℝ}
    (hf : MDifferentiableAt (J.prod 𝓘(ℝ)) 𝓘(ℝ) f p) :
    HasDerivAt (fun t => f (p.1, t)) (partialTimeDerivative f p) p.2 := by
  rw [partialTimeDerivative_eq_deriv]
  have hslice : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (fun t => f (p.1, t)) p.2 :=
    hf.comp p.2 (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  exact hslice.differentiableAt.hasDerivAt

theorem continuousAt_partialTimeDerivative {f : P × ℝ → ℝ} {p : P × ℝ}
    (hf : ContMDiffAt (J.prod 𝓘(ℝ)) 𝓘(ℝ) ω f p) :
    ContinuousAt (partialTimeDerivative f) p := by
  obtain ⟨S, hS, hreg⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (by decide : (ω : ℕ∞ω) ≠ ∞)).mp hf
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hS
  have hY : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent 0
      (fun t : ℝ => (⟨t, (NormedSpace.fromTangentSpace t).symm 1⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    change ContDiff ℝ 0 (fun _ : ℝ => (1 : ℝ))
    exact contDiff_const
  have hA : ContMDiffOn (J.prod 𝓘(ℝ)) (𝓘(ℝ)).tangent 0
      (fun q : P × ℝ => (⟨q.2, (NormedSpace.fromTangentSpace q.2).symm 1⟩ :
        TangentBundle 𝓘(ℝ) ℝ)) U := (hY.comp contMDiff_snd).contMDiffOn
  have hpartial := (hreg.mono hUsub).contMDiffOn_mvfderiv_snd_apply hU hA
    (by decide : (0 : ℕ∞ω) + 1 ≤ ω)
  exact (hpartial.continuousOn p hpU).continuousAt (hU.mem_nhds hpU)

end ConformalPoisson

end RefPart_PartialTimeDerivative

/- Interface support: HalfSpaceSign.lean, SHA256 0a19bef2f6da11012ded06d7898e40369ea1bdc1b8d4ba5bcb0145e1f6b37087 -/
noncomputable section RefPart_HalfSpaceSign

/-! Uniform half-space preservation from a positive time derivative and the
actual zero-time boundary identity. This uses one product neighborhood. -/


open Filter Metric Set Topology
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J ω P]

theorem exists_halfSpace_sign_neighborhood
    {f : P × ℝ → ℝ} {x₀ : P}
    (hf : ContMDiffAt (J.prod 𝓘(ℝ)) 𝓘(ℝ) ω f (x₀, 0))
    (hzero : ∀ᶠ x in nhds x₀, f (x, 0) = 0)
    (hpositive : 0 < partialTimeDerivative f (x₀, 0)) :
    ∃ (U : Set P) (ε : ℝ), IsOpen U ∧ x₀ ∈ U ∧ 0 < ε ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-ε) ε,
        (0 ≤ f (x, t) ↔ 0 ≤ t) ∧ (f (x, t) = 0 ↔ t = 0) := by
  have hDnear := (continuousAt_partialTimeDerivative hf).eventually_const_lt hpositive
  have hreg := (contMDiffAt_iff_contMDiffAt_nhds
    (by decide : (ω : ℕ∞ω) ≠ ∞)).mp hf
  have h0near : ∀ᶠ p : P × ℝ in nhds (x₀, 0), f (p.1, 0) = 0 :=
    (continuousAt_fst : ContinuousAt (Prod.fst : P × ℝ → P) (x₀, 0)).eventually hzero
  have hnear := hreg.and (hDnear.and h0near)
  rw [nhds_prod_eq, eventually_prod_iff] at hnear
  obtain ⟨u, hu, T, hT, hprop⟩ := hnear
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hu
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hT
  have htime {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : T t := by
    apply hεsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  refine ⟨U, ε, hU, hxU, hε, ?_⟩
  intro x hx t ht
  have hdata (r : ℝ) (hr : r ∈ Ioo (-ε) ε) := hprop (hUsub hx) (htime hr)
  have hderiv (r : ℝ) (hr : r ∈ Ioo (-ε) ε) :=
    hasDerivAt_partialTimeDerivative ((hdata r hr).1.mdifferentiableAt
      (by decide : (ω : ℕ∞ω) ≠ 0))
  have hmono : StrictMonoOn (fun r => f (x, r)) (Ioo (-ε) ε) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun r hr => (hderiv r hr).continuousAt.continuousWithinAt) (by
        intro r hr
        rw [isOpen_Ioo.interior_eq] at hr
        rw [(hderiv r hr).deriv]
        exact (hdata r hr).2.1)
  have hxzero : f (x, 0) = 0 := (hdata 0 h0).2.2
  exact ⟨by simpa only [hxzero] using hmono.le_iff_le h0 ht,
    by simpa only [hxzero] using hmono.eq_iff_eq ht h0⟩

end ConformalPoisson

end RefPart_HalfSpaceSign

/- Interface support: BoundaryNormalHalfSpace.lean, SHA256 85309f06382ef8db921f94b89c400a7f81da1b2d73414d856a88a18cbc2f6e9f -/
noncomputable section RefPart_BoundaryNormalHalfSpace

/-! The SAME actual analytic normal map preserves the two coordinate half-spaces
and their common boundary on one product neighborhood. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalMapData.halfSpace_sign
    {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) :
    ∃ (U : Set (boundaryParameterDomain V)) (ε : ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ R.source ∧ 0 < ε ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-ε) ε,
        (0 ≤ (R.map x t : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ t) ∧
        ((R.map x t : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ t = 0) := by
  let f : boundaryParameterDomain V × ℝ → ℝ :=
    fun p => ambientBoundaryFunction V (R.map p.1 p.2)
  have hf : ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) 𝓘(ℝ) ω f (x₀, 0) :=
    (contMDiff_ambientBoundaryFunction V).contMDiffAt.comp (x₀, 0) R.analytic
  have hz : ∀ᶠ x in nhds x₀, f (x, 0) = 0 := by
    filter_upwards [R.source_open.mem_nhds R.base_mem] with x hx
    dsimp only [f]
    rw [(R.geodesic x hx).base_eq, ambientBoundaryFunction_boundaryParameter]
  have htime := geodesic_hasDerivAt_ambient_zero (R.geodesic x₀ R.base_mem)
    (R.time_open.mem_nhds R.zero_mem)
  have hcoord : HasDerivAt (fun t => f (x₀, t))
      ((NormedSpace.fromTangentSpace (boundaryParameter V x₀ : EuclideanSpace ℝ (Fin (n + 1)))
        (tangentSpaceOpenEquiv (boundaryParameter V x₀)
          (ambientInwardNormal V (boundaryParameter V x₀)))) 0) 0 := by
    exact (EuclideanSpace.proj (0 : Fin (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 htime
  have hpos : 0 < partialTimeDerivative f (x₀, 0) := by
    rw [partialTimeDerivative_eq_deriv, hcoord.deriv]
    exact ambientInwardNormal_coordinate_pos V (boundaryParameter V x₀)
  obtain ⟨U, ε, hU, hxU, hε, hsign⟩ := exists_halfSpace_sign_neighborhood hf hz hpos
  exact ⟨U ∩ R.source, ε, hU.inter R.source_open, ⟨hxU, R.base_mem⟩,
    inter_subset_right, hε, fun x hx t ht => hsign x hx.1 t ht⟩

end ConformalPoisson

end RefPart_BoundaryNormalHalfSpace

/- Interface support: BoundaryNormalChart.lean, SHA256 7584fc78ed627ad6fce25c7a2f41bbb5b6f5e4b33cc82d285b7c5c6bd55dae3f -/
noncomputable section RefPart_BoundaryNormalChart

/-! Shrink the SAME analytic normal-map inverse together with the actual
geodesic source/time domain and the uniform half-space sign neighborhood. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalMapData.exists_halfSpace_partialDiffeomorph
    {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) :
    ∃ e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (boundaryParameterDomain V × ℝ) V ω,
      (x₀, 0) ∈ e.source ∧
      EqOn (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) e e.source ∧
      e.source ⊆ R.source ×ˢ R.time ∧
      (∀ p ∈ e.source,
        (0 ≤ (e p : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ p.2) ∧
        ((e p : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ p.2 = 0)) ∧
      ∀ y ∈ e.target,
        (0 ≤ (y : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ (e.symm y).2) ∧
        ((y : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ (e.symm y).2 = 0) := by
  have hlocal := R.isLocalDiffeomorphAt V
  let e := hlocal.localInverse.symm
  have he : (x₀, 0) ∈ e.source := hlocal.localInverse_mem_target
  have heq : EqOn (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) e e.source := by
    intro p hp
    have h := hlocal.localInverse_right_inv (y := e p) (e.map_source hp)
    change R.map (e.symm (e p)).1 (e.symm (e p)).2 = e p at h
    exact (congrArg (fun q : boundaryParameterDomain V × ℝ => R.map q.1 q.2)
      (e.left_inv hp)).symm.trans h
  obtain ⟨U, ε, hU, hxU, hUsub, hε, hsign⟩ := R.halfSpace_sign V
  let S : Set (boundaryParameterDomain V × ℝ) := U ×ˢ (Ioo (-ε) ε ∩ R.time)
  have hS : IsOpen S := hU.prod (isOpen_Ioo.inter R.time_open)
  let e' := e.restrOpen S hS
  have hsource : (e'.source : Set (boundaryParameterDomain V × ℝ)) = e.source ∩ S :=
    PartialDiffeomorph.restrOpen_source e hS
  have hbase : (x₀, 0) ∈ e'.source := by
    rw [hsource]
    exact ⟨he, hxU, ⟨neg_neg_of_pos hε, hε⟩, R.zero_mem⟩
  have heq' : EqOn (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2)
      e' e'.source := by
    intro p hp
    have hp' := hsource ▸ hp
    simpa only [e', PartialDiffeomorph.coe_restrOpen] using heq hp'.1
  have hdomain : e'.source ⊆ R.source ×ˢ R.time := by
    intro p hp
    have hp' := hsource ▸ hp
    exact ⟨hUsub hp'.2.1, hp'.2.2.2⟩
  have hforward : ∀ p ∈ e'.source,
      (0 ≤ (e' p : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ p.2) ∧
      ((e' p : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ p.2 = 0) := by
    intro p hp
    have hp' := hsource ▸ hp
    rw [← heq' hp]
    exact hsign p.1 hp'.2.1 p.2 hp'.2.2.1
  refine ⟨e', hbase, heq', hdomain, hforward, ?_⟩
  intro y hy
  have h := hforward (e'.symm y) (e'.map_target hy)
  have hr : e' (e'.symm y) = y := e'.right_inv hy
  exact (congrArg (fun z : V =>
    (0 ≤ (z : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ (e'.symm y).2) ∧
    ((z : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ (e'.symm y).2 = 0)) hr).mp h

end ConformalPoisson

end RefPart_BoundaryNormalChart

/- Interface support: GeodesicUnitSpeed.lean, SHA256 bf37fdea8b65af3ffa9e16d514bfb107738b67a36abf3eeca9e41ce98c8a1cd6 -/
noncomputable section RefPart_GeodesicUnitSpeed

/-! Actual unit speed for a geodesic with a unit initial velocity. -/


open Bundle Set TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

theorem geodesic_unitSpeed_of_unit_initial
    {γ : ℝ → M} {s : Set ℝ} {x : M} {v : TangentSpace I x}
    (h : IsGeodesicCurveOnFrom I γ s x v) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hv : ‖v‖ = 1) {t : ℝ} (ht : t ∈ s) :
    ‖curveVelocity I γ t‖ = 1 := by
  have hbase := h.base_eq
  subst x
  rw [← curveVelocityWithin_of_mem_nhds (I := I) (γ := γ) (hs.mem_nhds ht),
    h.isGeodesicCurveOn.norm_curveVelocityWithin_eq hconn ht h.zero_mem]
  have hvel : curveVelocityWithin I γ s 0 = v := by simpa using h.velocity_eq
  rw [hvel, hv]

end ConformalPoisson

end RefPart_GeodesicUnitSpeed

/- Interface support: BoundaryNormalRectangle.lean, SHA256 196fc4c809797d07a9c456aae591ffd2793307e8b9467128500a1229724f586d -/
noncomputable section RefPart_BoundaryNormalRectangle

/-! One open product domain where the SAME normal map is analytic and all its
curves are unit normal geodesics on the SAME connected time interval. -/


open Bundle Filter Metric Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

structure BoundaryNormalRectangle {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) where
  source : Set (boundaryParameterDomain V)
  source_open : IsOpen source
  base_mem : x₀ ∈ source
  radius : ℝ
  radius_pos : 0 < radius
  source_subset : source ⊆ R.source
  time_subset : Ioo (-radius) radius ⊆ R.time
  analytic : ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
    (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) (source ×ˢ Ioo (-radius) radius)

theorem exists_boundaryNormalRectangle
    {x₀ : boundaryParameterDomain V} (R : BoundaryNormalMapData V x₀) :
    Nonempty (BoundaryNormalRectangle V R) := by
  obtain ⟨S, hS, hreg⟩ := (contMDiffAt_iff_contMDiffOn_nhds
    (by decide : (ω : ℕ∞ω) ≠ ∞)).mp R.analytic
  have hdomain : R.source ×ˢ R.time ∈ nhds (x₀, (0 : ℝ)) :=
    prod_mem_nhds (R.source_open.mem_nhds R.base_mem) (R.time_open.mem_nhds R.zero_mem)
  obtain ⟨U, T, hU, hxU, hT, h0T, hsub⟩ := mem_nhds_prod_iff'.mp (inter_mem hS hdomain)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0T)
  have htime : Ioo (-ε) ε ⊆ T := by
    intro t ht
    apply hεsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht
  refine ⟨⟨U, hU, hxU, ε, hε, ?_, ?_, ?_⟩⟩
  · exact fun x hx => (hsub (show (x, (0 : ℝ)) ∈ U ×ˢ T from ⟨hx, h0T⟩)).2.1
  · exact fun t ht => (hsub (show (x₀, t) ∈ U ×ˢ T from ⟨hxU, htime ht⟩)).2.2
  · exact hreg.mono (fun p hp => (hsub ⟨hp.1, htime hp.2⟩).1)

theorem BoundaryNormalRectangle.geodesic
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source) :
    IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map x)
      (Ioo (-Q.radius) Q.radius) (boundaryParameter V x) (ambientInwardNormal V (boundaryParameter V x)) :=
  (R.geodesic x (Q.source_subset hx)).mono isOpen_Ioo.uniqueDiffOn Q.time_subset
    ⟨neg_neg_of_pos Q.radius_pos, Q.radius_pos⟩

theorem BoundaryNormalRectangle.unitSpeed
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source)
    {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius) :
    ‖curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map x) t‖ = 1 :=
  geodesic_unitSpeed_of_unit_initial (Q.geodesic V hx) isOpen_Ioo isPreconnected_Ioo
    (ambientInwardNormal_unit V _) ht

end ConformalPoisson

end RefPart_BoundaryNormalRectangle

/- Interface support: NormalVariationGauss.lean, SHA256 e530442b64459d48d939b7c49fe7a97f70d96ffe750a0bddeab32fb2d08b0a22 -/
noncomputable section RefPart_NormalVariationGauss

/-! The varying-base Gauss argument: constant unit speed makes the transverse
velocity pairing constant, and an initially normal variation makes it zero. -/


open Bundle CovariantDerivative Filter Set Topology TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

theorem normalVariation_inner_velocity_eq_zero
    (F : ℝ → ℝ → M) {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (h0 : (0 : ℝ) ∈ s)
    (hF : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ => F z.1 z.2) (0, t))
    (hgeo : IsGeodesicCurveOn I (F 0) s)
    (hspeed : ∀ t ∈ s, ∀ᶠ r in nhds (0 : ℝ), ‖curveVelocity I (F r) t‖ ^ 2 = 1)
    (horth : inner ℝ (variationField I F 0) (curveVelocity I (F 0) 0) = 0)
    {t : ℝ} (ht : t ∈ s) :
    inner ℝ (variationField I F t) (curveVelocity I (F 0) t) = 0 := by
  have hderiv (r : ℝ) (hr : r ∈ s) :
      HasDerivAt (fun u => inner ℝ (variationField I F u) (curveVelocity I (F 0) u)) 0 r := by
    have hspeedD := hasDerivAt_norm_sq_curveVelocity (hF r hr)
    have heq : (fun a => ‖curveVelocity I (F a) r‖ ^ 2) =ᶠ[nhds (0 : ℝ)]
        (fun _ => (1 : ℝ)) := hspeed r hr
    have hconst : HasDerivAt (fun a => ‖curveVelocity I (F a) r‖ ^ 2) 0 (0 : ℝ) :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq heq
    have hpair : inner ℝ
        (CovariantDerivative.alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) r)
        (curveVelocity I (F 0) r) = 0 :=
      (mul_eq_zero.mp (hspeedD.unique hconst)).resolve_left two_ne_zero
    have hprod := hasDerivAt_inner_variationField_curveVelocity (hF r hr)
    have hacc := ((isGeodesicCurveOn_iff_of_isOpen hs).mp hgeo).2 r hr
    simpa only [hpair, hacc, inner_zero_right, zero_add] using hprod
  have heq := hs.is_const_of_deriv_eq_zero hconn
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).deriv) ht h0
  exact heq.trans horth

end ConformalPoisson

end RefPart_NormalVariationGauss

/- Interface support: NormalGeodesicVariation.lean, SHA256 6669abf9918f9efeb47aa822b6dae826d96a5047c392b70edfa4d625dd232a96 -/
noncomputable section RefPart_NormalGeodesicVariation

/-! Supply the varying-base Gauss argument from actual normal-geodesic initial
data and an actual coordinate-hyperplane variation. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem normal_geodesic_rebase_initial
    {γ : ℝ → V} {s : Set ℝ} {x : V}
    (h : IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) γ s x
      (ambientInwardNormal V x)) :
    IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) γ s (γ 0)
      (ambientInwardNormal V (γ 0)) := by
  have hx := h.base_eq
  subst x
  exact h

theorem normal_geodesic_variation_inner_eq_zero
    (F : ℝ → ℝ → V) {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (h0 : (0 : ℝ) ∈ s)
    (hF : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 2
      (fun z : ℝ × ℝ => F z.1 z.2) (0, t))
    (hgeo : ∀ᶠ r in nhds (0 : ℝ), IsGeodesicCurveOnFrom 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (F r) s (F r 0) (ambientInwardNormal V (F r 0)))
    (hboundary : ∀ᶠ r in nhds (0 : ℝ), ambientBoundaryFunction V (F r 0) = 0)
    {t : ℝ} (ht : t ∈ s) :
    inner ℝ (variationField 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) F t)
      (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (F 0) t) = 0 := by
  have hgeo0 := hgeo.self_of_nhds
  have hspeed : ∀ u ∈ s, ∀ᶠ r in nhds (0 : ℝ),
      ‖curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (F r) u‖ ^ 2 = 1 := by
    intro u hu
    filter_upwards [hgeo] with r hr
    rw [geodesic_unitSpeed_of_unit_initial hr hs hconn (ambientInwardNormal_unit V _) hu]
    norm_num
  have hvelWithin : curveVelocityWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (F 0) s 0 =
      ambientInwardNormal V (F 0 0) := by simpa using hgeo0.velocity_eq
  have hvel : curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (F 0) 0 =
      ambientInwardNormal V (F 0 0) := by
    rwa [curveVelocityWithin_of_mem_nhds (hs.mem_nhds h0)] at hvelWithin
  have hc : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 2
      (fun r => F r 0) 0 := by
    have hinput : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) 2 (fun r : ℝ => (r, (0 : ℝ))) 0 :=
      (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
    exact (hF 0 h0).comp (f := fun r : ℝ => (r, 0)) 0 hinput
  have hchain := curveVelocityWithin_map (γ := fun r : ℝ => F r 0) (s := univ) (t := 0)
    ((contMDiff_ambientBoundaryFunction V).mdifferentiable
      (by decide : (ω : ℕ∞ω) ≠ 0) (F 0 0))
    (uniqueDiffOn_univ (0 : ℝ) (mem_univ _)) (hc.mdifferentiableAt (by decide)).mdifferentiableWithinAt
  rw [curveVelocityWithin_univ, curveVelocityWithin_univ] at hchain
  have hbeq : (fun r => ambientBoundaryFunction V (F r 0)) =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := hboundary
  have hzeroVel := hbeq.curveVelocity_eq (I := 𝓘(ℝ))
  rw [curveVelocity_const] at hzeroVel
  have hcoord : (NormedSpace.fromTangentSpace (F 0 0 : EuclideanSpace ℝ (Fin (n + 1)))
      (tangentSpaceOpenEquiv (F 0 0)
        (variationField 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) F 0))) 0 = 0 := by
    rw [← mvfderiv_ambientBoundaryFunction, mvfderiv_apply_eq_mfderiv_apply, variationField_apply]
    exact hchain.symm.trans hzeroVel
  have horth : inner ℝ (variationField 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) F 0)
      (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (F 0) 0) = 0 := by
    rw [hvel, real_inner_comm]
    exact ambientInwardNormal_orthogonal V (F 0 0) _ hcoord
  exact normalVariation_inner_velocity_eq_zero F hs hconn h0 hF hgeo0.isGeodesicCurveOn hspeed horth ht

end ConformalPoisson

end RefPart_NormalGeodesicVariation

/- Interface support: BoundaryNormalVariation.lean, SHA256 77ad92da2350fbe63cfbc649d4e57b7bd1b9999b338af0f26fa12e76db48489f -/
noncomputable section RefPart_BoundaryNormalVariation

/-! Apply the varying-base Gauss proof to the SAME actual normal map on its
common analytic rectangle. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalRectangle.variation_inner_velocity_eq_zero
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) (σ : ℝ → boundaryParameterDomain V)
    (hσ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 2 σ 0)
    (hx : σ 0 ∈ Q.source) {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius) :
    inner ℝ
      (variationField 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (fun r u => R.map (σ r) u) t)
      (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map (σ 0)) t) = 0 := by
  have hnear : ∀ᶠ r in nhds (0 : ℝ), σ r ∈ Q.source :=
    hσ.continuousAt.eventually (Q.source_open.mem_nhds hx)
  apply normal_geodesic_variation_inner_eq_zero V (fun r u => R.map (σ r) u)
    isOpen_Ioo isPreconnected_Ioo ⟨neg_neg_of_pos Q.radius_pos, Q.radius_pos⟩ _ _ _ ht
  · intro u hu
    have hmap := ((Q.analytic (σ 0, u) ⟨hx, hu⟩).contMDiffAt
      ((Q.source_open.prod isOpen_Ioo).mem_nhds ⟨hx, hu⟩)).of_le (by decide : (2 : ℕ∞ω) ≤ ω)
    have hinput : ContMDiffAt 𝓘(ℝ, ℝ × ℝ)
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) 2
        (fun p : ℝ × ℝ => (σ p.1, p.2)) (0, u) :=
      (hσ.comp (0, u) (ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiffAt).prodMk
        (ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiffAt
    exact hmap.comp (f := fun p : ℝ × ℝ => (σ p.1, p.2)) (0, u) hinput
  · filter_upwards [hnear] with r hr
    exact normal_geodesic_rebase_initial V (Q.geodesic V hr)
  · filter_upwards [hnear] with r hr
    rw [(Q.geodesic V hr).base_eq, ambientBoundaryFunction_boundaryParameter]

end ConformalPoisson

end RefPart_BoundaryNormalVariation

/- Interface support: BoundaryNormalGauss.lean, SHA256 870dae32c71bad94cf0b525b8662fcef1ab44169c43b650da2f0f5e5c5e8c8dc -/
noncomputable section RefPart_BoundaryNormalGauss

/-! Actual Gauss pairings of the SAME native metric and normal map. Every
spatial tangent vector is tested by an actual native smooth curve. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalRectangle.time_inner_self
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source)
    {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius) :
    inner ℝ (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map x) t)
      (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map x) t) = 1 := by
  rw [real_inner_self_eq_norm_sq, Q.unitSpeed V hx ht]
  norm_num

theorem BoundaryNormalRectangle.spatial_derivative_orthogonal
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source)
    {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (fun y => R.map y t) x v)
      (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map x) t) = 0 := by
  obtain ⟨σ, rfl, hσ, hv⟩ := exists_contMDiffAt_curveVelocity_eq
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := 2) (by decide) x v (0 : ℝ)
  have hmap := (Q.analytic (σ 0, t) ⟨hx, ht⟩).contMDiffAt
    ((Q.source_open.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
  have hslice : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (fun y => R.map y t) (σ 0) :=
    (hmap.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)).comp (σ 0)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hchain := curveVelocityWithin_map (γ := σ) (s := univ) (t := (0 : ℝ)) hslice
    (uniqueDiffOn_univ (0 : ℝ) (mem_univ _))
    (hσ.mdifferentiableAt (by decide : (2 : ℕ∞ω) ≠ 0)).mdifferentiableWithinAt
  rw [curveVelocityWithin_univ, curveVelocityWithin_univ, hv] at hchain
  have hgauss := Q.variation_inner_velocity_eq_zero V σ hσ hx ht
  simp only [variationField_apply] at hgauss
  change inner ℝ
    (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ((fun y => R.map y t) ∘ σ) 0)
    (curveVelocity 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (R.map (σ 0)) t) = 0 at hgauss
  rw [hchain] at hgauss
  exact hgauss

end ConformalPoisson

end RefPart_BoundaryNormalGauss

/- Interface support: ProductSliceDifferential.lean, SHA256 f073c696259aca5fe102f39fb98b8e012119f59be0492a6e6014b3ac45d7a346 -/
noncomputable section RefPart_ProductSliceDifferential

/-! Actual spatial and time columns of a map on a parameter manifold times real time. -/


open Bundle TauCeti.Manifold
open scoped Manifold

namespace ConformalPoisson

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {J : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F K}
  {P N : Type*} [TopologicalSpace P] [TopologicalSpace N]
  [ChartedSpace H P] [ChartedSpace K N]

theorem mfderiv_spatial_column {f : P × ℝ → N} {x : P} {t : ℝ}
    (hf : MDifferentiableAt (J.prod 𝓘(ℝ)) I f (x, t)) (v : TangentSpace J x) :
    mfderiv (J.prod 𝓘(ℝ)) I f (x, t)
        (show TangentSpace (J.prod 𝓘(ℝ)) (x, t) from (v, (0 : ℝ))) =
      mfderiv J I (fun y => f (y, t)) x v := by
  have h := mfderiv_prod_eq_add_apply hf
    (v := (show TangentSpace (J.prod 𝓘(ℝ)) (x, t) from (v, (0 : ℝ))))
  have hz : mfderiv 𝓘(ℝ) I (fun r => f (x, r)) t (0 : ℝ) = 0 :=
    map_zero _
  exact h.trans ((congrArg (fun z : TangentSpace I (f (x, t)) =>
    mfderiv J I (fun y => f (y, t)) x v + z) hz).trans (add_zero _))

theorem mfderiv_time_column {f : P × ℝ → N} {x : P} {t : ℝ}
    (hf : MDifferentiableAt (J.prod 𝓘(ℝ)) I f (x, t)) :
    mfderiv (J.prod 𝓘(ℝ)) I f (x, t)
        (show TangentSpace (J.prod 𝓘(ℝ)) (x, t) from ((0 : E), (1 : ℝ))) =
      curveVelocity I (fun r => f (x, r)) t := by
  have h := mfderiv_prod_eq_add_apply hf
    (v := (show TangentSpace (J.prod 𝓘(ℝ)) (x, t) from ((0 : E), (1 : ℝ))))
  have hz : mfderiv J I (fun y => f (y, t)) x (0 : E) = 0 := map_zero _
  exact h.trans (((congrArg (fun z : TangentSpace I (f (x, t)) =>
    z + mfderiv 𝓘(ℝ) I (fun r => f (x, r)) t (1 : ℝ)) hz).trans
      (zero_add _)).trans (curveVelocity_apply).symm)

end ConformalPoisson

end RefPart_ProductSliceDifferential

/- Interface support: BoundaryNormalMetricForm.lean, SHA256 8e550cf498a163245e0dd9b563dd1bfee787ebab39704e0366410555d2cb8d57 -/
noncomputable section RefPart_BoundaryNormalMetricForm

/-! Gauss normal form for the actual differential of the actual normal map:
the time column has length one and is orthogonal to every spatial column. -/


open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalRectangle.time_column_inner_self
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source)
    {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius) :
    let D := mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) (x, t)
    inner ℝ (D (0, 1)) (D (0, 1)) = 1 := by
  dsimp only
  have hmap := (Q.analytic (x, t) ⟨hx, ht⟩).contMDiffAt
    ((Q.source_open.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
  rw [mfderiv_time_column (hmap.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0))]
  exact Q.time_inner_self V hx ht

theorem BoundaryNormalRectangle.spatial_time_inner
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) {x : boundaryParameterDomain V} (hx : x ∈ Q.source)
    {t : ℝ} (ht : t ∈ Ioo (-Q.radius) Q.radius)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    let D := mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) (x, t)
    inner ℝ (D (v, 0)) (D (0, 1)) = 0 := by
  dsimp only
  have hmap := (Q.analytic (x, t) ⟨hx, ht⟩).contMDiffAt
    ((Q.source_open.prod isOpen_Ioo).mem_nhds ⟨hx, ht⟩)
  have hd := hmap.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)
  rw [mfderiv_spatial_column hd v, mfderiv_time_column hd]
  exact Q.spatial_derivative_orthogonal V hx ht v

end ConformalPoisson

end RefPart_BoundaryNormalMetricForm

/- Interface support: NormalChartRectangle.lean, SHA256 c2060c3a503b0ad7402b800089e054f625a6a0e9c1eabe180ddaff1fbf618d80 -/
noncomputable section RefPart_NormalChartRectangle

/-! One SAME normal chart with source inside the SAME Gauss rectangle. -/

open Bundle Set TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

theorem BoundaryNormalRectangle.exists_halfSpace_chart
    {x₀ : boundaryParameterDomain V} {R : BoundaryNormalMapData V x₀}
    (Q : BoundaryNormalRectangle V R) :
    ∃ e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (boundaryParameterDomain V × ℝ) V ω,
      (x₀, 0) ∈ e.source ∧
      EqOn (fun p : boundaryParameterDomain V × ℝ => R.map p.1 p.2) e e.source ∧
      e.source ⊆ Q.source ×ˢ Ioo (-Q.radius) Q.radius ∧
      (∀ p ∈ e.source,
        (0 ≤ (e p : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ p.2) ∧
        ((e p : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ p.2 = 0)) := by
  obtain ⟨e, hbase, heq, _, hsign, _⟩ := R.exists_halfSpace_partialDiffeomorph V
  let S := Q.source ×ˢ Ioo (-Q.radius) Q.radius
  have hS : IsOpen S := Q.source_open.prod isOpen_Ioo
  let e' := e.restrOpen S hS
  have hsource : (e'.source : Set (boundaryParameterDomain V × ℝ)) = e.source ∩ S :=
    PartialDiffeomorph.restrOpen_source e hS
  refine ⟨e', ?_, ?_, ?_, ?_⟩
  · rw [hsource]
    exact ⟨hbase, Q.base_mem, neg_neg_of_pos Q.radius_pos, Q.radius_pos⟩
  · intro p hp
    have hp' := hsource ▸ hp
    simpa only [e', PartialDiffeomorph.coe_restrOpen] using heq hp'.1
  · intro p hp
    exact (hsource ▸ hp).2
  · intro p hp
    have hp' := hsource ▸ hp
    simpa only [e', PartialDiffeomorph.coe_restrOpen] using hsign p hp'.1
end ConformalPoisson

end RefPart_NormalChartRectangle

/- Interface support: OpenModelCharts.lean, SHA256 5826d791002016e2047f05f8b4b433082a598111ef93bb4e6d1694d5056c9b96 -/
noncomputable section RefPart_OpenModelCharts

/-! Actual coordinate values of the inherited model-space charts used to carry
the normal chart to one full Euclidean ambient chart. -/


open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extChartAt_open_model_apply (U : TopologicalSpace.Opens E) (x y : U) :
    extChartAt 𝓘(ℝ, E) x y = (y : E) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq]

theorem extChartAt_open_model_prod_apply (U : TopologicalSpace.Opens E)
    (x y : U × ℝ) :
    extChartAt ((𝓘(ℝ, E)).prod 𝓘(ℝ)) x y = ((y.1 : E), y.2) := by
  rw [extChartAt_prod_apply]
  apply Prod.ext
  · exact extChartAt_open_model_apply U x.1 y.1
  · rfl

theorem extChartPartial_open_model_apply (U : TopologicalSpace.Opens E) (x y : U) :
    extChartPartialDiffeomorph 𝓘(ℝ, E) ω x y = (y : E) := by
  rw [coe_extChartPartialDiffeomorph]
  exact extChartAt_open_model_apply U x y

theorem extChartPartial_open_model_prod_apply (U : TopologicalSpace.Opens E) (x y : U × ℝ) :
    extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x y = ((y.1 : E), y.2) := by
  rw [coe_extChartPartialDiffeomorph]
  exact extChartAt_open_model_prod_apply U x y

theorem extChartPartial_open_model_prod_symm_snd (U : TopologicalSpace.Opens E)
    (x : U × ℝ) {z : E × ℝ}
    (hz : z ∈ (extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x).target) :
    ((extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x).symm z).2 = z.2 := by
  have h := (extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x).right_inv hz
  have heq :
      ((((extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x).symm z).1 : E),
        ((extChartPartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ)) ω x).symm z).2) = z := by
    simpa only [PartialDiffeomorph.symm_toPartialEquiv, extChartPartial_open_model_prod_apply] using h
  exact congrArg Prod.snd heq

end ConformalPoisson

end RefPart_OpenModelCharts

/- Interface support: AmbientCoordinateDiffeomorph.lean, SHA256 db9c4fb70c72305ac2d281d7155554ae5b6e6a57717f1a30729b50cdc0763ed5 -/
noncomputable section RefPart_AmbientCoordinateDiffeomorph

/-! Carry one actual normal partial diffeomorphism to full Euclidean coordinates,
retaining the actual parameter point and coordinate reading of every image. -/


open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ}

structure AmbientCoordinateDiffeomorph
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
    (e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (U × ℝ) V ω) (x₀ : U) where
  chart : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω
  base_mem : euclideanHalfSpaceBoundaryNormalEquiv n ((x₀ : EuclideanSpace ℝ (Fin n)), 0) ∈ chart.source
  reads : ∀ z ∈ chart.source, ∃ p ∈ e.source,
    (euclideanHalfSpaceBoundaryNormalEquiv n).symm z = ((p.1 : EuclideanSpace ℝ (Fin n)), p.2) ∧
      chart z = (e p : EuclideanSpace ℝ (Fin (n + 1)))

theorem exists_ambientCoordinateDiffeomorph
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
    (e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (U × ℝ) V ω)
    (x₀ : U) (hx₀ : (x₀, 0) ∈ e.source) :
    Nonempty (AmbientCoordinateDiffeomorph U V e x₀) := by
  let p₀ : U × ℝ := (x₀, 0)
  let q₀ := euclideanHalfSpaceBoundaryNormalEquiv n ((x₀ : EuclideanSpace ℝ (Fin n)), 0)
  let cS := extChartPartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) ω p₀
  let cT := extChartPartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω (e p₀)
  let A := ((euclideanHalfSpaceBoundaryNormalEquiv n).symm).toPartialDiffeomorph (n := ω)
  let C := (A.trans cS.symm).trans (e.trans cT)
  have hA (z : EuclideanSpace ℝ (Fin (n + 1))) :
      A z = (euclideanHalfSpaceBoundaryNormalEquiv n).symm z := by
    simp only [A, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
    rfl
  have hAsource (z : EuclideanSpace ℝ (Fin (n + 1))) : z ∈ A.source := by
    simp [A, ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hS₀ : p₀ ∈ cS.source :=
    (mem_extChartPartialDiffeomorph_source _ _ _).mpr BoundarylessManifold.isInteriorPoint
  have hT₀ : e p₀ ∈ cT.source :=
    (mem_extChartPartialDiffeomorph_source _ _ _).mpr BoundarylessManifold.isInteriorPoint
  have hA₀ : A q₀ = cS p₀ := by
    rw [hA]
    dsimp only [q₀]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartPartial_open_model_prod_apply U p₀ p₀).symm
  have hfirst : q₀ ∈ (A.trans cS.symm).source := by
    rw [PartialDiffeomorph.trans_source]
    refine ⟨hAsource q₀, ?_⟩
    change A q₀ ∈ cS.target
    rw [hA₀]
    exact cS.map_source hS₀
  have hfirstVal : (A.trans cS.symm) q₀ = p₀ := by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hA₀]
    exact cS.left_inv hS₀
  have hrest : p₀ ∈ (e.trans cT).source := by
    rw [PartialDiffeomorph.trans_source]
    exact ⟨hx₀, hT₀⟩
  have hbase : q₀ ∈ C.source := by
    rw [PartialDiffeomorph.trans_source]
    refine ⟨hfirst, ?_⟩
    change (A.trans cS.symm) q₀ ∈ (e.trans cT).source
    rw [hfirstVal]
    exact hrest
  refine ⟨⟨C, hbase, ?_⟩⟩
  intro z hz
  have hz' : z ∈ (A.trans cS.symm).source ∧
      (A.trans cS.symm) z ∈ (e.trans cT).source := by
    simpa only [C, PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage] using hz
  have hzs : A z ∈ cS.target := by
    exact hz'.1.2
  let p : U × ℝ := cS.symm (A z)
  have hpRest : p ∈ (e.trans cT).source := by
    simpa only [PartialDiffeomorph.coe_trans, Function.comp_apply, p] using hz'.2
  have hpe : p ∈ e.source := by
    rw [PartialDiffeomorph.trans_source] at hpRest
    exact hpRest.1
  have hcoords : ((p.1 : EuclideanSpace ℝ (Fin n)), p.2) = A z := by
    have h := cS.right_inv hzs
    simpa only [cS, p, PartialDiffeomorph.symm_toPartialEquiv,
      extChartPartial_open_model_prod_apply] using h
  have hvalue : C z = (e p : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa only [C, cT, p, PartialDiffeomorph.coe_trans, Function.comp_apply] using
      extChartPartial_open_model_apply V (e p₀) (e p)
  exact ⟨p, hpe, (hcoords.trans (hA z)).symm, hvalue⟩

section ReadConsequences
variable
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (U × ℝ) V ω} {x₀ : U}
    (C : AmbientCoordinateDiffeomorph U V e x₀)

theorem AmbientCoordinateDiffeomorph.base_value :
    C.chart (euclideanHalfSpaceBoundaryNormalEquiv n ((x₀ : EuclideanSpace ℝ (Fin n)), 0)) =
      (e (x₀, 0) : EuclideanSpace ℝ (Fin (n + 1))) := by
  obtain ⟨p, _, hcoords, hvalue⟩ := C.reads _ C.base_mem
  rw [ContinuousLinearEquiv.symm_apply_apply] at hcoords
  have hp : p = (x₀, 0) := Prod.ext
    (Subtype.ext (congrArg Prod.fst hcoords).symm) (congrArg Prod.snd hcoords).symm
  rw [hp] at hvalue
  exact hvalue

theorem AmbientCoordinateDiffeomorph.image_mem
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.chart.source) :
    C.chart z ∈ V := by
  obtain ⟨p, _, _, hvalue⟩ := C.reads z hz
  rw [hvalue]
  exact (e p).property
end ReadConsequences

end ConformalPoisson

end RefPart_AmbientCoordinateDiffeomorph

/- Interface support: AmbientHalfSpaceSign.lean, SHA256 38a5c89b33b9987f57f0ed23dd709c901668376867189e392ea011504f0175c4 -/
noncomputable section RefPart_AmbientHalfSpaceSign

/-! Side and boundary preservation for the actual Euclidean reading of one
normal partial diffeomorphism. -/


open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

theorem AmbientCoordinateDiffeomorph.halfSpace_sign
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (U × ℝ) V ω} {x₀ : U}
    (C : AmbientCoordinateDiffeomorph U V e x₀)
    (hsign : ∀ p ∈ e.source,
      (0 ≤ (e p : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ p.2) ∧
      ((e p : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ p.2 = 0))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.chart.source) :
    (0 ≤ C.chart z 0 ↔ 0 ≤ z 0) ∧ (C.chart z 0 = 0 ↔ z 0 = 0) := by
  obtain ⟨p, hp, hcoords, hvalue⟩ := C.reads z hz
  have ht : z 0 = p.2 := by
    have h := congrArg Prod.snd hcoords
    simpa only [euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd] using h
  rw [hvalue, ht]
  exact hsign p hp

theorem AmbientCoordinateDiffeomorph.halfSpace_sign_symm
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {e : PartialDiffeomorph ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (U × ℝ) V ω} {x₀ : U}
    (C : AmbientCoordinateDiffeomorph U V e x₀)
    (hsign : ∀ p ∈ e.source,
      (0 ≤ (e p : EuclideanSpace ℝ (Fin (n + 1))) 0 ↔ 0 ≤ p.2) ∧
      ((e p : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ↔ p.2 = 0))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.chart.target) :
    (0 ≤ z 0 ↔ 0 ≤ C.chart.symm z 0) ∧ (z 0 = 0 ↔ C.chart.symm z 0 = 0) := by
  have h := C.halfSpace_sign hsign (C.chart.map_target hz)
  have hr : C.chart (C.chart.symm z) = z := C.chart.right_inv hz
  exact (congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
    (0 ≤ y 0 ↔ 0 ≤ C.chart.symm z 0) ∧ (y 0 = 0 ↔ C.chart.symm z 0 = 0)) hr).mp h

end ConformalPoisson

end RefPart_AmbientHalfSpaceSign

/- Interface support: NormalModelChart.lean, SHA256 9fcc3bf0b721b06357cd16cedee7d9d531c6862290ed23a21bd0c98d1388948b -/
noncomputable section RefPart_NormalModelChart

/-! One ambient analytic normal chart, with every source point read in the
SAME original normal map and SAME Gauss rectangle. -/

open Bundle Set TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]

structure NormalModelChartData {x₀ : boundaryParameterDomain V}
    (D : BoundaryNormalMapData V x₀) (Q : BoundaryNormalRectangle V D) where
  chart : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω
  base_mem : euclideanHalfSpaceBoundaryNormalEquiv n ((x₀ : EuclideanSpace ℝ (Fin n)), 0) ∈ chart.source
  base_value : chart (euclideanHalfSpaceBoundaryNormalEquiv n ((x₀ : EuclideanSpace ℝ (Fin n)), 0)) =
    (boundaryParameter V x₀ : EuclideanSpace ℝ (Fin (n + 1)))
  image_mem : ∀ z ∈ chart.source, chart z ∈ V
  side : ∀ z ∈ chart.source, 0 ≤ chart z 0 ↔ 0 ≤ z 0
  boundary : ∀ z ∈ chart.source, chart z 0 = 0 ↔ z 0 = 0
  reads : ∀ z ∈ chart.source, ∃ p ∈ Q.source ×ˢ Ioo (-Q.radius) Q.radius,
    (euclideanHalfSpaceBoundaryNormalEquiv n).symm z = ((p.1 : EuclideanSpace ℝ (Fin n)), p.2) ∧
      chart z = (D.map p.1 p.2 : EuclideanSpace ℝ (Fin (n + 1)))

theorem exists_normalModelChartData {x₀ : boundaryParameterDomain V}
    (D : BoundaryNormalMapData V x₀) (Q : BoundaryNormalRectangle V D) :
    Nonempty (NormalModelChartData V D Q) := by
  obtain ⟨e, hbase, heq, hsub, hsign⟩ := Q.exists_halfSpace_chart V
  obtain ⟨C⟩ := exists_ambientCoordinateDiffeomorph (boundaryParameterDomain V) V e x₀ hbase
  refine ⟨⟨C.chart, C.base_mem, ?_, (fun _ hz => C.image_mem hz),
    (fun _ hz => (C.halfSpace_sign hsign hz).1),
    (fun _ hz => (C.halfSpace_sign hsign hz).2), ?_⟩⟩
  · exact C.base_value.trans ((congrArg Subtype.val (heq hbase)).symm.trans
      (congrArg Subtype.val (D.geodesic x₀ D.base_mem).base_eq))
  · intro z hz
    obtain ⟨p, hp, hc, hv⟩ := C.reads z hz
    exact ⟨p, hsub hp, hc, hv.trans (congrArg Subtype.val (heq hp)).symm⟩

theorem NormalModelChartData.side_symm {x₀ : boundaryParameterDomain V}
    {D : BoundaryNormalMapData V x₀} {Q : BoundaryNormalRectangle V D}
    (A : NormalModelChartData V D Q) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ A.chart.target) : 0 ≤ A.chart.symm z 0 ↔ 0 ≤ z 0 := by
  have h := A.side (A.chart.symm z) (A.chart.map_target hz)
  have hr : A.chart (A.chart.symm z) = z := A.chart.right_inv hz
  exact ((congrArg (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
    0 ≤ y 0 ↔ 0 ≤ A.chart.symm z 0)) hr).mp h |>.symm

theorem NormalModelChartData.boundary_identity {x₀ : boundaryParameterDomain V}
    {D : BoundaryNormalMapData V x₀} {Q : BoundaryNormalRectangle V D}
    (A : NormalModelChartData V D Q) {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ A.chart.source) (hzero : z 0 = 0) : A.chart z = z := by
  obtain ⟨p, hp, hc, hv⟩ := A.reads z hz
  have ht : p.2 = 0 := by
    have h := congrArg Prod.snd hc
    simpa only [euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd, hzero] using h.symm
  have hc' : z = euclideanHalfSpaceBoundaryNormalEquiv n ((p.1 : EuclideanSpace ℝ (Fin n)), 0) := by
    rw [ht] at hc
    exact ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply z).symm.trans
      (congrArg (euclideanHalfSpaceBoundaryNormalEquiv n) hc)
  rw [ht] at hv
  have hb := congrArg Subtype.val (Q.geodesic V hp.1).base_eq
  exact hv.trans (hb.trans (by
    rw [hc', euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
    rfl))

end ConformalPoisson

end RefPart_NormalModelChart

/- Interface support: HalfSpaceDiffeomorph.lean, SHA256 58d4ad633bbf3dea728809b54a2edb8491edf4deb173fc045d2950eb586a55c8 -/
noncomputable section RefPart_HalfSpaceDiffeomorph

/-! Restrict an actual ambient analytic partial diffeomorphism to the model
half-space using its proved side preservation. Analyticity is native up to the boundary. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

def halfSpaceOpenPartialHomeomorph
    (e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ e.source, 0 ≤ e z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ e.target, 0 ≤ e.symm z 0 ↔ 0 ≤ z 0) :
    OpenPartialHomeomorph (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) := by
  have hf (z : EuclideanHalfSpace (n + 1)) (hz : z.1 ∈ e.source) :
      (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e z.1)) = e z.1 :=
    (𝓡∂ (n + 1)).right_inv (by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (hforward z.1 hz).mpr z.property)
  have hb (z : EuclideanHalfSpace (n + 1)) (hz : z.1 ∈ e.target) :
      (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e.symm z.1)) = e.symm z.1 :=
    (𝓡∂ (n + 1)).right_inv (by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (hbackward z.1 hz).mpr z.property)
  refine
    { toFun := fun z => (𝓡∂ (n + 1)).symm (e z.1)
      invFun := fun z => (𝓡∂ (n + 1)).symm (e.symm z.1)
      source := {z | z.1 ∈ e.source}
      target := {z | z.1 ∈ e.target}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := e.open_source.preimage (𝓡∂ (n + 1)).continuous
      open_target := e.open_target.preimage (𝓡∂ (n + 1)).continuous
      continuousOn_toFun := (𝓡∂ (n + 1)).continuous_symm.continuousOn.comp
        (e.contMDiffOn_toFun.continuousOn.comp (𝓡∂ (n + 1)).continuous.continuousOn
          (fun _ hz => hz)) (fun _ _ => mem_univ _)
      continuousOn_invFun := (𝓡∂ (n + 1)).continuous_symm.continuousOn.comp
        (e.contMDiffOn_invFun.continuousOn.comp (𝓡∂ (n + 1)).continuous.continuousOn
          (fun _ hz => hz)) (fun _ _ => mem_univ _) }
  · intro z hz
    change (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e z.1)) ∈ e.target
    rw [hf z hz]
    exact e.map_source hz
  · intro z hz
    change (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e.symm z.1)) ∈ e.source
    rw [hb z hz]
    exact e.map_target hz
  · intro z hz
    change (𝓡∂ (n + 1)).symm (e.symm ((𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e z.1)))) = z
    rw [hf z hz]
    exact (congrArg (𝓡∂ (n + 1)).symm
      (show e.symm (e z.1) = z.1 from e.left_inv hz)).trans ((𝓡∂ (n + 1)).left_inv z)
  · intro z hz
    change (𝓡∂ (n + 1)).symm (e ((𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).symm (e.symm z.1)))) = z
    rw [hb z hz]
    exact (congrArg (𝓡∂ (n + 1)).symm
      (show e (e.symm z.1) = z.1 from e.right_inv hz)).trans ((𝓡∂ (n + 1)).left_inv z)

def halfSpacePartialDiffeomorph
    (e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ e.source, 0 ≤ e z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ e.target, 0 ≤ e.symm z 0 ↔ 0 ≤ z 0) :
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) ω where
  toPartialEquiv := (halfSpaceOpenPartialHomeomorph e hforward hbackward).toPartialEquiv
  open_source := (halfSpaceOpenPartialHomeomorph e hforward hbackward).open_source
  open_target := (halfSpaceOpenPartialHomeomorph e hforward hbackward).open_target
  contMDiffOn_toFun := by
    let S : Set (EuclideanHalfSpace (n + 1)) := (𝓡∂ (n + 1)) ⁻¹' e.source
    have he : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
        (fun z : EuclideanHalfSpace (n + 1) => e ((𝓡∂ (n + 1)) z)) S :=
      e.contMDiffOn_toFun.comp (𝓡∂ (n + 1)).contMDiff.contMDiffOn (fun _ hz => hz)
    have hr := (𝓡∂ (n + 1)).contMDiffOn_symm.comp he (fun z hz => by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (hforward z.1 hz).mpr z.property)
    exact hr
  contMDiffOn_invFun := by
    let S : Set (EuclideanHalfSpace (n + 1)) := (𝓡∂ (n + 1)) ⁻¹' e.target
    have he : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
        (fun z : EuclideanHalfSpace (n + 1) => e.symm ((𝓡∂ (n + 1)) z)) S :=
      e.contMDiffOn_invFun.comp (𝓡∂ (n + 1)).contMDiff.contMDiffOn (fun _ hz => hz)
    have hr := (𝓡∂ (n + 1)).contMDiffOn_symm.comp he (fun z hz => by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact (hbackward z.1 hz).mpr z.property)
    exact hr

section Computations
variable
    (e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ e.source, 0 ≤ e z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ e.target, 0 ≤ e.symm z 0 ↔ 0 ≤ z 0)

theorem halfSpacePartialDiffeomorph_source :
    (halfSpacePartialDiffeomorph e hforward hbackward).source =
      {z : EuclideanHalfSpace (n + 1) | z.1 ∈ e.source} := rfl

theorem halfSpacePartialDiffeomorph_target :
    (halfSpacePartialDiffeomorph e hforward hbackward).target =
      {z : EuclideanHalfSpace (n + 1) | z.1 ∈ e.target} := rfl

theorem halfSpacePartialDiffeomorph_apply (z : EuclideanHalfSpace (n + 1)) :
    halfSpacePartialDiffeomorph e hforward hbackward z = (𝓡∂ (n + 1)).symm (e z.1) := rfl

theorem halfSpacePartialDiffeomorph_symm_apply (z : EuclideanHalfSpace (n + 1)) :
    (halfSpacePartialDiffeomorph e hforward hbackward).symm z =
      (𝓡∂ (n + 1)).symm (e.symm z.1) := rfl

theorem halfSpacePartialDiffeomorph_coe_apply {z : EuclideanHalfSpace (n + 1)}
    (hz : z.1 ∈ e.source) :
    (halfSpacePartialDiffeomorph e hforward hbackward z).1 = e z.1 := by
  rw [halfSpacePartialDiffeomorph_apply]
  exact (𝓡∂ (n + 1)).right_inv (by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact (hforward z.1 hz).mpr z.property)
end Computations

end ConformalPoisson

end RefPart_HalfSpaceDiffeomorph

/- Interface support: NativeChartPartialDiffeomorph.lean, SHA256 ba6338e4331a9abd267ac72eb70caf301baf00fbb27b65ef07f68479c1c58b59 -/
noncomputable section RefPart_NativeChartPartialDiffeomorph

/-! The actual boundary chart is an analytic partial diffeomorphism to the
half-space model, including its boundary, without restricting to the interior. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def nativeChartPartialDiffeomorph (α : M) :
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M (EuclideanHalfSpace (n + 1)) ω where
  toPartialEquiv := (chartAt (EuclideanHalfSpace (n + 1)) α).toPartialEquiv
  open_source := (chartAt (EuclideanHalfSpace (n + 1)) α).open_source
  open_target := (chartAt (EuclideanHalfSpace (n + 1)) α).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

theorem nativeChartPartialDiffeomorph_source (α : M) :
    (nativeChartPartialDiffeomorph (n := n) α).source = (chartAt (EuclideanHalfSpace (n + 1)) α).source := rfl

theorem nativeChartPartialDiffeomorph_target (α : M) :
    (nativeChartPartialDiffeomorph (n := n) α).target = (chartAt (EuclideanHalfSpace (n + 1)) α).target := rfl

theorem nativeChartPartialDiffeomorph_apply (α x : M) :
    nativeChartPartialDiffeomorph (n := n) α x = chartAt (EuclideanHalfSpace (n + 1)) α x := rfl

theorem nativeChartPartialDiffeomorph_symm_apply (α : M) (z : EuclideanHalfSpace (n + 1)) :
    (nativeChartPartialDiffeomorph (n := n) α).symm z = (chartAt (EuclideanHalfSpace (n + 1)) α).symm z := rfl
end ConformalPoisson

end RefPart_NativeChartPartialDiffeomorph

/- Interface support: AmbientToNativeChart.lean, SHA256 d7e64b703c98caba5e69f1953dc0267e9ea4c20bf2fdd96c2c16e50dad89a54c -/
noncomputable section RefPart_AmbientToNativeChart

/-! Compose the actual half-space restriction with the actual inverse original
boundary chart. Both directions are analytic, including at the boundary. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

variable
    (α : M)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)

def nativeHalfSpaceChart :
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) M ω :=
  (halfSpacePartialDiffeomorph C hforward hbackward).trans
    (nativeChartPartialDiffeomorph (n := n) α).symm

theorem nativeHalfSpaceChart_apply (z : EuclideanHalfSpace (n + 1)) :
    nativeHalfSpaceChart α C hforward hbackward z =
      (extChartAt (𝓡∂ (n + 1)) α).symm (C z.1) := by
  rw [nativeHalfSpaceChart, PartialDiffeomorph.coe_trans, Function.comp_apply,
    halfSpacePartialDiffeomorph_apply, nativeChartPartialDiffeomorph_symm_apply,
    extChartAt_coe_symm, Function.comp_apply]

theorem nativeHalfSpaceChart_source
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target) :
    (nativeHalfSpaceChart α C hforward hbackward).source =
      {z : EuclideanHalfSpace (n + 1) | z.1 ∈ C.source} := by
  rw [nativeHalfSpaceChart, PartialDiffeomorph.trans_source,
    halfSpacePartialDiffeomorph_source]
  apply Set.ext
  intro z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    change halfSpacePartialDiffeomorph C hforward hbackward z ∈
      (nativeChartPartialDiffeomorph (n := n) α).target
    rw [halfSpacePartialDiffeomorph_apply, nativeChartPartialDiffeomorph_target]
    have h := htarget z.1 hz z.property
    rw [extChartAt_target] at h
    exact h.1

end ConformalPoisson

end RefPart_AmbientToNativeChart

/- Interface support: NativeNormalInverse.lean, SHA256 568f2f4b8f0e5ac67f16834940f0ffd43205e0a76bc30be7f1070a568d5e1ad6 -/
noncomputable section RefPart_NativeNormalInverse

/-! Instantiate every normal-geodesic and inverse theorem with the SAME analytic
ambient metric extending the original native boundary tensor. -/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem NativeMetricAmbientExtension.exists_boundaryNormalMapData
    {g : Metric (n := n) (M := M)} {α : M} (R : NativeMetricAmbientExtension g α)
    (x₀ : boundaryParameterDomain R.domain) :
    let : RiemannianBundle (fun x : R.domain =>
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
    let : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
    Nonempty (BoundaryNormalMapData R.domain x₀) := by
  let : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
      IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
  exact ConformalPoisson.exists_boundaryNormalMapData R.domain x₀

end ConformalPoisson

end RefPart_NativeNormalInverse

/- Interface support: NativeBoundaryNormalBase.lean, SHA256 fe283e84c3701efd28ab58b6b28576f91cf0a0ffb2b6e1e9704bf263aa63da7e -/
noncomputable section RefPart_NativeBoundaryNormalBase

/-! The selected original boundary point belongs to the actual hyperplane
parameter domain of its analytic ambient extension. -/


open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def NativeMetricAmbientExtension.boundaryBase
    {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
    (R : NativeMetricAmbientExtension g (α : M)) : boundaryParameterDomain R.domain :=
  ⟨extChartAt (𝓡 n) α α, by
    change euclideanHalfSpaceBoundaryParam n (extChartAt (𝓡 n) α α) ∈ R.domain
    rw [boundaryParam_extChartAt (mem_extChartAt_source α)]
    exact R.base_mem⟩

theorem NativeMetricAmbientExtension.boundaryParameter_boundaryBase
    {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
    (R : NativeMetricAmbientExtension g (α : M)) :
    (boundaryParameter R.domain R.boundaryBase : EuclideanSpace ℝ (Fin (n + 1))) =
      extChartAt (𝓡∂ (n + 1)) (α : M) (α : M) := by
  exact boundaryParam_extChartAt (mem_extChartAt_source α)

end ConformalPoisson

end RefPart_NativeBoundaryNormalBase

/- Interface support: NativeAmbientDomain.lean, SHA256 3f18d572400bd723ac77886cdb486711abef8292487e7dbc0514cd62ae8f1a4d -/
noncomputable section RefPart_NativeAmbientDomain

/-! Shrink the full ambient metric domain so that its half-space part lies in
the actual original extended chart target. -/


open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem NativeMetricAmbientExtension.exists_domain_in_chart
    {g : Metric (n := n) (M := M)} {α : M} (R : NativeMetricAmbientExtension g α) :
    ∃ R' : NativeMetricAmbientExtension g α,
      R'.tensor = R.tensor ∧ R'.domain ≤ R.domain ∧
      ∀ z ∈ R'.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) α).target := by
  obtain ⟨O, hO, hαO, hOsub⟩ := mem_nhdsWithin.mp
    (extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (n + 1)) α)
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
    R.domain ⊓ ⟨O, hO⟩
  let R' : NativeMetricAmbientExtension g α :=
    { domain := V
      base_mem := ⟨R.base_mem, hαO⟩
      tensor := R.tensor
      analytic := R.analytic.mono (by intro z hz; exact hz.1)
      symmetric := R.symmetric
      positive := fun z hz => R.positive z hz.1
      agrees := R.agrees }
  refine ⟨R', rfl, (by intro z hz; exact hz.1), ?_⟩
  intro z hz hnonneg
  apply hOsub
  refine ⟨hz.2, ?_⟩
  simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hnonneg

end ConformalPoisson

end RefPart_NativeAmbientDomain

/- Interface support: NativeNormalGauss.lean, SHA256 3e3d6bd93469b48ee46185613b3ece5a74f600f7d92bd454b80d4ec9f697db6b -/
noncomputable section RefPart_NativeNormalGauss

/-! The original native boundary point, SAME extended native metric, SAME normal
map and actual common analytic/unit-Gauss rectangle are produced together. -/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem NativeMetricAmbientExtension.exists_normalRectangle
    {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
    (R : NativeMetricAmbientExtension g (α : M)) :
    let : RiemannianBundle (fun x : R.domain =>
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
    let : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
    Nonempty (Σ D : BoundaryNormalMapData R.domain R.boundaryBase, BoundaryNormalRectangle R.domain D) := by
  let : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
      IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
  obtain ⟨D⟩ := R.exists_boundaryNormalMapData R.boundaryBase
  obtain ⟨Q⟩ := exists_boundaryNormalRectangle R.domain D
  exact ⟨⟨D, Q⟩⟩

end ConformalPoisson

end RefPart_NativeNormalGauss

/- Interface support: NativeNormalChart.lean, SHA256 53492c3db4bacbe7ad31f2303c7df7e85393b8efc52dad4d9f6ca56dde53f7d8 -/
noncomputable section RefPart_NativeNormalChart

/-! The SAME ambient normal chart composed into the original manifold. The
actual base point and original boundary parameter labels are retained. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
  (R : NativeMetricAmbientExtension g (α : M))

local instance : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
local instance : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)

variable {D : BoundaryNormalMapData R.domain R.boundaryBase}
  {Q : BoundaryNormalRectangle R.domain D} (A : NormalModelChartData R.domain D Q)

def NativeMetricAmbientExtension.normalChart :
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω :=
  nativeHalfSpaceChart (α : M) A.chart A.side (fun _ hz => A.side_symm R.domain hz)

theorem NativeMetricAmbientExtension.normalChart_source
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target) :
    (R.normalChart A).source = {z : EuclideanHalfSpace (n + 1) | z.1 ∈ A.chart.source} := by
  apply nativeHalfSpaceChart_source
  intro z hz hpos
  exact hcompat (A.chart z) (A.image_mem z hz) ((A.side z hz).mpr hpos)

theorem NativeMetricAmbientExtension.normalChart_apply (z : EuclideanHalfSpace (n + 1)) :
    R.normalChart A z = (extChartAt (𝓡∂ (n + 1)) (α : M)).symm (A.chart z.1) :=
  nativeHalfSpaceChart_apply _ _ _ _ z

theorem NativeMetricAmbientExtension.normal_base_coordinate :
    euclideanHalfSpaceBoundaryNormalEquiv n ((R.boundaryBase : EuclideanSpace ℝ (Fin n)), 0) =
      extChartAt (𝓡∂ (n + 1)) (α : M) (α : M) := by
  rw [euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
  exact R.boundaryParameter_boundaryBase

theorem NativeMetricAmbientExtension.normalChart_base_mem
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target) :
    chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M) ∈ (R.normalChart A).source := by
  rw [R.normalChart_source A hcompat]
  change extChartAt (𝓡∂ (n + 1)) (α : M) (α : M) ∈ A.chart.source
  rw [← R.normal_base_coordinate]
  exact A.base_mem

theorem NativeMetricAmbientExtension.normalChart_base_value :
    R.normalChart A (chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M)) = (α : M) := by
  rw [R.normalChart_apply]
  change (extChartAt (𝓡∂ (n + 1)) (α : M)).symm
    (A.chart (extChartAt (𝓡∂ (n + 1)) (α : M) (α : M))) = (α : M)
  rw [← R.normal_base_coordinate, A.base_value, R.boundaryParameter_boundaryBase]
  exact extChartAt_to_inv (α : M)

theorem NativeMetricAmbientExtension.normalChart_boundary_value
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) (hzero : z.1 0 = 0) :
    R.normalChart A z = (extChartAt (𝓡∂ (n + 1)) (α : M)).symm z.1 := by
  rw [R.normalChart_apply, A.boundary_identity R.domain hz hzero]
end ConformalPoisson

end RefPart_NativeNormalChart

/- Interface support: NormalParameterRead.lean, SHA256 c01987002f7fecc53b65f8de0a1fc978b0907bd7edfd522e9ab0a75dabb5b6c7 -/
noncomputable section RefPart_NormalParameterRead

/-! The actual coordinate inclusion of an open spatial parameter times time,
with its analytic regularity and native differential. -/

open Filter Set Topology TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

def normalParameterRead (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (p : U × ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  euclideanHalfSpaceBoundaryNormalEquiv n ((p.1 : EuclideanSpace ℝ (Fin n)), p.2)

theorem normalParameterRead_chart (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (p q : U × ℝ) :
    normalParameterRead U q = euclideanHalfSpaceBoundaryNormalEquiv n
      (extChartAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p q) := by
  rw [extChartAt_open_model_prod_apply]
  rfl

theorem contMDiffAt_normalParameterRead (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (p : U × ℝ) :
    ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω (normalParameterRead U) p := by
  have h : ContMDiffAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω
      (euclideanHalfSpaceBoundaryNormalEquiv n ∘
        extChartAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) p :=
    (euclideanHalfSpaceBoundaryNormalEquiv n).toContinuousLinearMap.contMDiffAt.comp p
      (contMDiffAt_extChartAt (x := p))
  exact h.congr_of_eventuallyEq (Eventually.of_forall (normalParameterRead_chart U p))

theorem mvfderiv_normalParameterRead_apply (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (p : U × ℝ)
    (v : TangentSpace ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) :
    mvfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) (normalParameterRead U) p v =
      euclideanHalfSpaceBoundaryNormalEquiv n v := by
  have heq : normalParameterRead U =ᶠ[nhds p]
      (euclideanHalfSpaceBoundaryNormalEquiv n ∘
        extChartAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) :=
    Eventually.of_forall (normalParameterRead_chart U p)
  have hc := (euclideanHalfSpaceBoundaryNormalEquiv n).toContinuousLinearMap.mvfderiv_comp_apply
    ((contMDiffAt_extChartAt (I := ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)))
      (n := ω) (x := p)).mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)) v
  have hd : mvfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
      (extChartAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) p v = v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_extChartAt_self]
    rfl
  exact (congrArg (fun L => L v) heq.mvfderiv_eq).trans
    (hc.trans (congrArg (euclideanHalfSpaceBoundaryNormalEquiv n) hd))
end ConformalPoisson

end RefPart_NormalParameterRead

/- Interface support: NormalModelDifferential.lean, SHA256 7bdb0c02e27bc86e52c6d7d8627a99518d5183b08b1ca84fa0af639b321a5d42 -/
noncomputable section RefPart_NormalModelDifferential

/-! The full Euclidean normal chart has the derivative of the SAME normal map
on its SAME Gauss rectangle, in the actual boundary/time splitting. -/

open Bundle Filter Set Topology TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}
  (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (n + 1))))
  [RiemannianBundle (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : V => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x)]
variable {x₀ : boundaryParameterDomain V} {D : BoundaryNormalMapData V x₀}
  {Q : BoundaryNormalRectangle V D} (A : NormalModelChartData V D Q)

theorem NormalModelChartData.read_parameter {p : boundaryParameterDomain V × ℝ}
    (hp : normalParameterRead (boundaryParameterDomain V) p ∈ A.chart.source) :
    p ∈ Q.source ×ˢ Ioo (-Q.radius) Q.radius ∧
      A.chart (normalParameterRead (boundaryParameterDomain V) p) =
        (D.map p.1 p.2 : EuclideanSpace ℝ (Fin (n + 1))) := by
  obtain ⟨q, hq, hc, hv⟩ := A.reads _ hp
  rw [normalParameterRead, ContinuousLinearEquiv.symm_apply_apply] at hc
  have hqp : q = p := Prod.ext (Subtype.ext (congrArg Prod.fst hc).symm)
    (congrArg Prod.snd hc).symm
  rw [hqp] at hq hv
  exact ⟨hq, hv⟩

theorem NormalModelChartData.ambient_derivative {p : boundaryParameterDomain V × ℝ}
    (hp : normalParameterRead (boundaryParameterDomain V) p ∈ A.chart.source)
    (v : TangentSpace ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) :
    fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain V) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n v) =
      mvfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
        (fun q : boundaryParameterDomain V × ℝ =>
          (D.map q.1 q.2 : EuclideanSpace ℝ (Fin (n + 1)))) p v := by
  have hK := contMDiffAt_normalParameterRead (boundaryParameterDomain V) p
  have heq : (A.chart ∘ normalParameterRead (boundaryParameterDomain V)) =ᶠ[nhds p]
      (fun q : boundaryParameterDomain V × ℝ =>
        (D.map q.1 q.2 : EuclideanSpace ℝ (Fin (n + 1)))) := by
    filter_upwards [hK.continuousAt.eventually (A.chart.open_source.mem_nhds hp)] with q hq
    exact (A.read_parameter V hq).2
  have hC : DifferentiableAt ℝ A.chart (normalParameterRead (boundaryParameterDomain V) p) :=
    ((A.chart.contMDiffOn_toFun _ hp).contMDiffAt
      (A.chart.open_source.mem_nhds hp)).contDiffAt.differentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)
  have hchain := TauCeti.mvfderiv_comp_apply_of_differentiableAt hC
    (hK.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)) v
  rw [mvfderiv_normalParameterRead_apply] at hchain
  exact hchain.symm.trans (congrArg (fun L => L v) heq.mvfderiv_eq)

theorem NormalModelChartData.ambient_differential {p : boundaryParameterDomain V × ℝ}
    (hp : normalParameterRead (boundaryParameterDomain V) p ∈ A.chart.source)
    (v : TangentSpace ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ)) p) :
    fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain V) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n v) =
      (show EuclideanSpace ℝ (Fin (n + 1)) from
        mfderiv ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (fun q : boundaryParameterDomain V × ℝ => D.map q.1 q.2) p v) := by
  have hpQ := (A.read_parameter V hp).1
  have hD := (Q.analytic p hpQ).contMDiffAt
    ((Q.source_open.prod isOpen_Ioo).mem_nhds hpQ)
  have hval := (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (n := ω)).mdifferentiable (by decide : (ω : ℕ∞ω) ≠ 0) (D.map p.1 p.2)
  have hchain := mvfderiv_comp_apply p hval
    (hD.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0)) v
  rw [mvfderiv_subtype_val_apply] at hchain
  exact (A.ambient_derivative V hp v).trans hchain
end ConformalPoisson

end RefPart_NormalModelDifferential

/- Interface support: NativeNormalModelMetric.lean, SHA256 5d832813fd72dbb21c67792af33bb27fdab9d6db77176ecd745519069bfd967d -/
noncomputable section RefPart_NativeNormalModelMetric

/-! Gauss form for the actual ambient chart's ordinary differential, evaluated
in the SAME native metric's actual tensor. -/

open Bundle Set TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : M}
  (R : NativeMetricAmbientExtension g α)
local instance : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
local instance : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)

theorem NativeMetricAmbientExtension.model_inner (z : R.domain)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) z) :
    R.metric.inner z v w = R.tensor (z : EuclideanSpace ℝ (Fin (n + 1)))
      (show EuclideanSpace ℝ (Fin (n + 1)) from v) (show EuclideanSpace ℝ (Fin (n + 1)) from w) := by
  rw [NativeMetricAmbientExtension.metric, analyticAmbientMetric_inner]
  rw [NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1))),
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1))),
    tangentSpaceOpenEquiv_apply, tangentSpaceOpenEquiv_apply]

variable {x₀ : boundaryParameterDomain R.domain} {D : BoundaryNormalMapData R.domain x₀}
  {Q : BoundaryNormalRectangle R.domain D} (A : NormalModelChartData R.domain D Q)

theorem NativeMetricAmbientExtension.normalModel_time_inner
    {p : boundaryParameterDomain R.domain × ℝ}
    (hp : normalParameterRead (boundaryParameterDomain R.domain) p ∈ A.chart.source) :
    R.tensor (A.chart (normalParameterRead (boundaryParameterDomain R.domain) p))
      (fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain R.domain) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
      (fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain R.domain) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 1 := by
  have hpQ := (A.read_parameter R.domain hp).1
  have hg := Q.time_column_inner_self R.domain hpQ.1 hpQ.2
  change R.metric.inner (D.map p.1 p.2) _ _ = 1 at hg
  rw [R.model_inner] at hg
  rw [A.ambient_differential R.domain hp (0, 1), (A.read_parameter R.domain hp).2]
  exact hg

theorem NativeMetricAmbientExtension.normalModel_spatial_time_inner
    {p : boundaryParameterDomain R.domain × ℝ}
    (hp : normalParameterRead (boundaryParameterDomain R.domain) p ∈ A.chart.source)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p.1) :
    R.tensor (A.chart (normalParameterRead (boundaryParameterDomain R.domain) p))
      (fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain R.domain) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)))
      (fderiv ℝ A.chart (normalParameterRead (boundaryParameterDomain R.domain) p)
        (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 0 := by
  have hpQ := (A.read_parameter R.domain hp).1
  have hg := Q.spatial_time_inner R.domain hpQ.1 hpQ.2 v
  change R.metric.inner (D.map p.1 p.2) _ _ = 0 at hg
  rw [R.model_inner] at hg
  rw [A.ambient_differential R.domain hp (v, 0), A.ambient_differential R.domain hp (0, 1),
    (A.read_parameter R.domain hp).2]
  exact hg
end ConformalPoisson

end RefPart_NativeNormalModelMetric

/- Interface support: InteriorChartDerivative.lean, SHA256 aa4d14a53fa8e7258272b0918c03b08260669dc6601ad79bce69d4fffee350a7 -/
noncomputable section RefPart_InteriorChartDerivative

/-!
Differentiation in an ordinary chart at an interior point. Unlike the boundaryless
chart-frame lemma, these statements only require the point under consideration to
lie in the interior of the extended chart target.

The proof follows the chain-rule argument of Tau Ceti's
`Riemannian.Tensor.mvfderiv_chartLocalFrame`, with an arbitrary model vector and
the local interior hypothesis in place of a boundaryless ambient model.
-/


open Bundle Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem mdifferentiableAt_inverseChart_of_interior {α : M} {z : E}
    (hz : z ∈ interior (extChartAt I α).target) :
    MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm z := by
  exact (mdifferentiableWithinAt_extChartAt_symm (interior_subset hz)).mdifferentiableAt
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hz)
      (interior_subset.trans (extChartAt_target_subset_range α)))

/-- A chart-constant tangent field differentiates by the ordinary coordinate derivative. -/
theorem mvfderiv_inverseChart_vector (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source)
    (hint : extChartAt I α y ∈ interior (extChartAt I α).target)
    {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ) f y) (v : E) :
    mvfderiv I f y ((trivializationAt E (TangentSpace I) α).symmL ℝ y v) =
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α y) v := by
  have hsymm := mdifferentiableAt_inverseChart_of_interior hint
  have hy' : (extChartAt I α).symm (extChartAt I α y) = y :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  have h := mvfderiv_comp_apply_of_eq (g := f) (extChartAt I α y) hf hsymm hy' v
  rw [mvfderiv_eq_fderiv] at h
  have hrange : range I ∈ 𝓝 (extChartAt I α y) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hint)
      (interior_subset.trans (extChartAt_target_subset_range α))
  rw [TangentBundle.symmL_trivializationAt hy, mfderivWithin_of_mem_nhds hrange]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the chart sends its chart-constant tangent vector back to the model vector.
This round-trip identity holds at boundary points as well. -/
theorem mfderiv_chart_inverseVector (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source) (v : E) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) y
      ((trivializationAt E (TangentSpace I) α).symmL ℝ y v) = v := by
  have hsource : y ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hz := (extChartAt I α).map_source hsource
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
  rw [(extChartAt I α).left_inv hsource] at h
  rw [TangentBundle.symmL_trivializationAt hy]
  exact congrArg (fun L => L v) h

section Hessian

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [RiemannianBundle (fun y : M => TangentSpace I y)]
  [IsContMDiffRiemannianBundle I 1 E (fun y : M => TangentSpace I y)]

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun y : M => TangentSpace I y)]
  [IsContMDiffRiemannianBundle I 1 E (fun y : M => TangentSpace I y)] in
/-- A constant vector in chart coordinates defines a differentiable tangent field throughout
the chart source, without a boundaryless assumption. -/
theorem mdifferentiableAt_chartConstantVector (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source) (w : E) :
    MDifferentiableAt I I.tangent
      (fun z => (⟨z, (trivializationAt E (TangentSpace I) α).symmL ℝ z w⟩ :
        TangentBundle I M)) y := by
  let : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  let : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hframe : ContMDiffAt I I.tangent 1
      (fun z => (⟨z, (trivializationAt E (TangentSpace I) α).symmL ℝ z w⟩ :
        TangentBundle I M)) y :=
    ((trivializationAt E (TangentSpace I) α).contMDiffAt_symmL
      (by simpa using hy)).clm_bundle_apply (by
        rw [contMDiffAt_section_iff]
        exact contMDiffAt_const)
  exact hframe.mdifferentiableAt one_ne_zero

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary coordinate Hessian in a fixed chart, with its exact native connection
correction. -/
theorem hessian_fixedChart (α : M) {y : M}
    (hy : y ∈ (chartAt H α).source)
    (hint : extChartAt I α y ∈ interior (extChartAt I α).target)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f y) (v w : E) :
    TauCeti.Manifold.hessian I f y
        ((trivializationAt E (TangentSpace I) α).symmL ℝ y v)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ y w) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I α).symm)) (extChartAt I α y) v w -
        mvfderiv I f y
          (CovariantDerivative.leviCivitaConnection I M
            (fun z => (trivializationAt E (TangentSpace I) α).symmL ℝ z w) y
            ((trivializationAt E (TangentSpace I) α).symmL ℝ y v)) := by
  let φ := extChartAt I α
  let F := f ∘ φ.symm
  let G : E → ℝ := fun z => fderiv ℝ F z w
  have hround : φ.symm (φ y) = y := φ.left_inv (by rwa [extChartAt_source])
  have hinv : ContMDiffAt 𝓘(ℝ, E) I 2 φ.symm (φ y) :=
    (contMDiffOn_extChartAt_symm α (φ y) (interior_subset hint)).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset)
  have hF : ContDiffAt ℝ 2 F (φ y) :=
    (ContMDiffAt.comp (φ y) (hround.symm ▸ hf) hinv).contDiffAt
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (φ y) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ G (φ y) := hdF.clm_apply (differentiableAt_const w)
  have heq : (fun z => mvfderiv I f z
      ((trivializationAt E (TangentSpace I) α).symmL ℝ z w)) =ᶠ[𝓝 y] G ∘ φ := by
    have hevent : ∀ᶠ z in 𝓝 y, φ z ∈ interior φ.target :=
      (mdifferentiableAt_extChartAt hy).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hint)
    filter_upwards [hf.eventually_mdifferentiableAt (by norm_num),
      (chartAt H α).open_source.mem_nhds hy, hevent] with z hfz hz hiz
    exact mvfderiv_inverseChart_vector α hz hiz hfz w
  have hdir : mvfderiv I (fun z => mvfderiv I f z
        ((trivializationAt E (TangentSpace I) α).symmL ℝ z w)) y
        ((trivializationAt E (TangentSpace I) α).symmL ℝ y v) =
      fderiv ℝ (fderiv ℝ F) (φ y) v w := by
    rw [heq.mvfderiv_eq]
    rw [mvfderiv_comp_apply y (mdifferentiableAt_iff_differentiableAt.mpr hG)
      (mdifferentiableAt_extChartAt hy)]
    rw [mfderiv_chart_inverseVector α hy, mvfderiv_eq_fderiv]
    change fderiv ℝ G (φ y) v = _
    dsimp only [G]
    rw [fderiv_clm_apply hdF (differentiableAt_const w)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  rw [TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub y hf
    (fun z => (trivializationAt E (TangentSpace I) α).symmL ℝ z v)
    (fun z => (trivializationAt E (TangentSpace I) α).symmL ℝ z w)
    (mdifferentiableAt_chartConstantVector α hy w), hdir]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The covariant Hessian differs from the ordinary chart Hessian by the connection term.
The chart at its own center has identity tangent trivialization, including for a manifold
with boundary; only the evaluation point is required to be interior. -/
theorem hessian_centerChart (x : M) (hint : I.IsInteriorPoint x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : E) :
    TauCeti.Manifold.hessian I f x v w =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x) v w -
        mvfderiv I f x
          (CovariantDerivative.leviCivitaConnection I M (FiberBundle.extend (x := x) E w) x v) := by
  let φ := extChartAt I x
  let F := f ∘ φ.symm
  let G : E → ℝ := fun z => fderiv ℝ F z w
  have hxi : φ x ∈ interior φ.target := ModelWithCorners.isInteriorPoint_iff.mp hint
  have hinv : ContMDiffAt 𝓘(ℝ, E) I 2 φ.symm (φ x) :=
    (contMDiffOn_extChartAt_symm x (φ x) (interior_subset hxi)).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset)
  have hround : φ.symm (φ x) = x := φ.left_inv (mem_extChartAt_source x)
  have hF : ContDiffAt ℝ 2 F (φ x) :=
    (ContMDiffAt.comp (φ x) (hround.symm ▸ hf) hinv).contDiffAt
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (φ x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ G (φ x) := hdF.clm_apply (differentiableAt_const w)
  have heq : (fun y => mvfderiv I f y (FiberBundle.extend (x := x) E w y)) =ᶠ[𝓝 x] G ∘ φ := by
    have hevent : ∀ᶠ y in 𝓝 x, φ y ∈ interior φ.target :=
      (contMDiffAt_extChartAt (I := I) (n := 1)).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hxi)
    filter_upwards [hf.eventually_mdifferentiableAt (by norm_num),
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x), hevent] with y hfy hy hiy
    rw [TauCeti.Manifold.extend_eq_trivializationAt_symm (x := x)]
    dsimp only
    rw [← (trivializationAt E (TangentSpace I) x).symmL_apply (R := ℝ)
      (by simpa using hy) w]
    exact mvfderiv_inverseChart_vector x hy hiy hfy w
  have hdir : mvfderiv I (fun y => mvfderiv I f y (FiberBundle.extend (x := x) E w y)) x v =
      fderiv ℝ (fderiv ℝ F) (φ x) v w := by
    rw [heq.mvfderiv_eq]
    rw [mvfderiv_comp_apply x (mdifferentiableAt_iff_differentiableAt.mpr hG)
      (mdifferentiableAt_extChartAt (mem_chart_source H x)) v]
    rw [mfderiv_extChartAt_self]
    change mvfderiv 𝓘(ℝ, E) G (φ x) v = _
    rw [mvfderiv_eq_fderiv]
    change fderiv ℝ G (φ x) v = _
    dsimp only [G]
    rw [fderiv_clm_apply hdF (differentiableAt_const w)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
  have h := TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub x hf
    (FiberBundle.extend (x := x) E v) (FiberBundle.extend (x := x) E w)
    (FiberBundle.mdifferentiableAt_extend (x := x) (V := TangentSpace I) I E
      (w : TangentSpace I x))
  simpa only [FiberBundle.extend_apply_self, hdir] using h

end Hessian

end ConformalPoisson

end RefPart_InteriorChartDerivative

/- Interface support: NativeChartPullbackDerivative.lean, SHA256 6de744cd94d4ed1f7122e0e59c0e01d3f1853e8254b50ba23f7ee2332125a3f6 -/
noncomputable section RefPart_NativeChartPullbackDerivative

/-! The actual derivative of the original-manifold chart is its actual inverse
chart frame applied to the differential of the same ambient map, also at time zero. -/

open Bundle Filter Set Topology TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
theorem nativeHalfSpaceChart_mfderiv_apply
    (α : M)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (v : TangentSpace (𝓡∂ (n + 1)) z) :
    let χ := nativeHalfSpaceChart α C hforward hbackward
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z v =
      (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ (χ z) (fderiv ℝ C z.1 v) := by
  let χ := nativeHalfSpaceChart α C hforward hbackward
  let φ := extChartAt (𝓡∂ (n + 1)) α
  have hsource := nativeHalfSpaceChart_source α C hforward hbackward htarget
  have hzχ : z ∈ χ.source := by rw [hsource]; exact hz
  have hcoordinate (w : EuclideanHalfSpace (n + 1)) (hw : w.1 ∈ C.source) :
      φ (χ w) = C w.1 := by
    rw [nativeHalfSpaceChart_apply]
    exact φ.right_inv (htarget w.1 hw w.property)
  have hyφ : χ z ∈ φ.source := by
    rw [nativeHalfSpaceChart_apply]
    exact φ.map_target (htarget z.1 hz z.property)
  have hy : χ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    simpa only [φ, extChartAt_source] using hyφ
  have heq : (φ ∘ χ) =ᶠ[nhds z] (fun w : EuclideanHalfSpace (n + 1) => C w.1) := by
    filter_upwards [χ.open_source.mem_nhds hzχ] with w hw
    apply hcoordinate
    change w ∈ (nativeHalfSpaceChart α C hforward hbackward).source at hw
    rw [hsource] at hw
    exact hw
  have hχ := χ.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hzχ
  have hφ : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) φ (χ z) :=
    mdifferentiableAt_extChartAt hy
  have hC : DifferentiableAt ℝ C z.1 :=
    ((C.contMDiffOn_toFun z.1 hz).contMDiffAt (C.open_source.mem_nhds hz)).contDiffAt.differentiableAt
      (by decide : (ω : ℕ∞ω) ≠ 0)
  have hI : mvfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) z v = v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, (𝓡∂ (n + 1)).hasMFDerivAt.mfderiv]
    rfl
  have hH : mvfderiv (𝓡∂ (n + 1))
      (fun w : EuclideanHalfSpace (n + 1) => C w.1) z v = fderiv ℝ C z.1 v := by
    exact (TauCeti.mvfderiv_comp_apply_of_differentiableAt (g := (𝓡∂ (n + 1))) hC
      (𝓡∂ (n + 1)).hasMFDerivAt.mdifferentiableAt v).trans (congrArg (fderiv ℝ C z.1) hI)
  have hG : mvfderiv (𝓡∂ (n + 1)) φ (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z v) = fderiv ℝ C z.1 v := by
    exact (mvfderiv_comp_apply z hφ hχ v).symm.trans
      ((congrArg (fun L => L v) heq.mvfderiv_eq).trans hH)
  apply (isInvertible_mfderiv_extChartAt
    hyφ).injective
  exact hG.trans (mfderiv_chart_inverseVector α hy (fderiv ℝ C z.1 v)).symm
end ConformalPoisson

end RefPart_NativeChartPullbackDerivative

/- Interface support: NativeChartPullbackMetric.lean, SHA256 4fd681a5351dccd0a650faaf28f0d6b8172cd59383b3f0e35673102eb71d7e0f -/
noncomputable section RefPart_NativeChartPullbackMetric

/-! Actual original pullback metric equals the same ambient coordinate tensor
on the actual ambient-map derivatives, including at boundary points. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
theorem nativeHalfSpaceChart_inner
    {g : Metric (n := n) (M := M)} {α : M} (R : NativeMetricAmbientExtension g α)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (v w : TangentSpace (𝓡∂ (n + 1)) z) :
    let χ := nativeHalfSpaceChart α C hforward hbackward
    let D := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
    g.inner (χ z) (D v) (D w) = R.tensor (C z.1) (fderiv ℝ C z.1 v) (fderiv ℝ C z.1 w) := by
  dsimp only
  rw [nativeHalfSpaceChart_mfderiv_apply α C hforward hbackward htarget hz v,
    nativeHalfSpaceChart_mfderiv_apply α C hforward hbackward htarget hz w]
  have hy : nativeHalfSpaceChart α C hforward hbackward z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    rw [nativeHalfSpaceChart_apply]
    simpa only [extChartAt_source] using
      (extChartAt (𝓡∂ (n + 1)) α).map_target (htarget z.1 hz z.property)
  rw [← metricTensorRead_apply g α hy]
  rw [nativeHalfSpaceChart_apply]
  exact congrArg (fun B : CoordinateBilinear n => B (fderiv ℝ C z.1 v) (fderiv ℝ C z.1 w))
    (R.agrees (htarget z.1 hz z.property))
end ConformalPoisson

end RefPart_NativeChartPullbackMetric

/- Interface support: NativeNormalChartGauss.lean, SHA256 491621be5c4667ea503a5a534001ac8b6da7c948ffcf8b5c87ed9a18222c0fe0 -/
noncomputable section RefPart_NativeNormalChartGauss

/-! Gauss form for the ACTUAL differential of the ACTUAL original-manifold
analytic normal chart, with the same original metric and normal-map witnesses. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
  (R : NativeMetricAmbientExtension g (α : M))

local instance : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
local instance : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)

variable {D : BoundaryNormalMapData R.domain R.boundaryBase}
  {Q : BoundaryNormalRectangle R.domain D} (A : NormalModelChartData R.domain D Q)


theorem NativeMetricAmbientExtension.normalChart_time_inner
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) :
    let Dχ := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (R.normalChart A) z
    g.inner (R.normalChart A z)
      (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
      (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 1 := by
  have htarg : ∀ y ∈ A.chart.source, 0 ≤ y 0 →
      A.chart y ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target :=
    fun y hy hpos => hcompat (A.chart y) (A.image_mem y hy) ((A.side y hy).mpr hpos)
  have hmetric := nativeHalfSpaceChart_inner R A.chart A.side
    (fun _ hy => A.side_symm R.domain hy) htarg hz
    (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
    (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
  refine hmetric.trans ?_
  obtain ⟨p, _, hc, _⟩ := A.reads z.1 hz
  have hpval : normalParameterRead (boundaryParameterDomain R.domain) p = z.1 :=
    (congrArg (euclideanHalfSpaceBoundaryNormalEquiv n) hc).symm.trans
      ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply z.1)
  have hp : normalParameterRead (boundaryParameterDomain R.domain) p ∈ A.chart.source :=
    hpval.symm ▸ hz
  simpa only [hpval] using R.normalModel_time_inner A hp

theorem NativeMetricAmbientExtension.normalChart_spatial_time_inner
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    let Dχ := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (R.normalChart A) z
    g.inner (R.normalChart A z)
      (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)))
      (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 0 := by
  have htarg : ∀ y ∈ A.chart.source, 0 ≤ y 0 →
      A.chart y ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target :=
    fun y hy hpos => hcompat (A.chart y) (A.image_mem y hy) ((A.side y hy).mpr hpos)
  have hmetric := nativeHalfSpaceChart_inner R A.chart A.side
    (fun _ hy => A.side_symm R.domain hy) htarg hz
    (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0))
    (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
  refine hmetric.trans ?_
  obtain ⟨p, _, hc, _⟩ := A.reads z.1 hz
  have hpval : normalParameterRead (boundaryParameterDomain R.domain) p = z.1 :=
    (congrArg (euclideanHalfSpaceBoundaryNormalEquiv n) hc).symm.trans
      ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply z.1)
  have hp : normalParameterRead (boundaryParameterDomain R.domain) p ∈ A.chart.source :=
    hpval.symm ▸ hz
  simpa only [hpval] using R.normalModel_spatial_time_inner A hp v
end ConformalPoisson

end RefPart_NativeNormalChartGauss

/- Interface support: NativeChartCoordinateDerivative.lean, SHA256 932e3b8736c961149fa3dae1c8b0e1b3ae6afd1a9ae5ce729b42d96953225472 -/
noncomputable section RefPart_NativeChartCoordinateDerivative

/-! Actual forward coordinate derivative of the native normal chart. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
set_option backward.isDefEq.respectTransparency false in
theorem nativeHalfSpaceChart_coordinate_mfderiv_apply
    (α : M)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (v : TangentSpace (𝓡∂ (n + 1)) z) :
    let χ := nativeHalfSpaceChart α C hforward hbackward
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (extChartAt (𝓡∂ (n + 1)) α) (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z v) = fderiv ℝ C z.1 v := by
  dsimp only
  rw [nativeHalfSpaceChart_mfderiv_apply α C hforward hbackward htarget hz v]
  have hy : nativeHalfSpaceChart α C hforward hbackward z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    rw [nativeHalfSpaceChart_apply]
    simpa only [extChartAt_source] using
      (extChartAt (𝓡∂ (n + 1)) α).map_target (htarget z.1 hz z.property)
  exact mfderiv_chart_inverseVector α hy (fderiv ℝ C z.1 v)
end ConformalPoisson

end RefPart_NativeChartCoordinateDerivative

/- Interface support: AmbientNormalFactor.lean, SHA256 833c081080721ea3e4528297aa2c154b7226a0e90e21616cce9dc8ea06e540b2 -/
noncomputable section RefPart_AmbientNormalFactor

/-! An actual side-preserving ambient analytic partial diffeomorphism has a
strictly positive normal derivative factor at the boundary. The local-minimum/
tangent-cone argument is adapted from the pinned Tau Ceti TransitionNormal proof;
its Apache-2.0 license is retained in External/LICENSE.tauceti. -/

open Filter Set Topology TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}
variable
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)

theorem ambientHalfSpace_derivative_normal_nonneg
    (hside : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.source)
    (hzero : z 0 = 0) (hCzero : C z 0 = 0)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) :
    0 ≤ (fderiv ℝ C z v) 0 := by
  let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := {y | 0 ≤ y 0}
  let π := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
  let f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := π ∘ C
  have hf0 : f z = 0 := hCzero
  have hmin : IsLocalMinOn f S z := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (C.open_source.mem_nhds hz),
      self_mem_nhdsWithin] with y hy hyS
    change f z ≤ f y
    rw [hf0]
    exact (hside y hy).mpr hyS
  have hC : DifferentiableAt ℝ C z :=
    ((C.contMDiffOn_toFun z hz).contMDiffAt (C.open_source.mem_nhds hz)).contDiffAt.differentiableAt
      (by decide : (ω : ℕ∞ω) ≠ 0)
  have hdf : HasFDerivWithinAt f (π.comp (fderiv ℝ C z)) S z :=
    (π.hasFDerivAt.comp z hC.hasFDerivAt).hasFDerivWithinAt
  have hcone : v ∈ posTangentConeAt S z := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (EuclideanHalfSpace.convex (n := n + 1)).segment_subset (show z ∈ S from hzero.ge)
    change 0 ≤ (z + v) 0
    simpa only [PiLp.add_apply, hzero, zero_add] using hv
  exact hmin.hasFDerivWithinAt_nonneg hdf hcone

theorem ambientPartialDiffeomorph_fderiv_surjective
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.source) :
    Function.Surjective (fderiv ℝ C z) := by
  have hsurj := ((PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ω C hz).isInvertible_mfderiv
    (by decide : (ω : ℕ∞ω) ≠ 0)).surjective
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨v, ?_⟩
  have h' : mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) C z v = w :=
    (mvfderiv_apply_eq_mfderiv_apply C z v).trans hv
  exact (mvfderiv_eq_fderiv_apply C z v).symm.trans h'

theorem ambientHalfSpace_derivative_normal_pos
    (hside : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ C.source)
    (hzero : z 0 = 0) (hCzero : C z 0 = 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : EuclideanSpace ℝ (Fin (n + 1)),
      (fderiv ℝ C z v) 0 = a * v 0 := by
  let D := fderiv ℝ C z
  let π := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
  let ν := EuclideanSpace.single (𝕜 := ℝ) (0 : Fin (n + 1)) 1
  let a := (D ν) 0
  have hnonneg (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : 0 ≤ v 0) : 0 ≤ (D v) 0 :=
    ambientHalfSpace_derivative_normal_nonneg C hside hz hzero hCzero v hv
  have hfactor (v : EuclideanSpace ℝ (Fin (n + 1))) : (D v) 0 = a * v 0 :=
    Module.Dual.apply_eq_mul_apply_of_nonneg (EuclideanSpace.projₗ (𝕜 := ℝ) 0)
      (π.comp D : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) (x := ν) (by simp [ν]) hnonneg v
  have ha : 0 ≤ a := hnonneg ν (by simp [ν])
  have hpos : 0 < a := by
    by_contra hn
    have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
    obtain ⟨v, hv⟩ := ambientPartialDiffeomorph_fderiv_surjective C hz ν
    have h := hfactor v
    rw [hv, ha0, zero_mul] at h
    simp [ν] at h
  exact ⟨a, hpos, hfactor⟩
end ConformalPoisson

end RefPart_AmbientNormalFactor

/- Interface support: NormalAlgebra.lean, SHA256 55949bd27ed1fd060968358d1bb40d18cf061c25222f75e70ae5753ea1894a75 -/
noncomputable section RefPart_NormalAlgebra

/-! The unit outward normal of a regular level hypersurface is its negative unit gradient. -/


open scoped InnerProductSpace

namespace ConformalPoisson

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A unit vector orthogonal to a level hyperplane, pointing toward decreasing level,
is the negative normalized metric dual of the level covector. -/
theorem normal_eq_neg_normalize_gradient
    (ℓ : V →ₗ[ℝ] ℝ) (G ν : V) (hG : ∀ u, ⟪G, u⟫_ℝ = ℓ u)
    (hunit : ⟪ν, ν⟫_ℝ = 1) (hneg : ℓ ν < 0)
    (horth : ∀ u, ℓ u = 0 → ⟪ν, u⟫_ℝ = 0) :
    ν = -NormedSpace.normalize G := by
  have hℓ : ℓ ν ≠ 0 := ne_of_lt hneg
  have hid (u : V) : ⟪ν, u⟫_ℝ = ℓ u / ℓ ν := by
    have hker : ℓ (u - (ℓ u / ℓ ν) • ν) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    have h := horth _ hker
    simp only [inner_sub_right, real_inner_smul_right, hunit, mul_one] at h
    exact sub_eq_zero.mp h
  have hs : (ℓ ν) ^ 2 = ‖G‖ ^ 2 := by
    have h := hid G
    rw [real_inner_comm, hG ν] at h
    have hGG := hG G
    rw [real_inner_self_eq_norm_sq] at hGG
    rw [← hGG] at h
    field_simp at h
    nlinarith
  have hnorm : ℓ ν = -‖G‖ := by nlinarith [norm_nonneg G]
  apply ext_inner_right ℝ
  intro u
  rw [hid, NormedSpace.normalize, inner_neg_left, real_inner_smul_left, hG u, hnorm]
  simp only [inv_neg, div_eq_mul_inv]
  ring

end ConformalPoisson

end RefPart_NormalAlgebra

/- Interface support: BoundaryNormalFormula.lean, SHA256 552c42419d82834eef2a3b4f7f4d420bdf5816b2ba67a2484a1205eda3fa11ea -/
noncomputable section RefPart_BoundaryNormalFormula

/-!
Pointwise identification of the supplied actual unit outward normal with a
negative unit gradient of a local boundary defining coordinate.
-/


open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def nativeNegativeUnitGradient (g : Metric (n := n) (M := M)) (f : M → ℝ) (x : M) :
    TangentSpace (𝓡∂ (n + 1)) x :=
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩;
  -NormedSpace.normalize (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) f x)

set_option backward.isDefEq.respectTransparency false in
/-- The positive chart-transition normal factor identifies the same native unit normal. -/
theorem IsOutwardUnitNormal.eq_nativeNegativeUnitGradient
    (g : Metric (n := n) (M := M)) (x : (𝓡∂ (n + 1)).boundary M)
    (ν : TangentSpace (𝓡∂ (n + 1)) (x : M)) (hν : IsOutwardUnitNormal g x ν)
    (f : M → ℝ) (a : ℝ) (ha : 0 < a)
    (hfactor : ∀ v : TangentSpace (𝓡∂ (n + 1)) (x : M),
      mvfderiv (𝓡∂ (n + 1)) f x v = a * (show EuclideanSpace ℝ (Fin (n + 1)) from v) 0) :
    ν = nativeNegativeUnitGradient g f x := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  change ν = -NormedSpace.normalize (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) f x)
  apply normal_eq_neg_normalize_gradient (mvfderiv (𝓡∂ (n + 1)) f x).toLinearMap
  · intro u
    exact TauCeti.Manifold.inner_mgradient (I := 𝓡∂ (n + 1)) (f := f) (x := (x : M)) u
  · exact hν.2.1
  · change mvfderiv (𝓡∂ (n + 1)) f x ν < 0
    rw [hfactor]
    have hneg := hν.1.coordinate_deriv_neg
    rw [mfderiv_extChartAt_self] at hneg
    exact mul_neg_of_pos_of_neg ha hneg
  · intro u hu
    have hu0 : (show EuclideanSpace ℝ (Fin (n + 1)) from u) 0 = 0 := by
      have h := (hfactor u).symm.trans hu
      exact (mul_eq_zero.mp h).resolve_left ha.ne'
    have horth := hν.2.2 (TauCeti.euclideanHalfSpaceBoundaryProj n u)
    have huMem : (show EuclideanSpace ℝ (Fin (n + 1)) from u) ∈
        TauCeti.euclideanHalfSpaceBoundary n := by
      exact TauCeti.mem_euclideanHalfSpaceBoundary.mpr hu0
    rw [TauCeti.mfderiv_subtypeVal_boundary] at horth
    change g.inner x ν (TauCeti.euclideanHalfSpaceBoundaryParam n
      (TauCeti.euclideanHalfSpaceBoundaryProj n (show EuclideanSpace ℝ (Fin (n + 1)) from u))) = 0 at horth
    rw [TauCeti.euclideanHalfSpaceBoundaryParam_proj huMem] at horth
    exact horth

end ConformalPoisson

end RefPart_BoundaryNormalFormula

/- Interface support: ChartBoundaryFunction.lean, SHA256 9aa91ac7efc125388749fda5ec710b000c47dfa7bf0f0c01fe3f21d0ab0fb2cf -/
noncomputable section RefPart_ChartBoundaryFunction

/-! The actual inward coordinate of a fixed chart, its derivative and normal factor. -/


open Bundle Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def chartBoundaryFunction (α : M) : M → ℝ :=
  EuclideanSpace.proj (0 : Fin (n + 1)) ∘ extChartAt (𝓡∂ (n + 1)) α

theorem contMDiffOn_chartBoundaryFunction (α : M) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (chartBoundaryFunction (n := n) α)
      (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
  exact (EuclideanSpace.proj (0 : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt (I := 𝓡∂ (n + 1)) (x := α))

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_chartBoundaryFunction (α : M) {x : M}
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (v : TangentSpace (𝓡∂ (n + 1)) x) :
    mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) x v =
      (tangentCoordChange (𝓡∂ (n + 1)) x α x v) 0 := by
  unfold chartBoundaryFunction
  rw [(EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply
    (mdifferentiableAt_extChartAt (I := 𝓡∂ (n + 1)) hx)]
  rw [mvfderiv_apply_eq_mfderiv_apply, (hasMFDerivAt_extChartAt (I := 𝓡∂ (n + 1)) hx).mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange hx]
  rfl

/-- Its derivative is a positive multiple of the preferred tangent zeroth coordinate. -/
theorem chartBoundaryFunction_normal_factor (α : M)
    (x : (𝓡∂ (n + 1)).boundary M)
    (hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    ∃ a : ℝ, 0 < a ∧ ∀ v : TangentSpace (𝓡∂ (n + 1)) (x : M),
      mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) x v =
        a * (show EuclideanSpace ℝ (Fin (n + 1)) from v) 0 := by
  obtain ⟨a, ha, hfactor⟩ := TauCeti.tangentCoordChange_normal_pos x.property
    (mem_extChartAt_source (I := 𝓡∂ (n + 1)) (x : M))
    (show (x : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source by rwa [extChartAt_source])
  exact ⟨a, ha, fun v => (mvfderiv_chartBoundaryFunction (n := n) α hx v).trans (hfactor v)⟩

theorem IsOutwardUnitNormal.eq_nativeNegativeUnitGradient_chart
    (g : Metric (n := n) (M := M)) (α : M) (x : (𝓡∂ (n + 1)).boundary M)
    (hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (ν : TangentSpace (𝓡∂ (n + 1)) (x : M)) (hν : IsOutwardUnitNormal g x ν) :
    ν = nativeNegativeUnitGradient g (chartBoundaryFunction (n := n) α) x := by
  obtain ⟨a, ha, hfactor⟩ := chartBoundaryFunction_normal_factor α x hx
  exact hν.eq_nativeNegativeUnitGradient g x ν (chartBoundaryFunction (n := n) α) a ha hfactor

end ConformalPoisson

end RefPart_ChartBoundaryFunction

/- Interface support: NativeChartNormalFactor.lean, SHA256 34a6644d33071d4f90467e2341bfdaf6387e81758c7dda5192b4ee73023b5888 -/
noncomputable section RefPart_NativeChartNormalFactor

/-! The actual defining covector on the original manifold reads the actual
normal-chart derivative by one strictly positive normal factor. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
theorem nativeHalfSpaceChart_normalFactor
    (α : M)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (hzero : z.1 0 = 0) (hCzero : C z.1 0 = 0) :
    let χ := nativeHalfSpaceChart α C hforward hbackward
    ∃ a : ℝ, 0 < a ∧ ∀ v : TangentSpace (𝓡∂ (n + 1)) z,
      mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) (χ z)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z v) =
          a * (show EuclideanSpace ℝ (Fin (n + 1)) from v) 0 := by
  let χ := nativeHalfSpaceChart α C hforward hbackward
  obtain ⟨a, ha, hfactor⟩ := ambientHalfSpace_derivative_normal_pos C hforward hz hzero hCzero
  refine ⟨a, ha, ?_⟩
  intro v
  have hy : χ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    rw [nativeHalfSpaceChart_apply]
    simpa only [extChartAt_source] using
      (extChartAt (𝓡∂ (n + 1)) α).map_target (htarget z.1 hz z.property)
  have hφ := mdifferentiableAt_extChartAt (I := 𝓡∂ (n + 1)) hy
  have hc := nativeHalfSpaceChart_coordinate_mfderiv_apply α C hforward hbackward htarget hz v
  have hd : mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z v) =
        (fderiv ℝ C z.1 v) 0 := by
    unfold chartBoundaryFunction
    rw [(EuclideanSpace.proj (0 : Fin (n + 1))).mvfderiv_comp_apply hφ]
    exact congrArg (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)))
      ((mvfderiv_apply_eq_mfderiv_apply _ _ _).trans hc)
  exact hd.trans (hfactor v)
end ConformalPoisson

end RefPart_NativeChartNormalFactor

/- Interface support: NormalFrameAlgebra.lean, SHA256 54d0717788f9ba94d94b6963410ddd99269f88d12f86316db58c97b73d8d347a -/
noncomputable section RefPart_NormalFrameAlgebra

/-! An actual surjective frame with Gauss cross terms makes its time column
orthogonal to the entire kernel of the actual normal covector. -/

open TauCeti

namespace ConformalPoisson
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem normalFrame_time_orthogonal_kernel
    (B : V → V → ℝ) (hsymm : ∀ v w, B v w = B w v)
    (D : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] V) (hD : Function.Surjective D)
    (ℓ : V →ₗ[ℝ] ℝ) (a : ℝ) (ha : a ≠ 0)
    (hfactor : ∀ v, ℓ (D v) = a * v 0)
    (hgauss : ∀ v : EuclideanSpace ℝ (Fin n),
      B (D (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)))
        (D (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 0)
    (u : V) (hu : ℓ u = 0) :
    B (D (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) u = 0 := by
  obtain ⟨v, rfl⟩ := hD u
  have hv0 : v 0 = 0 := (mul_eq_zero.mp ((hfactor v).symm.trans hu)).resolve_left ha
  have hv : euclideanHalfSpaceBoundaryNormalEquiv n (euclideanHalfSpaceBoundaryProj n v, 0) = v := by
    rw [euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
    exact euclideanHalfSpaceBoundaryParam_proj (mem_euclideanHalfSpaceBoundary.mpr hv0)
  rw [hsymm]
  have h := hgauss (euclideanHalfSpaceBoundaryProj n v)
  rw [hv] at h
  exact h
end ConformalPoisson

end RefPart_NormalFrameAlgebra

/- Interface support: NativeNormalVector.lean, SHA256 185889fddcbf0b6b7e81d828c616d1bd08ba9329acb7ba303d46cd65926eaa06 -/
noncomputable section RefPart_NativeNormalVector

/-! A unit vector orthogonal to the actual defining-covector kernel and
pointing inward is the negative of the actual outward unit normal. -/

open Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
theorem IsOutwardUnitNormal.eq_neg_of_unit_inward_orthogonal_kernel
    (g : Metric (n := n) (M := M)) (α : M) (y : (𝓡∂ (n + 1)).boundary M)
    (hy : (y : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (ν δ : TangentSpace (𝓡∂ (n + 1)) (y : M)) (hν : IsOutwardUnitNormal g y ν)
    (hunit : g.inner y δ δ = 1)
    (hpos : 0 < mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) y δ)
    (horth : ∀ u : TangentSpace (𝓡∂ (n + 1)) (y : M),
      mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) y u = 0 →
        g.inner y δ u = 0) : ν = -δ := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) := ⟨g.toRiemannianMetric⟩
  have hνG := IsOutwardUnitNormal.eq_nativeNegativeUnitGradient_chart g α y hy ν hν
  have hδG : -δ = nativeNegativeUnitGradient g (chartBoundaryFunction (n := n) α) y := by
    change -δ = -NormedSpace.normalize
      (TauCeti.Manifold.mgradient (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) y)
    apply normal_eq_neg_normalize_gradient
      (mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) y).toLinearMap
    · intro u
      exact TauCeti.Manifold.inner_mgradient u
    · change g.inner y (-δ) (-δ) = 1
      simpa only [map_neg, neg_apply, neg_neg] using hunit
    · change mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) y (-δ) < 0
      rw [map_neg]
      exact neg_neg_of_pos hpos
    · intro u hu
      change g.inner y (-δ) u = 0
      rw [map_neg, neg_apply, horth u hu, neg_zero]
  exact hνG.trans hδG.symm
end ConformalPoisson

end RefPart_NativeNormalVector

/- Interface support: NativeChartNormalVector.lean, SHA256 e90a0711354b7ab5b3239aa77434e4b3ec18e9c1c73b236a7fd76b58b2a513e9 -/
noncomputable section RefPart_NativeChartNormalVector

/-! The negative time column is the ACTUAL supplied outward unit normal.
Gauss plus invertibility spans the full defining-covector kernel. The earlier
native normal/gradient identification supplies intrinsic-boundary orthogonality. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
theorem nativeHalfSpaceChart_outwardNormal_eq_neg_time
    (g : Metric (n := n) (M := M)) (α : M)
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hforward : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hbackward : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    (htarget : ∀ z ∈ C.source, 0 ≤ z 0 → C z ∈ (extChartAt (𝓡∂ (n + 1)) α).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (hzero : z.1 0 = 0) (hCzero : C z.1 0 = 0)
    (hyB : nativeHalfSpaceChart α C hforward hbackward z ∈ (𝓡∂ (n + 1)).boundary M)
    (ν : TangentSpace (𝓡∂ (n + 1)) (nativeHalfSpaceChart α C hforward hbackward z))
    (hν : IsOutwardUnitNormal g ⟨nativeHalfSpaceChart α C hforward hbackward z, hyB⟩ ν)
    (hunit :
      let χ := nativeHalfSpaceChart α C hforward hbackward
      let Dχ := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
      g.inner (χ z) (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
        (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 1)
    (hgauss : ∀ v : EuclideanSpace ℝ (Fin n),
      let χ := nativeHalfSpaceChart α C hforward hbackward
      let Dχ := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
      g.inner (χ z) (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)))
        (Dχ (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 0) :
    ν = -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (nativeHalfSpaceChart α C hforward hbackward) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  let χ := nativeHalfSpaceChart α C hforward hbackward
  let L := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
  let ℓ := mvfderiv (𝓡∂ (n + 1)) (chartBoundaryFunction (n := n) α) (χ z)
  obtain ⟨a, ha, hfactor⟩ := nativeHalfSpaceChart_normalFactor α C hforward hbackward htarget hz hzero hCzero
  have hzχ : z ∈ χ.source := by
    rw [nativeHalfSpaceChart_source α C hforward hbackward htarget]
    exact hz
  have hsurj := (PartialDiffeomorph.isLocalDiffeomorphAt
    (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω χ hzχ).isInvertible_mfderiv
      (by decide : (ω : ℕ∞ω) ≠ 0) |>.surjective
  have hy : χ z ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    rw [nativeHalfSpaceChart_apply]
    simpa only [extChartAt_source] using
      (extChartAt (𝓡∂ (n + 1)) α).map_target (htarget z.1 hz z.property)
  have hpos : 0 < ℓ (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) := by
    have h := hfactor (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
    simp only [euclideanHalfSpaceBoundaryNormalEquiv_apply_zero, mul_one] at h
    exact ha.trans_eq h.symm
  have horth : ∀ u : TangentSpace (𝓡∂ (n + 1)) (χ z), ℓ u = 0 →
      g.inner (χ z) (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) u = 0 := by
    exact normalFrame_time_orthogonal_kernel (V := TangentSpace (𝓡∂ (n + 1)) (χ z))
      (fun v w => g.inner (χ z) v w) (fun v w => g.symm (χ z) v w)
      L.toLinearMap hsurj ℓ.toLinearMap a ha.ne' (fun v => hfactor v) (fun v => hgauss v)
  exact IsOutwardUnitNormal.eq_neg_of_unit_inward_orthogonal_kernel g α ⟨χ z, hyB⟩ hy ν
    (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) hν hunit hpos horth
end ConformalPoisson

end RefPart_NativeChartNormalVector

/- Interface support: NormalDerivativeChart.lean, SHA256 3af582806b1eb71ef4abdd150d6c93727d3372e1a111f9fae0c2b17036afaba8 -/
noncomputable section RefPart_NormalDerivativeChart

/-! Boundary transport and the actual native outward/time derivative identity.
The time derivative is native at the boundary; no arbitrary off-halfspace
extension is differentiated. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

theorem partialDiffeomorph_halfSpace_boundary
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (hzero : z.1 0 = 0) :
    χ z ∈ (𝓡∂ (n + 1)).boundary M := by
  have hzB : (𝓡∂ (n + 1)).IsBoundaryPoint z := by
    change z ∈ (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))
    rw [boundary_euclideanHalfSpace]
    exact hzero
  exact (PartialDiffeomorph.isLocalDiffeomorphAt
    (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω χ hz).isBoundaryPoint_iff
      (by decide : (ω : ℕ∞ω) ≠ 0) |>.mp hzB

theorem normalDerivative_eq_neg_chart_time_of_normal_eq
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source)
    (hyB : χ z ∈ (𝓡∂ (n + 1)).boundary M)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (hνeq : ν ⟨χ z, hyB⟩ = -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
    (u : M → ℝ) (hu : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) u (χ z)) :
    normalDerivative ν u ⟨χ z, hyB⟩ =
      -mvfderiv (𝓡∂ (n + 1)) (u ∘ χ) z (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  have hχ := χ.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hz
  unfold normalDerivative
  rw [hνeq, map_neg]
  exact congrArg Neg.neg (mvfderiv_comp_apply z hu hχ
    (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))).symm
end ConformalPoisson

end RefPart_NormalDerivativeChart

/- Interface support: NativeNormalChartDN.lean, SHA256 85a790a613bee1b98fcb81abe18a243a6500f8326e6336f7c179a6aec1f3bf99 -/
noncomputable section RefPart_NativeNormalChartDN

/-! The SAME actual original normal chart has the actual supplied outward
normal = minus time column, and the actual native DN time-derivative identity. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
  (R : NativeMetricAmbientExtension g (α : M))

local instance : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
local instance : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)

variable {D : BoundaryNormalMapData R.domain R.boundaryBase}
  {Q : BoundaryNormalRectangle R.domain D} (A : NormalModelChartData R.domain D Q)


theorem NativeMetricAmbientExtension.normalChart_boundary_mem
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) (hzero : z.1 0 = 0) :
    R.normalChart A z ∈ (𝓡∂ (n + 1)).boundary M := by
  apply partialDiffeomorph_halfSpace_boundary (R.normalChart A) _ hzero
  rw [R.normalChart_source A hcompat]
  exact hz

theorem NativeMetricAmbientExtension.normalChart_outwardNormal
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) (hzero : z.1 0 = 0)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (hν : ∀ y, IsOutwardUnitNormal g y (ν y)) :
    ν ⟨R.normalChart A z, R.normalChart_boundary_mem A hcompat hz hzero⟩ =
      -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (R.normalChart A) z
        (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  have htarg : ∀ y ∈ A.chart.source, 0 ≤ y 0 →
      A.chart y ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target :=
    fun y hy hpos => hcompat (A.chart y) (A.image_mem y hy) ((A.side y hy).mpr hpos)
  exact nativeHalfSpaceChart_outwardNormal_eq_neg_time g (α : M) A.chart A.side
    (fun _ hy => A.side_symm R.domain hy) htarg hz hzero ((A.boundary z.1 hz).mpr hzero)
    (R.normalChart_boundary_mem A hcompat hz hzero)
    (ν ⟨R.normalChart A z, R.normalChart_boundary_mem A hcompat hz hzero⟩)
    (hν _) (R.normalChart_time_inner A hcompat hz)
    (fun v => R.normalChart_spatial_time_inner A hcompat hz v)

theorem NativeMetricAmbientExtension.normalChart_normalDerivative
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) (hzero : z.1 0 = 0)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (hν : ∀ y, IsOutwardUnitNormal g y (ν y))
    (u : M → ℝ) (hu : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) u (R.normalChart A z)) :
    normalDerivative ν u ⟨R.normalChart A z, R.normalChart_boundary_mem A hcompat hz hzero⟩ =
      -mvfderiv (𝓡∂ (n + 1)) (u ∘ R.normalChart A) z
        (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  have hzχ : z ∈ (R.normalChart A).source := by
    rw [R.normalChart_source A hcompat]
    exact hz
  exact normalDerivative_eq_neg_chart_time_of_normal_eq (R.normalChart A) hzχ
    (R.normalChart_boundary_mem A hcompat hz hzero) ν
    (R.normalChart_outwardNormal A hcompat hz hzero ν hν) u hu
end ConformalPoisson

end RefPart_NativeNormalChartDN

/- Interface support: NormalChartGeometry.lean, SHA256 ab0c6219a2b78887e75297e1dc6177875900f238b90b74efeb04f72258677908 -/
noncomputable section RefPart_NormalChartGeometry

/-! The actual normal-chart geometry consumed by local coefficient and DN
arguments. This is produced by project proofs, not a literature premise. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

structure NormalChartGeometry (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω) : Prop where
  time_inner : ∀ z ∈ χ.source,
    let L := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
    g.inner (χ z) (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
      (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 1
  spatial_time_inner : ∀ z ∈ χ.source, ∀ v : EuclideanSpace ℝ (Fin n),
    let L := mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
    g.inner (χ z) (L (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)))
      (L (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) = 0
  normal : ∀ z, ∀ hz : z ∈ χ.source, ∀ hzero : z.1 0 = 0,
    ∀ (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M)),
      (∀ y, IsOutwardUnitNormal g y (ν y)) →
      ν ⟨χ z, partialDiffeomorph_halfSpace_boundary χ hz hzero⟩ =
        -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z
          (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))

theorem NormalChartGeometry.normalDerivative
    {g : Metric (n := n) (M := M)}
    {χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω}
    (G : NormalChartGeometry g χ) {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source)
    (hzero : z.1 0 = 0)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (hν : ∀ y, IsOutwardUnitNormal g y (ν y)) (u : M → ℝ)
    (hu : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) u (χ z)) :
    normalDerivative ν u ⟨χ z, partialDiffeomorph_halfSpace_boundary χ hz hzero⟩ =
      -mvfderiv (𝓡∂ (n + 1)) (u ∘ χ) z (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) :=
  normalDerivative_eq_neg_chart_time_of_normal_eq χ hz _ ν (G.normal z hz hzero ν hν) u hu
end ConformalPoisson

end RefPart_NormalChartGeometry

/- Interface support: TangentialGram.lean, SHA256 fa48d6f0e284f88a2191dc06f3d4cd496d57851ea92b1c2244ca52c0eaaecfa4 -/
noncomputable section RefPart_TangentialGram

/-! The ACTUAL tangential metric matrix in an actual analytic normal chart,
with native derivative and canonical Euclidean boundary basis. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

set_option backward.isDefEq.respectTransparency false in
def normalTangentialForm (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (z : EuclideanHalfSpace (n + 1)) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) where
  toFun v :=
    { toFun := fun w => g.inner (χ z)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n v))
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w))
      map_add' := by intros; simp only [map_add]
      map_smul' := by intros; simp only [map_smul, smul_eq_mul, RingHom.id_apply] }
  map_add' := by
    intro v₁ v₂
    ext w
    change g.inner (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n (v₁ + v₂)))
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w)) =
      g.inner (χ z)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n v₁))
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w)) +
      g.inner (χ z)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n v₂))
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w))
    simp only [map_add, add_apply]
  map_smul' := by
    intro r v
    ext w
    change g.inner (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n (r • v)))
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w)) =
      r * g.inner (χ z)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n v))
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n w))
    simp only [map_smul, smul_apply, smul_eq_mul]

def normalTangentialGram (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (z : EuclideanHalfSpace (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  (normalTangentialForm g χ z).toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

theorem normalTangentialGram_apply (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (z : EuclideanHalfSpace (n + 1)) (i j : Fin n) :
    normalTangentialGram g χ z i j = g.inner (χ z)
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single i 1)))
      (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ z (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single j 1))) := by
  simp only [normalTangentialGram, LinearMap.BilinForm.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rfl

theorem normalTangentialForm_symmetric (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (z : EuclideanHalfSpace (n + 1)) : (normalTangentialForm g χ z).IsSymm := by
  constructor
  intro v w
  exact g.symm (χ z) _ _

set_option backward.isDefEq.respectTransparency false in
theorem normalTangentialForm_pos (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) : 0 < normalTangentialForm g χ z v v := by
  have hinj := (PartialDiffeomorph.isLocalDiffeomorphAt
    (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω χ hz).isInvertible_mfderiv
      (by decide : (ω : ℕ∞ω) ≠ 0) |>.injective
  have hB : euclideanHalfSpaceBoundaryParam n v ≠ 0 := by
    intro h
    have hp := congrArg (euclideanHalfSpaceBoundaryProj n) h
    simp only [euclideanHalfSpaceBoundaryProj_param, map_zero] at hp
    exact hv hp
  apply g.pos (χ z)
  intro h
  exact hB (hinj (h.trans (map_zero _).symm))

theorem normalTangentialGram_posDef (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    (normalTangentialGram g χ z).PosDef := by
  apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (normalTangentialForm g χ z)
      (normalTangentialForm_symmetric g χ z)).mp
  intro v hv
  exact normalTangentialForm_pos g χ hz v hv
end ConformalPoisson

end RefPart_TangentialGram

/- Interface support: NativeMapVectorFields.lean, SHA256 d5297f372aae8fe5018a7127ca9728cda4491984e2c1f7cc965e34c67435a4c9 -/
noncomputable section RefPart_NativeMapVectorFields

/-! Actual derivative vector fields for an analytic native map, including
a map whose differential may degenerate at a boundary point. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

theorem contMDiffAt_halfSpace_constTangent (w : EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanHalfSpace (n + 1)) (k : ℕ∞ω) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k
      (fun y : EuclideanHalfSpace (n + 1) =>
        (⟨y, (show TangentSpace (𝓡∂ (n + 1)) y from w)⟩ : TangentBundle (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)))) z := by
  apply (contMDiffAt_section_iff z).mpr
  simpa only [trivializationAt_model_space_apply] using
    (contMDiffAt_const : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k
      (fun _ : EuclideanHalfSpace (n + 1) => w) z)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ω M]

theorem nativeMap_vector_contMDiffAt
    {F : EuclideanHalfSpace (n + 1) → M} {z : EuclideanHalfSpace (n + 1)}
    (hF : ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω F z)
    (w : EuclideanSpace ℝ (Fin (n + 1))) (k : ℕ∞ω) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k
      (fun y : EuclideanHalfSpace (n + 1) =>
        (⟨F y, mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) F y w⟩ : TangentBundle (𝓡∂ (n + 1)) M)) z := by
  have hT := hF.contMDiffAt_tangentMap
    (X := (⟨z, w⟩ : TangentBundle (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1))))
    (m := k) le_top
  exact hT.comp z (contMDiffAt_halfSpace_constTangent w z k)
end ConformalPoisson

end RefPart_NativeMapVectorFields

/- Interface support: NormalChartVectorFields.lean, SHA256 83bf2bf85f9c2b73da6d76ed7065e6e3e4d8d6db20ba15a4e4911fb5a0d8fc40 -/
noncomputable section RefPart_NormalChartVectorFields

/-! Genuine smooth constant model tangent sections and their actual images
under the derivative of the actual analytic half-space chart. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}


variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem normalChart_vector_contMDiffAt
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source)
    (w : EuclideanSpace ℝ (Fin (n + 1))) (k : ℕ∞ω) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent k
      (fun y : EuclideanHalfSpace (n + 1) =>
        (⟨χ y, mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ y w⟩ : TangentBundle (𝓡∂ (n + 1)) M)) z := by
  have hχ := (χ.contMDiffOn_toFun z hz).contMDiffAt (χ.open_source.mem_nhds hz)
  exact nativeMap_vector_contMDiffAt hχ w k

end ConformalPoisson

end RefPart_NormalChartVectorFields

/- Interface support: NativeMapPullbackPairing.lean, SHA256 41d7ef21bbb327afed3592c0ed88c6aecb9ff0ce4d85c885d683437b29ff935f -/
noncomputable section RefPart_NativeMapPullbackPairing

/-! The actual possibly DEGENERATE pullback tensor pairing. It is
analytic for analytic F and an analytic metric; it is not packaged as a
positive Riemannian metric and never requires DF to be invertible. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ω M]

def nativeMapPullbackPairing (g : Metric (n := n) (M := M))
    (F : EuclideanHalfSpace (n + 1) → M) (y : EuclideanHalfSpace (n + 1))
    (v w : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  g.inner (F y) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) F y v)
    (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) F y w)

theorem nativeMap_inner_contMDiffAt
    (g : Metric (n := n) (M := M)) {F : EuclideanHalfSpace (n + 1) → M}
    {z : EuclideanHalfSpace (n + 1)} (hF : ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω F z)
    (k : ℕ∞ω)
    (hg : ContMDiffAt (𝓡∂ (n + 1))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) k
      (fun x => TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) x (g.inner x)) (F z))
    (v w : EuclideanSpace ℝ (Fin (n + 1))) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun y => nativeMapPullbackPairing g F y v w) z := by
  have hpair := (hg.comp z (hF.of_le (show k ≤ ω from le_top))).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    (nativeMap_vector_contMDiffAt hF v k) (nativeMap_vector_contMDiffAt hF w k)
  exact (contMDiffAt_totalSpace_iff.mp hpair).2

theorem nativeMapPullbackPairing_analyticOn
    (g : Metric (n := n) (M := M) ω) {F : EuclideanHalfSpace (n + 1) → M}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hF : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ω F S)
    (v w : EuclideanSpace ℝ (Fin (n + 1))) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω
      (fun y => nativeMapPullbackPairing (g.ofLE (by decide)) F y v w) S := by
  intro z hz
  exact (nativeMap_inner_contMDiffAt (g.ofLE (by decide))
    ((hF z hz).contMDiffAt (hS.mem_nhds hz)) ω (by simpa only [ContMDiffRiemannianMetric.ofLE_inner] using g.contMDiff (F z)) v w).contMDiffWithinAt

theorem nativeMapPullbackPairing_self_eq_zero_iff
    (g : Metric (n := n) (M := M)) (F : EuclideanHalfSpace (n + 1) → M)
    (z : EuclideanHalfSpace (n + 1)) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    nativeMapPullbackPairing g F z v v = 0 ↔
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) F z v = 0 := by
  constructor
  · intro hzero
    by_contra hne
    have hpos := g.pos (F z) _ hne
    change 0 < nativeMapPullbackPairing g F z v v at hpos
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · intro hzero
    simp only [nativeMapPullbackPairing, hzero, map_zero]
end ConformalPoisson

end RefPart_NativeMapPullbackPairing

/- Interface support: TangentialGramRegularity.lean, SHA256 11f308f9278fcf5137124e66ea5aaea324dcdd8f4a596c537acd02b678313895 -/
noncomputable section RefPart_TangentialGramRegularity

/-! Regularity of the actual metric coefficients, obtained by pairing the
actual derivative vector fields with the actual native metric section. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem normalChart_inner_contMDiffAt
    (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (k : ℕ∞ω)
    (hg : ContMDiffAt (𝓡∂ (n + 1))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) k
      (fun x => TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) x (g.inner x)) (χ z))
    (v w : EuclideanSpace ℝ (Fin (n + 1))) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y => g.inner (χ y)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ y v)
        (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ y w)) z := by
  exact nativeMap_inner_contMDiffAt g
    ((χ.contMDiffOn_toFun z hz).contMDiffAt (χ.open_source.mem_nhds hz)) k hg v w

theorem normalTangentialGram_contMDiffAt
    (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞
      (normalTangentialGram g χ) z := by
  apply contMDiffAt_pi_module_iff.mpr
  intro i
  apply contMDiffAt_pi_module_iff.mpr
  intro j
  simpa only [normalTangentialGram_apply] using normalChart_inner_contMDiffAt g χ hz ∞
    (g.contMDiff (χ z))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single i 1))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single j 1))

theorem normalTangentialGram_analyticAt
    (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (U : TopologicalSpace.Opens M) (hg : MetricAnalyticOn g U)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (hU : χ z ∈ U) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω
      (normalTangentialGram g χ) z := by
  apply contMDiffAt_pi_module_iff.mpr
  intro i
  apply contMDiffAt_pi_module_iff.mpr
  intro j
  simpa only [normalTangentialGram_apply] using normalChart_inner_contMDiffAt g χ hz ω
    ((hg (χ z) hU).contMDiffAt (U.isOpen.mem_nhds hU))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single i 1))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single j 1))
end ConformalPoisson

end RefPart_TangentialGramRegularity

/- Interface support: TangentialInverse.lean, SHA256 0ee1da9d65f42305c2c08f36e3dcc4e87b5e8ad05b6794cdf42c1b2863078944 -/
noncomputable section RefPart_TangentialInverse

/-! The actual inverse tangential Gram matrix. The determinant/adjugate
regularity argument adapts Tau Ceti's ChartGram.lean (pin recorded in the
project), `contMDiffOn_matrix_det_of_entries` and the adjugate/inverse entry
proofs, Apache-2.0; see External/LICENSE.tauceti. Here it applies at a point
and at any order, including analytic order, to the actual normal chart. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalMatrix_det_contMDiffAt
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {z : EuclideanHalfSpace (n + 1)} {k : ℕ∞ω}
    (hA : ∀ i j, ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun x => A x i j) z) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun x => (A x).det) z := by
  classical
  have hexp : (fun x => (A x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContMDiffAt.sum fun σ _ => ?_
  refine contMDiffAt_const.mul ?_
  exact ContMDiffAt.prod fun i _ => hA (σ i) i

theorem normalMatrix_adjugate_contMDiffAt
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {z : EuclideanHalfSpace (n + 1)} {k : ℕ∞ω}
    (hA : ∀ i j, ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun x => A x i j) z)
    (i j : Fin n) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun x => (A x).adjugate i j) z := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply normalMatrix_det_contMDiffAt
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contMDiffAt_const
  · simp only [Matrix.updateRow_apply, ha, ite_false]
    exact hA a b

theorem normalMatrix_inv_contMDiffAt
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {z : EuclideanHalfSpace (n + 1)} {k : ℕ∞ω}
    (hA : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k A z)
    (hdet : (A z).det ≠ 0) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k
      (fun x => (A x)⁻¹) z := by
  have he : ∀ i j, ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun x => A x i j) z :=
    fun i j => contMDiffAt_pi_module_iff.mp (contMDiffAt_pi_module_iff.mp hA i) j
  apply contMDiffAt_pi_module_iff.mpr
  intro i
  apply contMDiffAt_pi_module_iff.mpr
  intro j
  have h := ((normalMatrix_det_contMDiffAt he).inv₀ hdet).mul
    (normalMatrix_adjugate_contMDiffAt he i j)
  simpa only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Pi.mul_def] using h

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

def normalTangentialInverse (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (z : EuclideanHalfSpace (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  (normalTangentialGram g χ z)⁻¹

theorem normalTangentialInverse_posDef (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    (normalTangentialInverse g χ z).PosDef :=
  (normalTangentialGram_posDef g χ hz).inv

theorem normalTangentialGram_mul_inverse (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    normalTangentialGram g χ z * normalTangentialInverse g χ z = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (normalTangentialGram_posDef g χ hz).det_pos.ne')

theorem normalTangentialInverse_mul_gram (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    normalTangentialInverse g χ z * normalTangentialGram g χ z = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (normalTangentialGram_posDef g χ hz).det_pos.ne')

theorem normalTangentialInverse_contMDiffAt (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞
      (normalTangentialInverse g χ) z :=
  normalMatrix_inv_contMDiffAt (normalTangentialGram_contMDiffAt g χ hz)
    (normalTangentialGram_posDef g χ hz).det_pos.ne'

theorem normalTangentialInverse_analyticAt (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (U : TopologicalSpace.Opens M) (hg : MetricAnalyticOn g U)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (hU : χ z ∈ U) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω
      (normalTangentialInverse g χ) z :=
  normalMatrix_inv_contMDiffAt (normalTangentialGram_analyticAt g χ U hg hz hU)
    (normalTangentialGram_posDef g χ hz).det_pos.ne'
end ConformalPoisson

end RefPart_TangentialInverse

/- Interface support: NormalJets.lean, SHA256 308edf20d41bb4b7eb6734dcbcabcd1ff8d39112f8cd72b0ff70a60e1ee443aa -/
noncomputable section RefPart_NormalJets

/-! Native repeated inward derivatives, including at time zero. All locality
and regularity statements concern the relative half-space topology. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def normalDeriv (f : EuclideanHalfSpace (n + 1) → F)
    (z : EuclideanHalfSpace (n + 1)) : F :=
  mvfderiv (𝓡∂ (n + 1)) f z (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))

def normalJet : ℕ → (EuclideanHalfSpace (n + 1) → F) → EuclideanHalfSpace (n + 1) → F
  | 0, f => f
  | k + 1, f => normalDeriv (normalJet k f)

@[simp] theorem normalJet_zero (f : EuclideanHalfSpace (n + 1) → F) : normalJet 0 f = f := rfl
@[simp] theorem normalJet_succ (k : ℕ) (f : EuclideanHalfSpace (n + 1) → F) :
    normalJet (k + 1) f = normalDeriv (normalJet k f) := rfl

theorem normalJet_succ' (k : ℕ) (f : EuclideanHalfSpace (n + 1) → F) :
    normalJet (k + 1) f = normalJet k (normalDeriv f) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg normalDeriv ih

theorem normalDeriv_contMDiffAt
    {f : EuclideanHalfSpace (n + 1) → F} {z : EuclideanHalfSpace (n + 1)}
    {k m : ℕ∞ω} (hf : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, F) k f z)
    (hmk : m + 1 ≤ k) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, F) m (normalDeriv f) z := by
  have hd := hf.contMDiffAt_mvfderiv_apply
    (p := (⟨z, euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)⟩ :
      TangentBundle (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)))) hmk
  exact hd.comp z (contMDiffAt_halfSpace_constTangent _ z m)

theorem normalJet_contMDiffOn {f : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ f S) (k : ℕ) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ (normalJet k f) S := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro z hz
    exact (normalDeriv_contMDiffAt ((ih z hz).contMDiffAt (hS.mem_nhds hz))
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).contMDiffWithinAt

theorem normalDeriv_eq_of_eventuallyEq
    {f g : EuclideanHalfSpace (n + 1) → F} {z : EuclideanHalfSpace (n + 1)}
    (h : f =ᶠ[𝓝 z] g) : normalDeriv f z = normalDeriv g z := by
  have hv := h.mfderiv_eq (I := 𝓡∂ (n + 1)) (I' := 𝓘(ℝ, F))
  have hv' := congrArg (fun A => A (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))) hv
  have hv'' := congrArg (NormedSpace.fromTangentSpace (f z)) hv'
  simpa [normalDeriv, mvfderiv, NormedSpace.fromTangentSpace, tangentSpaceCastModel, tangentSpaceCast] using hv'' 

theorem normalJet_eqOn {f g : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S) (h : EqOn f g S) (k : ℕ) :
    EqOn (normalJet k f) (normalJet k g) S := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z hz
    exact normalDeriv_eq_of_eventuallyEq (Filter.eventuallyEq_of_mem (hS.mem_nhds hz) ih)

@[simp] theorem normalDeriv_const (c : F) :
    normalDeriv (fun _ : EuclideanHalfSpace (n + 1) => c) = 0 := by
  funext z
  simp only [normalDeriv, mvfderiv_const, zero_apply, Pi.zero_apply]

@[simp] theorem normalJet_const_succ (k : ℕ) (c : F) :
    normalJet (k + 1) (fun _ : EuclideanHalfSpace (n + 1) => c) = 0 := by
  induction k with
  | zero => exact normalDeriv_const c
  | succ k ih => rw [normalJet_succ, ih]; exact normalDeriv_const 0
end ConformalPoisson

end RefPart_NormalJets

/- Interface support: NormalJetAlgebra.lean, SHA256 d24e817d06fc7b5986639a997e67e5eda335eec479145adc49dd9284c5017337 -/
noncomputable section RefPart_NormalJetAlgebra

/-! Local algebra of the actual native normal derivatives. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalDeriv_add {f g : EuclideanHalfSpace (n + 1) → F}
    {z : EuclideanHalfSpace (n + 1)}
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F) f z)
    (hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F) g z) :
    normalDeriv (f + g) z = normalDeriv f z + normalDeriv g z := by
  exact congrArg (fun A => A (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
    (mvfderiv_add hf hg)

theorem normalDeriv_smul {f : EuclideanHalfSpace (n + 1) → ℝ}
    {g : EuclideanHalfSpace (n + 1) → F} {z : EuclideanHalfSpace (n + 1)}
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f z)
    (hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F) g z) :
    normalDeriv (f • g) z = f z • normalDeriv g z + normalDeriv f z • g z := by
  have h := congrArg (fun A => A (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
    (mvfderiv_smul hf hg)
  simpa only [normalDeriv, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using h

theorem normalDeriv_mul {f g : EuclideanHalfSpace (n + 1) → ℝ}
    {z : EuclideanHalfSpace (n + 1)}
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f z)
    (hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) g z) :
    normalDeriv (f * g) z = normalDeriv f z * g z + f z * normalDeriv g z := by
  have h := normalDeriv_smul hf hg
  simpa only [smul_eq_mul] using h.trans (add_comm _ _)

theorem normalJet_add_eqOn {f g : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (f + g)) (normalJet k f + normalJet k g) S := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
    intro z hz
    have he := normalDeriv_eq_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hS.mem_nhds hz) ih)
    have hfk := ((normalJet_contMDiffOn hS hf k z hz).contMDiffAt
      (hS.mem_nhds hz)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
    have hgk := ((normalJet_contMDiffOn hS hg k z hz).contMDiffAt
      (hS.mem_nhds hz)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
    exact he.trans (normalDeriv_add hfk hgk)

theorem normalDeriv_const_smul (r : ℝ) (f : EuclideanHalfSpace (n + 1) → F)
    (z : EuclideanHalfSpace (n + 1)) :
    normalDeriv (r • f) z = r • normalDeriv f z := by
  have h := congrArg (fun A => A (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)))
    (mvfderiv_const_smul_field (I := 𝓡∂ (n + 1)) f z r)
  exact h

theorem normalJet_const_smul (r : ℝ) (f : EuclideanHalfSpace (n + 1) → F) (k : ℕ) :
    normalJet k (r • f) = r • normalJet k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [normalJet_succ, ih]
    funext z
    exact normalDeriv_const_smul r (normalJet k f) z
end ConformalPoisson

end RefPart_NormalJetAlgebra

/- Interface support: NormalJetLeibniz.lean, SHA256 7ca5cbe69fd68f557b1b5a9045e470e274d6aef63c387a51561fb481d72b0898 -/
noncomputable section RefPart_NormalJetLeibniz

/-! The binomial product rule for native normal jets on one relative-open
domain. The induction follows the standard Leibniz argument also used in
mathlib's IteratedDeriv/Lemmas.lean; no boundary extension is chosen. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace ConformalPoisson
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalJet_binomial_step (a : ℕ → ℝ) (b : ℕ → F) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), k.choose i • a i • b (k - i + 1)) +
      (∑ i ∈ Finset.range (k + 1), k.choose i • a (i + 1) • b (k - i)) =
    ∑ i ∈ Finset.range (k + 2), (k + 1).choose i • a i • b (k + 1 - i) := by
  have hleft : (∑ i ∈ Finset.range (k + 1), k.choose i • a i • b (k - i + 1)) =
      (∑ i ∈ Finset.range k, k.choose (i + 1) • a (i + 1) • b (k - i)) + a 0 • b (k + 1) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have he : k - (i + 1) + 1 = k - i := by omega
      rw [he]
    · simp
  have hright : (∑ i ∈ Finset.range (k + 2), (k + 1).choose i • a i • b (k + 1 - i)) =
      (∑ i ∈ Finset.range (k + 1), k.choose i • a (i + 1) • b (k - i)) +
      (∑ i ∈ Finset.range k, k.choose (i + 1) • a (i + 1) • b (k - i)) + a 0 • b (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, add_smul,
      Finset.sum_add_distrib, Nat.choose_zero_right, one_smul, Nat.sub_zero]
    rw [Finset.sum_range_succ (fun i => k.choose (i + 1) • a (i + 1) • b (k - i))]
    simp
  rw [hleft, hright]
  abel

variable {n : ℕ}

theorem normalJet_smul_eqOn
    {f : EuclideanHalfSpace (n + 1) → ℝ} {g : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (f • g))
      (fun z => ∑ i ∈ Finset.range (k + 1),
        k.choose i • normalJet i f z • normalJet (k - i) g z) S := by
  induction k generalizing f g with
  | zero => intro z hz; simp [normalJet, Pi.smul_apply']
  | succ k ih =>
    have hNf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (normalDeriv f) S :=
      normalJet_contMDiffOn hS hf 1
    have hNg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ (normalDeriv g) S :=
      normalJet_contMDiffOn hS hg 1
    have hproduct : EqOn (normalDeriv (f • g))
        (f • normalDeriv g + normalDeriv f • g) S := by
      intro z hz
      exact normalDeriv_smul
        (((hf z hz).contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by decide))
        (((hg z hz).contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by decide))
    intro z hz
    have he := normalJet_eqOn hS hproduct k hz
    have ha := normalJet_add_eqOn hS (hf.smul hNg) (hNf.smul hg) k hz
    have hfirst := ih hf hNg hz
    have hsecond := ih hNf hg hz
    simp_rw [← normalJet_succ'] at hfirst hsecond
    rw [normalJet_succ']
    exact he.trans (ha.trans ((congrArg₂ (· + ·) hfirst hsecond).trans
      (normalJet_binomial_step (fun j => normalJet j f z) (fun j => normalJet j g z) k)))

theorem normalJet_mul_eqOn
    {f g : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (f * g))
      (fun z => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * normalJet i f z * normalJet (k - i) g z) S := by
  simpa only [smul_eq_mul, nsmul_eq_mul, mul_assoc] using normalJet_smul_eqOn hS hf hg k
end ConformalPoisson

end RefPart_NormalJetLeibniz

/- Interface support: NormalJetLinearMaps.lean, SHA256 8cc8e79aa96e8f5b4183d0502a9ecdb67bcda0102cbbfba1c2d993c8c655d22e -/
noncomputable section RefPart_NormalJetLinearMaps

/-! Continuous linear readings commute with native normal jets. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem normalJet_clm_eqOn (L : F →L[ℝ] F')
    {f : EuclideanHalfSpace (n + 1) → F} {S : Set (EuclideanHalfSpace (n + 1))}
    (hS : IsOpen S) (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ f S) (k : ℕ) :
    EqOn (normalJet k (L ∘ f)) (L ∘ normalJet k f) S := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
    intro z hz
    have he := normalDeriv_eq_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hS.mem_nhds hz) ih)
    have hfk := ((normalJet_contMDiffOn hS hf k z hz).contMDiffAt
      (hS.mem_nhds hz)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
    exact he.trans (L.mvfderiv_comp_apply hfk _)

theorem normalJet_finsetSum_eqOn {ι : Type*} (t : Finset ι)
    (f : ι → EuclideanHalfSpace (n + 1) → F)
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ∀ i ∈ t, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ (f i) S) (k : ℕ) :
    EqOn (normalJet k (∑ i ∈ t, f i)) (∑ i ∈ t, normalJet k (f i)) S := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro z hz
    cases k with
    | zero => rfl
    | succ k =>
      change normalJet (k + 1) (fun _ : EuclideanHalfSpace (n + 1) => (0 : F)) z = 0
      rw [normalJet_const_succ]; rfl
  | @insert i t hi ih =>
    have hfi := hf i (Finset.mem_insert_self i t)
    have hft : ∀ j ∈ t, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ (f j) S :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hs : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ (∑ j ∈ t, f j) S := by
      have hfun : (fun x => ∑ j ∈ t, f j x) = ∑ j ∈ t, f j := by
        funext x
        simp only [Finset.sum_apply]
      rw [← hfun]
      exact contMDiffOn_finsetSum hft
    intro z hz
    simp only [Finset.sum_insert hi]
    exact (normalJet_add_eqOn hS hfi hs k hz).trans
      (congrArg (fun v => normalJet k (f i) z + v) (ih hft hz))

def normalMatrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → ℝ))

theorem normalJet_matrix_entry
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ A S)
    (k : ℕ) (i j : Fin n) :
    EqOn (normalJet k (fun z => A z i j)) (fun z => normalJet k A z i j) S :=
  normalJet_clm_eqOn (normalMatrixEntry i j) hS hA k
end ConformalPoisson

end RefPart_NormalJetLinearMaps

/- Interface support: MetricJetTrace.lean, SHA256 ca8d42b2eec52ea4d03ef00393e7f121580051bb6f5fac7ce3f3ad58086140d7 -/
noncomputable section RefPart_MetricJetTrace

/-! The trace algebra which makes the pure-metric normal recursion invertible
in boundary dimension at least two. -/

open TauCeti
open scoped BigOperators Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

def metricJetTrace (G D : Matrix (Fin n) (Fin n) ℝ) : ℝ := Matrix.trace (G * D)

def metricJetProjection (G A D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D - metricJetTrace G D • A

theorem metricJetTrace_projection (G A D : Matrix (Fin n) (Fin n) ℝ)
    (hGA : G * A = 1) :
    metricJetTrace G (metricJetProjection G A D) = (1 - (n : ℝ)) * metricJetTrace G D := by
  simp only [metricJetTrace, metricJetProjection, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, hGA, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

theorem metricJetProjection_injective (G A : Matrix (Fin n) (Fin n) ℝ)
    (hGA : G * A = 1) (hn : 2 ≤ n) : Function.Injective (metricJetProjection G A) := by
  intro D₁ D₂ hD
  have ht := congrArg (metricJetTrace G) hD
  rw [metricJetTrace_projection G A D₁ hGA, metricJetTrace_projection G A D₂ hGA] at ht
  have hn' : (1 : ℝ) - n ≠ 0 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he := mul_left_cancel₀ hn' ht
  unfold metricJetProjection at hD
  rw [he] at hD
  exact sub_left_inj.mp hD

theorem normalTangential_trace_inverse
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ω M]
    (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) :
    metricJetTrace (normalTangentialGram g χ z) (normalTangentialInverse g χ z) = n := by
  rw [metricJetTrace, normalTangentialGram_mul_inverse g χ hz, Matrix.trace_one]
  simp
end ConformalPoisson

end RefPart_MetricJetTrace

/- Interface support: NormalMatrixProduct.lean, SHA256 46b31800ddd918a5c0ca720a97c04804ee3837f597ff4ed9a3870b10219f249c -/
noncomputable section RefPart_NormalMatrixProduct

/-! The actual matrix product satisfies the native normal-jet product rule. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalMatrix_entry_contMDiffOn
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} {k : ℕ∞ω}
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k A S)
    (i j : Fin n) : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun z => A z i j) S :=
  contMDiffOn_pi_module_iff.mp (contMDiffOn_pi_module_iff.mp hA i) j

theorem normalMatrix_mul_contMDiffOn
    {A B : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} {k : ℕ∞ω}
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k A S)
    (hB : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k B S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k (fun z => A z * B z) S := by
  apply contMDiffOn_pi_module_iff.mpr
  intro i
  apply contMDiffOn_pi_module_iff.mpr
  intro j
  change ContMDiffOn _ _ k (fun z => ∑ m, A z i m * B z m j) S
  exact contMDiffOn_finsetSum fun m _ =>
    (normalMatrix_entry_contMDiffOn hA i m).mul (normalMatrix_entry_contMDiffOn hB m j)

theorem normalJet_matrix_mul
    {A B : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ A S)
    (hB : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ B S)
    (k : ℕ) {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalJet k (fun y => A y * B y) z = ∑ r ∈ Finset.range (k + 1),
      (k.choose r : ℝ) • (normalJet r A z * normalJet (k - r) B z) := by
  ext i j
  have hAB := normalMatrix_mul_contMDiffOn hA hB
  have hfun : (fun y => (A y * B y) i j) =
      ∑ m : Fin n, (fun y => A y i m * B y m j) := by
    funext y
    simp only [Matrix.mul_apply, Finset.sum_apply]
  have hsum := normalJet_finsetSum_eqOn Finset.univ
    (fun m y => A y i m * B y m j) hS
    (fun m _ => (normalMatrix_entry_contMDiffOn hA i m).mul
      (normalMatrix_entry_contMDiffOn hB m j)) k hz
  calc
    normalJet k (fun y => A y * B y) z i j =
        ∑ m : Fin n, normalJet k (fun y => A y i m * B y m j) z := by
      have hentry := (normalJet_matrix_entry hS hAB k i j hz).symm
      refine hentry.trans ?_
      rw [hfun]
      simpa only [Finset.sum_apply] using hsum
    _ = ∑ m : Fin n, ∑ r ∈ Finset.range (k + 1),
        (k.choose r : ℝ) * normalJet r A z i m * normalJet (k - r) B z m j := by
      apply Finset.sum_congr rfl
      intro m hm
      have hp := normalJet_mul_eqOn hS (normalMatrix_entry_contMDiffOn hA i m)
        (normalMatrix_entry_contMDiffOn hB m j) k hz
      refine hp.trans ?_
      apply Finset.sum_congr rfl
      intro r hr
      rw [normalJet_matrix_entry hS hA r i m hz,
        normalJet_matrix_entry hS hB (k - r) m j hz]
    _ = (∑ r ∈ Finset.range (k + 1),
        (k.choose r : ℝ) • (normalJet r A z * normalJet (k - r) B z)) i j := by
      rw [Finset.sum_comm]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Finset.mul_sum, mul_assoc]
end ConformalPoisson

end RefPart_NormalMatrixProduct

/- Interface support: UnitJetSequences.lean, SHA256 352a83a8e848004793cb62c980bb8495ad702288079f93b8f1464461784065a3 -/
noncomputable section RefPart_UnitJetSequences

/-! Common algebra of differentiated unit products. The native matrix and
scalar reciprocal callers supply the actual Leibniz and unit identities. -/

open scoped BigOperators
namespace ConformalPoisson
variable {R : Type*} [Ring R]

def jetLeibnizProduct (a b : ℕ → R) (k : ℕ) : R :=
  ∑ r ∈ Finset.range (k + 1), k.choose r • (a r * b (k - r))

theorem unitJetSequence_unique (G₁ A₁ G₂ A₂ : ℕ → R) (L : ℕ)
    (hGA₁ : G₁ 0 * A₁ 0 = 1) (hAG₂ : A₂ 0 * G₂ 0 = 1)
    (hA : ∀ r ≤ L, A₁ r = A₂ r)
    (hprod : ∀ r ≤ L, jetLeibnizProduct G₁ A₁ r = jetLeibnizProduct G₂ A₂ r) :
    ∀ r ≤ L, G₁ r = G₂ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hA0 := hA 0 (Nat.zero_le L)
    cases r with
    | zero =>
      calc
        G₁ 0 = G₁ 0 * (A₂ 0 * G₂ 0) := by rw [hAG₂, mul_one]
        _ = (G₁ 0 * A₁ 0) * G₂ 0 := by rw [hA0, mul_assoc]
        _ = G₂ 0 := by rw [hGA₁, one_mul]
    | succ k =>
      have hsums := hprod (k + 1) hr
      unfold jetLeibnizProduct at hsums
      rw [Finset.sum_range_succ (fun j => (k + 1).choose j • (G₁ j * A₁ (k + 1 - j))) (k + 1),
        Finset.sum_range_succ (fun j => (k + 1).choose j • (G₂ j * A₂ (k + 1 - j))) (k + 1)] at hsums
      have hlow : (∑ j ∈ Finset.range (k + 1), (k + 1).choose j • (G₁ j * A₁ (k + 1 - j))) =
          ∑ j ∈ Finset.range (k + 1), (k + 1).choose j • (G₂ j * A₂ (k + 1 - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < k + 1 := Finset.mem_range.mp hj
        rw [ih j hj' (by omega), hA (k + 1 - j) (by omega)]
      rw [hlow] at hsums
      have htop := add_left_cancel hsums
      simp only [Nat.choose_self, one_nsmul, Nat.sub_self] at htop
      rw [hA0] at htop
      have hc := congrArg (fun D : R => D * G₂ 0) htop
      simpa only [mul_assoc, hAG₂, mul_one] using hc
end ConformalPoisson

end RefPart_UnitJetSequences

/- Interface support: NormalInverseJets.lean, SHA256 4acdf7482b2da60e1f273ae640481106e0eadda0d816a5d308c5354e7d2ed606 -/
noncomputable section RefPart_NormalInverseJets

/-! Equal inverse-metric normal jets force equal metric normal jets, by the
actual differentiated matrix inverse identity on the common open domain. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_inverse_transfer
    {G₁ A₁ G₂ A₂ : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hG₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ G₁ S)
    (hA₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ A₁ S)
    (hG₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ G₂ S)
    (hA₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ A₂ S)
    (hGA₁ : EqOn (fun y => G₁ y * A₁ y) (fun _ => 1) S)
    (hGA₂ : EqOn (fun y => G₂ y * A₂ y) (fun _ => 1) S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S)
    (hAG₂ : A₂ z * G₂ z = 1) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r A₁ z = normalJet r A₂ z) :
    ∀ r ≤ L, normalJet r G₁ z = normalJet r G₂ z := by
  apply unitJetSequence_unique
    (fun r => normalJet r G₁ z) (fun r => normalJet r A₁ z)
    (fun r => normalJet r G₂ z) (fun r => normalJet r A₂ z) L
    (hGA₁ hz) hAG₂ hjets
  intro r hr
  have heq : EqOn (fun y => G₁ y * A₁ y) (fun y => G₂ y * A₂ y) S :=
    fun y hy => (hGA₁ hy).trans (hGA₂ hy).symm
  have h := normalJet_eqOn hS heq r hz
  rw [normalJet_matrix_mul hS hG₁ hA₁ r hz,
    normalJet_matrix_mul hS hG₂ hA₂ r hz] at h
  simpa only [jetLeibnizProduct, Nat.cast_smul_eq_nsmul] using h
end ConformalPoisson

end RefPart_NormalInverseJets

/- Interface support: NormalMetricFields.lean, SHA256 59fbd61b6e475f0dc3ce8f3cdb00757faad428f7389ab577b63002a4da51a1a1 -/
noncomputable section RefPart_NormalMetricFields

/-! A shared matrix-calculus interface, produced by the ACTUAL metric and
chart, for the boundary symbol recursion and its project jet induction. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

structure NormalMetricField (S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))) where
  gram : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ
  inverse : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ
  gram_smooth : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ gram S
  inverse_smooth : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ inverse S
  gram_posDef : ∀ z ∈ S, (gram z).PosDef
  inverse_posDef : ∀ z ∈ S, (inverse z).PosDef
  gram_inverse : EqOn (fun z => gram z * inverse z) (fun _ => 1) S
  inverse_gram : EqOn (fun z => inverse z * gram z) (fun _ => 1) S

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def fromChart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ω M]
    (g : Metric (n := n) (M := M))
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))) (hS : (S : Set _) ⊆ χ.source) :
    NormalMetricField S where
  gram := normalTangentialGram g χ
  inverse := normalTangentialInverse g χ
  gram_smooth := fun _ hz => (normalTangentialGram_contMDiffAt g χ (hS hz)).contMDiffWithinAt
  inverse_smooth := fun _ hz => (normalTangentialInverse_contMDiffAt g χ (hS hz)).contMDiffWithinAt
  gram_posDef := fun _ hz => normalTangentialGram_posDef g χ (hS hz)
  inverse_posDef := fun _ hz => normalTangentialInverse_posDef g χ (hS hz)
  gram_inverse := fun _ hz => normalTangentialGram_mul_inverse g χ (hS hz)
  inverse_gram := fun _ hz => normalTangentialInverse_mul_gram g χ (hS hz)

theorem inverse_jet_transfer (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r F₁.gram z = normalJet r F₂.gram z :=
  normalJet_inverse_transfer S.isOpen F₁.gram_smooth F₁.inverse_smooth
    F₂.gram_smooth F₂.inverse_smooth F₁.gram_inverse F₂.gram_inverse hz
    (F₂.inverse_gram hz) L hjets
end NormalMetricField
end ConformalPoisson

end RefPart_NormalMetricFields

/- Interface support: NormalMetricRecursion.lean, SHA256 dee74f78b79f6f274c19a6352df5a8cf739a66be2f0027c1e14ec98d070c7d8f -/
noncomputable section RefPart_NormalMetricRecursion

/-! Actual native trace, K and ell fields used by the local pure-metric
symbol recursion. Their smoothness and jet formulas are project proofs. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_sub_eqOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (f - g)) (normalJet k f - normalJet k g) S := by
  have he : f - g = f + (-1 : ℝ) • g := by ext z; simp [sub_eq_add_neg]
  rw [he]
  have hc : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞
      (fun _ : EuclideanHalfSpace (n + 1) => (-1 : ℝ)) S := contMDiffOn_const
  have h := normalJet_add_eqOn hS hf (hc.smul hg) k
  have hs : ((fun _ : EuclideanHalfSpace (n + 1) => (-1 : ℝ)) • g) = (-1 : ℝ) • g := by
    funext z
    rfl
  rw [hs, normalJet_const_smul] at h
  simpa only [neg_one_smul, sub_eq_add_neg] using h

def normalMatrixTrace : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def tau (F : NormalMetricField S) : EuclideanHalfSpace (n + 1) → ℝ :=
  fun z => metricJetTrace (F.gram z) (normalDeriv F.inverse z)

def K (F : NormalMetricField S) : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ :=
  normalDeriv F.inverse - F.tau • F.inverse

def ell (F : NormalMetricField S) : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ :=
  (1 / 4 : ℝ) • normalDeriv F.K

theorem normal_inverse_smooth (F : NormalMetricField S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ (normalDeriv F.inverse) S :=
  normalJet_contMDiffOn S.isOpen F.inverse_smooth 1

theorem tau_smooth (F : NormalMetricField S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ F.tau S := by
  have hprod := normalMatrix_mul_contMDiffOn F.gram_smooth F.normal_inverse_smooth
  have hL : ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) 𝓘(ℝ) ∞
      (normalMatrixTrace (n := n)) := (normalMatrixTrace (n := n)).contDiff.contMDiff
  exact hL.comp_contMDiffOn hprod

theorem K_smooth (F : NormalMetricField S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ F.K S :=
  F.normal_inverse_smooth.sub (F.tau_smooth.smul F.inverse_smooth)

theorem ell_smooth (F : NormalMetricField S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ F.ell S := by
  have hc : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞
      (fun _ : EuclideanHalfSpace (n + 1) => (1 / 4 : ℝ)) S := contMDiffOn_const
  exact hc.smul (normalJet_contMDiffOn S.isOpen F.K_smooth 1)

theorem normalJet_tau (F : NormalMetricField S) (k : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalJet k F.tau z = ∑ r ∈ Finset.range (k + 1),
      (k.choose r : ℝ) * metricJetTrace (normalJet r F.gram z)
        (normalJet (k - r + 1) F.inverse z) := by
  have hprod := normalMatrix_mul_contMDiffOn F.gram_smooth F.normal_inverse_smooth
  have ht := normalJet_clm_eqOn (normalMatrixTrace (n := n)) S.isOpen hprod k hz
  calc
    normalJet k F.tau z = normalMatrixTrace
        (normalJet k (fun y => F.gram y * normalDeriv F.inverse y) z) := ht
    _ = _ := by
      rw [normalJet_matrix_mul S.isOpen F.gram_smooth F.normal_inverse_smooth k hz]
      simp only [map_sum, map_smul, ← normalJet_succ', smul_eq_mul]
      rfl

theorem normalJet_K (F : NormalMetricField S) (k : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalJet k F.K z = normalJet (k + 1) F.inverse z -
      ∑ r ∈ Finset.range (k + 1),
        k.choose r • normalJet r F.tau z • normalJet (k - r) F.inverse z := by
  have hsub := normalJet_sub_eqOn S.isOpen F.normal_inverse_smooth
    (F.tau_smooth.smul F.inverse_smooth) k hz
  have hsmul := normalJet_smul_eqOn S.isOpen F.tau_smooth F.inverse_smooth k hz
  exact hsub.trans (congrArg₂ (· - ·) (congrFun (normalJet_succ' k F.inverse).symm z) hsmul)

theorem normalJet_ell (F : NormalMetricField S) (k : ℕ) :
    normalJet k F.ell = (1 / 4 : ℝ) • normalJet (k + 1) F.K := by
  unfold ell
  rw [normalJet_const_smul, ← normalJet_succ']
end NormalMetricField
end ConformalPoisson

end RefPart_NormalMetricRecursion

/- Interface support: NormalMetricJetStep.lean, SHA256 f143385679b709105d143821373970d7810f5d1cb75c266543a12179111ff569 -/
noncomputable section RefPart_NormalMetricJetStep

/-! Project algebra of the next normal metric jet. The symbol calculation's
open caller must supply the actual K jet; no boundary recovery is assumed. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def tauJetRemainder (F : NormalMetricField S) (L : ℕ) (z : EuclideanHalfSpace (n + 1)) : ℝ :=
  ∑ r ∈ Finset.range L, (L.choose (r + 1) : ℝ) *
    metricJetTrace (normalJet (r + 1) F.gram z) (normalJet (L - (r + 1) + 1) F.inverse z)

def KJetRemainder (F : NormalMetricField S) (L : ℕ) (z : EuclideanHalfSpace (n + 1)) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ r ∈ Finset.range L, L.choose r • normalJet r F.tau z • normalJet (L - r) F.inverse z

theorem normalJet_tau_leading (F : NormalMetricField S) (L : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalJet L F.tau z = F.tauJetRemainder L z +
      metricJetTrace (F.gram z) (normalJet (L + 1) F.inverse z) := by
  rw [F.normalJet_tau L hz, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, normalJet_zero]
  rfl

theorem normalJet_K_leading (F : NormalMetricField S) (L : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalJet L F.K z = metricJetProjection (F.gram z) (F.inverse z)
      (normalJet (L + 1) F.inverse z) -
      (F.KJetRemainder L z + F.tauJetRemainder L z • F.inverse z) := by
  rw [F.normalJet_K L hz, Finset.sum_range_succ]
  simp only [Nat.choose_self, one_smul, Nat.sub_self, normalJet_zero]
  rw [F.normalJet_tau_leading L hz]
  unfold metricJetProjection KJetRemainder
  simp only [add_smul]
  abel

theorem tau_jet_eq_of_inverse_jets (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z)
    (r : ℕ) (hr : r + 1 ≤ L) : normalJet r F₁.tau z = normalJet r F₂.tau z := by
  have hG := inverse_jet_transfer F₁ F₂ hz L hA
  rw [F₁.normalJet_tau r hz, F₂.normalJet_tau r hz]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < r + 1 := Finset.mem_range.mp hj
  rw [hG j (by omega), hA (r - j + 1) (by omega)]

theorem tauJetRemainder_eq_of_inverse_jets (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    F₁.tauJetRemainder L z = F₂.tauJetRemainder L z := by
  have hG := inverse_jet_transfer F₁ F₂ hz L hA
  unfold tauJetRemainder
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r < L := Finset.mem_range.mp hr
  rw [hG (r + 1) (by omega), hA (L - (r + 1) + 1) (by omega)]

theorem KJetRemainder_eq_of_inverse_jets (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    F₁.KJetRemainder L z = F₂.KJetRemainder L z := by
  unfold KJetRemainder
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r < L := Finset.mem_range.mp hr
  rw [tau_jet_eq_of_inverse_jets F₁ F₂ hz L hA r (by omega), hA (L - r) (by omega)]

theorem inverse_jet_step (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (hn : 2 ≤ n) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z)
    (hK : normalJet L F₁.K z = normalJet L F₂.K z) :
    normalJet (L + 1) F₁.inverse z = normalJet (L + 1) F₂.inverse z := by
  have hG := inverse_jet_transfer F₁ F₂ hz L hA
  have hG0 : F₁.gram z = F₂.gram z := hG 0 (Nat.zero_le L)
  have hA0 : F₁.inverse z = F₂.inverse z := hA 0 (Nat.zero_le L)
  rw [F₁.normalJet_K_leading L hz, F₂.normalJet_K_leading L hz,
    hG0, hA0, tauJetRemainder_eq_of_inverse_jets F₁ F₂ hz L hA,
    KJetRemainder_eq_of_inverse_jets F₁ F₂ hz L hA] at hK
  exact metricJetProjection_injective (F₂.gram z) (F₂.inverse z) (F₂.gram_inverse hz) hn
    (sub_left_inj.mp hK)
end ConformalPoisson.NormalMetricField

end RefPart_NormalMetricJetStep

/- Interface support: NormalMatrixSymmetry.lean, SHA256 05fb4ebf6de04965f6de23c8301c4c122a545efa331be5df096237b58c5eabbd -/
noncomputable section RefPart_NormalMatrixSymmetry

/-! Native jets preserve actual coefficient symmetry, and the trace
convention agrees with the manuscript's indexed contraction. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem metricJetTrace_eq_sum (G D : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) :
    metricJetTrace G D = ∑ i, ∑ j, G i j * D i j := by
  simp only [metricJetTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hG.apply i j]

theorem normalJet_matrix_symmetric
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ A S)
    (hs : ∀ z ∈ S, (A z).IsSymm) (k : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) : (normalJet k A z).IsSymm := by
  ext i j
  have heq : EqOn (fun y => A y j i) (fun y => A y i j) S :=
    fun y hy => (hs y hy).apply i j
  have hjets := normalJet_eqOn hS heq k hz
  exact ((normalJet_matrix_entry hS hA k j i hz).symm.trans hjets).trans
    (normalJet_matrix_entry hS hA k i j hz)

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

theorem inverse_normalJet_symmetric (F : NormalMetricField S) (k : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) : (normalJet k F.inverse z).IsSymm :=
  normalJet_matrix_symmetric S.isOpen F.inverse_smooth
    (fun y hy => (F.inverse_posDef y hy).isHermitian.isSymm) k hz

theorem K_symmetric (F : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) : (F.K z).IsSymm := by
  change (normalDeriv F.inverse z - F.tau z • F.inverse z).IsSymm
  exact (F.inverse_normalJet_symmetric 1 hz).sub
    ((F.inverse_posDef z hz).isHermitian.isSymm.smul (F.tau z))

theorem K_normalJet_symmetric (F : NormalMetricField S) (k : ℕ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) : (normalJet k F.K z).IsSymm :=
  normalJet_matrix_symmetric S.isOpen F.K_smooth (fun _ hy => F.K_symmetric hy) k hz

theorem tau_eq_indexed_contraction (F : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    F.tau z = ∑ i, ∑ j, F.gram z i j * normalDeriv F.inverse z i j :=
  metricJetTrace_eq_sum _ _ (F.gram_posDef z hz).isHermitian.isSymm
end NormalMetricField
end ConformalPoisson

end RefPart_NormalMatrixSymmetry

/- Interface support: NormalSymbolQuadratic.lean, SHA256 d559391ccdb72ff8ffff562c6ca1492396693b4c6b2b804cc829bf1c9b8fd98f -/
noncomputable section RefPart_NormalSymbolQuadratic

/-! Project polarization and principal-symbol algebra for the actual
tangential matrix coefficients. Frequencies are their real coordinate
covector components, in the same canonical basis defining the Gram matrix. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

def normalMatrixQuadratic (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ :=
  A.toBilin' ξ ξ

theorem normalMatrixQuadratic_eq_dot (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    normalMatrixQuadratic A ξ = dotProduct ξ (Matrix.mulVec A ξ) := Matrix.toBilin'_apply' A ξ ξ

theorem normalMatrixQuadratic_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (ξ : Fin n → ℝ) :
    normalMatrixQuadratic A (r • ξ) = r ^ 2 * normalMatrixQuadratic A ξ := by
  simp only [normalMatrixQuadratic, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem normalMatrix_eq_of_quadratic_eq (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hquad : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → normalMatrixQuadratic A ξ = normalMatrixQuadratic B ξ) :
    A = B := by
  have hq : ∀ ξ : Fin n → ℝ, A.toBilin' ξ ξ = B.toBilin' ξ ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ; simp
    · exact hquad ξ hξ
  have hsA := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  have hsB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hB
  apply Matrix.toBilin'.injective
  apply LinearMap.ext₂
  intro x y
  have hx := hq x
  have hy := hq y
  have hxy := hq (x + y)
  simp only [map_add, LinearMap.add_apply, hsA.eq x y, hsB.eq x y] at hxy
  rw [hsA.eq x y, hsB.eq x y]
  linarith

def normalPrincipal (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (normalMatrixQuadratic A ξ)

theorem normalPrincipal_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) : 0 < normalPrincipal A ξ := by
  apply Real.sqrt_pos.mpr
  rw [normalMatrixQuadratic_eq_dot]
  exact hA.dotProduct_mulVec_pos hξ

theorem normalPrincipal_sq (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) : (normalPrincipal A ξ) ^ 2 = normalMatrixQuadratic A ξ :=
  Real.sq_sqrt (by rw [normalMatrixQuadratic_eq_dot]; exact (hA.dotProduct_mulVec_pos hξ).le)

theorem normalMatrix_eq_of_principal_eq (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef)
    (hs : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → normalPrincipal A ξ = normalPrincipal B ξ) : A = B := by
  apply normalMatrix_eq_of_quadratic_eq A B hA.isHermitian.isSymm hB.isHermitian.isSymm
  intro ξ hξ
  rw [← normalPrincipal_sq A hA ξ hξ, ← normalPrincipal_sq B hB ξ hξ, hs ξ hξ]

def normalFrequency (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  (normalPrincipal A ξ)⁻¹ • ξ

theorem normalMatrix_eq_of_normalized_quadratic_eq
    (A C D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hC : C.IsSymm) (hD : D.IsSymm)
    (hq : ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
      normalMatrixQuadratic C (normalFrequency A ξ) = normalMatrixQuadratic D (normalFrequency A ξ)) :
    C = D := by
  apply normalMatrix_eq_of_quadratic_eq C D hC hD
  intro ξ hξ
  have h := hq ξ hξ
  change normalMatrixQuadratic C ((normalPrincipal A ξ)⁻¹ • ξ) =
    normalMatrixQuadratic D ((normalPrincipal A ξ)⁻¹ • ξ) at h
  rw [normalMatrixQuadratic_smul, normalMatrixQuadratic_smul] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero (normalPrincipal_pos A hA ξ hξ).ne')) h
end ConformalPoisson

end RefPart_NormalSymbolQuadratic

/- Interface support: NormalScalarInverseJets.lean, SHA256 f9f44496bf47bfd02eff064dcde1e8bea187d06f1b27b62a7473a11bde6f0263 -/
noncomputable section RefPart_NormalScalarInverseJets

/-! Scalar reciprocal jets use the SAME unit-product sequence argument as
the native matrix inverse jets; no second inversion induction is duplicated. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_scalar_inverse_transfer
    {G₁ A₁ G₂ A₂ : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hG₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ G₁ S)
    (hA₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ A₁ S)
    (hG₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ G₂ S)
    (hA₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ A₂ S)
    (hGA₁ : EqOn (G₁ * A₁) (fun _ => 1) S)
    (hGA₂ : EqOn (G₂ * A₂) (fun _ => 1) S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r A₁ z = normalJet r A₂ z) :
    ∀ r ≤ L, normalJet r G₁ z = normalJet r G₂ z := by
  have hAG₂ : A₂ z * G₂ z = 1 := by
    rw [mul_comm]
    exact hGA₂ hz
  apply unitJetSequence_unique
    (fun r => normalJet r G₁ z) (fun r => normalJet r A₁ z)
    (fun r => normalJet r G₂ z) (fun r => normalJet r A₂ z) L
    (hGA₁ hz) hAG₂ hjets
  intro r hr
  have heq : EqOn (G₁ * A₁) (G₂ * A₂) S :=
    fun y hy => (hGA₁ hy).trans (hGA₂ hy).symm
  have h := normalJet_eqOn hS heq r hz
  rw [normalJet_mul_eqOn hS hG₁ hA₁ r hz, normalJet_mul_eqOn hS hG₂ hA₂ r hz] at h
  simpa only [jetLeibnizProduct, nsmul_eq_mul, mul_assoc] using h

theorem normalJet_reciprocal_eq
    {f₁ f₂ : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₁ S)
    (hf₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₂ S)
    (hne₁ : ∀ y ∈ S, f₁ y ≠ 0) (hne₂ : ∀ y ∈ S, f₂ y ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r f₁ z = normalJet r f₂ z) :
    ∀ r ≤ L, normalJet r (fun y => (f₁ y)⁻¹) z = normalJet r (fun y => (f₂ y)⁻¹) z := by
  apply normalJet_scalar_inverse_transfer hS (hf₁.inv₀ hne₁) hf₁ (hf₂.inv₀ hne₂) hf₂
    (fun y hy => inv_mul_cancel₀ (hne₁ y hy))
    (fun y hy => inv_mul_cancel₀ (hne₂ y hy)) hz L hjets
end ConformalPoisson

end RefPart_NormalScalarInverseJets

/- Interface support: SquareJetSequences.lean, SHA256 7eea0b35bd3bf4ad3217c8deb1e1dbc9a425e517236a072167346991b13c612f -/
noncomputable section RefPart_SquareJetSequences

/-! The positive branch of a square determines all finite jets of its root.
The native caller supplies the actual scalar Leibniz identities. -/

open scoped BigOperators
namespace ConformalPoisson

theorem squareJetSequence_unique (a b : ℕ → ℝ) (L : ℕ)
    (ha : 0 < a 0) (hb : 0 < b 0)
    (hprod : ∀ r ≤ L, jetLeibnizProduct a a r = jetLeibnizProduct b b r) :
    ∀ r ≤ L, a r = b r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    cases r with
    | zero =>
      have h : a 0 * a 0 = b 0 * b 0 := by
        simpa [jetLeibnizProduct] using hprod 0 (Nat.zero_le L)
      nlinarith
    | succ k =>
      have hsplit (c : ℕ → ℝ) : jetLeibnizProduct c c (k + 1) =
          (∑ j ∈ Finset.range k, (k + 1).choose (j + 1) •
            (c (j + 1) * c (k + 1 - (j + 1)))) + c (k + 1) * c 0 + c 0 * c (k + 1) := by
        unfold jetLeibnizProduct
        rw [Finset.sum_range_succ']
        rw [Finset.sum_range_succ (fun j => (k + 1).choose (j + 1) •
          (c (j + 1) * c (k + 1 - (j + 1)))) k]
        simp only [Nat.choose_self, one_nsmul, Nat.sub_self, Nat.choose_zero_right, Nat.sub_zero]
      have h := hprod (k + 1) hr
      rw [hsplit a, hsplit b] at h
      have hlow : (∑ j ∈ Finset.range k, (k + 1).choose (j + 1) •
          (a (j + 1) * a (k + 1 - (j + 1)))) =
          ∑ j ∈ Finset.range k, (k + 1).choose (j + 1) •
          (b (j + 1) * b (k + 1 - (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < k := Finset.mem_range.mp hj
        rw [ih (j + 1) (by omega) (by omega), ih (k + 1 - (j + 1)) (by omega) (by omega)]
      have h0 := ih 0 (by omega) (Nat.zero_le L)
      rw [hlow, h0] at h
      have hfactor : (b 0 + b 0) * (a (k + 1) - b (k + 1)) = 0 := by nlinarith [h]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (by linarith))
end ConformalPoisson

end RefPart_SquareJetSequences

/- Interface support: NormalScalarSquareJets.lean, SHA256 e77f151889a9229fa4b902922440871e63a8f93fb2af4862bd715de040768247 -/
noncomputable section RefPart_NormalScalarSquareJets

/-! Actual native finite jets of the positive square root, using the
positive-branch sequence lemma and the actual native product rule. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_positive_square_transfer
    {f₁ f₂ : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₁ S)
    (hf₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₂ S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S)
    (hpos₁ : 0 < f₁ z) (hpos₂ : 0 < f₂ z) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r (f₁ * f₁) z = normalJet r (f₂ * f₂) z) :
    ∀ r ≤ L, normalJet r f₁ z = normalJet r f₂ z := by
  apply squareJetSequence_unique (fun r => normalJet r f₁ z) (fun r => normalJet r f₂ z)
    L hpos₁ hpos₂
  intro r hr
  have h := hjets r hr
  rw [normalJet_mul_eqOn hS hf₁ hf₁ r hz, normalJet_mul_eqOn hS hf₂ hf₂ r hz] at h
  simpa only [jetLeibnizProduct, nsmul_eq_mul, mul_assoc] using h

theorem normalJet_positive_root_eq
    {f₁ f₂ q₁ q₂ : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₁ S)
    (hf₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f₂ S)
    (hsq₁ : EqOn (f₁ * f₁) q₁ S) (hsq₂ : EqOn (f₂ * f₂) q₂ S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S)
    (hpos₁ : 0 < f₁ z) (hpos₂ : 0 < f₂ z) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r q₁ z = normalJet r q₂ z) :
    ∀ r ≤ L, normalJet r f₁ z = normalJet r f₂ z := by
  apply normalJet_positive_square_transfer hS hf₁ hf₂ hz hpos₁ hpos₂ L
  intro r hr
  exact (normalJet_eqOn hS hsq₁ r hz).trans
    ((hjets r hr).trans (normalJet_eqOn hS hsq₂ r hz).symm)

theorem normalJet_sqrt_eq
    {q₁ q₂ : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hq₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q₁ S)
    (hq₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q₂ S)
    (hpos₁ : ∀ y ∈ S, 0 < q₁ y) (hpos₂ : ∀ y ∈ S, 0 < q₂ y)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hjets : ∀ r ≤ L, normalJet r q₁ z = normalJet r q₂ z) :
    ∀ r ≤ L, normalJet r (fun y => Real.sqrt (q₁ y)) z =
      normalJet r (fun y => Real.sqrt (q₂ y)) z := by
  apply normalJet_positive_root_eq hS
    (hq₁.sqrt (fun y hy => (hpos₁ y hy).ne')) (hq₂.sqrt (fun y hy => (hpos₂ y hy).ne'))
    (fun y hy => Real.mul_self_sqrt (hpos₁ y hy).le)
    (fun y hy => Real.mul_self_sqrt (hpos₂ y hy).le) hz
    (Real.sqrt_pos.mpr (hpos₁ z hz)) (Real.sqrt_pos.mpr (hpos₂ z hz)) L hjets
end ConformalPoisson

end RefPart_NormalScalarSquareJets

/- Interface support: NormalPrincipalJets.lean, SHA256 b3d3d9ad84ae9dc32c8b398f7d004e81c8aec28846a49fd50273856474267cd8 -/
noncomputable section RefPart_NormalPrincipalJets

/-! Actual principal coefficient, positive root and reciprocal jets are
determined by the actual inverse-metric jets, for each nonzero frequency. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

def normalQuadraticRead (ξ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => normalMatrixQuadratic A ξ
     map_add' := by
       intro A B
       simp only [normalMatrixQuadratic, map_add, LinearMap.add_apply]
     map_smul' := by
       intro r A
       simp only [normalMatrixQuadratic, map_smul, LinearMap.smul_apply, smul_eq_mul,
         RingHom.id_apply] } : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem normalQuadraticRead_apply (ξ : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    normalQuadraticRead ξ A = normalMatrixQuadratic A ξ := rfl

theorem normalQuadratic_contMDiffOn (ξ : Fin n → ℝ)
    {A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} {k : ℕ∞ω}
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) k A S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) k (fun z => normalMatrixQuadratic (A z) ξ) S :=
  (normalQuadraticRead ξ).contDiff.contMDiff.comp_contMDiffOn hA

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def quadratic (F : NormalMetricField S) (ξ : Fin n → ℝ) : EuclideanHalfSpace (n + 1) → ℝ :=
  fun z => normalMatrixQuadratic (F.inverse z) ξ

def principal (F : NormalMetricField S) (ξ : Fin n → ℝ) : EuclideanHalfSpace (n + 1) → ℝ :=
  fun z => normalPrincipal (F.inverse z) ξ

def frequency (F : NormalMetricField S) (ξ : Fin n → ℝ) : EuclideanHalfSpace (n + 1) → (Fin n → ℝ) :=
  fun z => normalFrequency (F.inverse z) ξ

theorem quadratic_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (F.quadratic ξ) S :=
  normalQuadratic_contMDiffOn ξ F.inverse_smooth

theorem quadratic_pos (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ∀ z ∈ S, 0 < F.quadratic ξ z := by
  intro z hz
  rw [quadratic, normalMatrixQuadratic_eq_dot]
  exact (F.inverse_posDef z hz).dotProduct_mulVec_pos hξ

theorem principal_pos (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ∀ z ∈ S, 0 < F.principal ξ z :=
  fun z hz => normalPrincipal_pos _ (F.inverse_posDef z hz) ξ hξ

theorem principal_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (F.principal ξ) S :=
  (F.quadratic_smooth ξ).sqrt (fun z hz => (F.quadratic_pos ξ hξ z hz).ne')

theorem inverse_principal_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (fun z => (F.principal ξ z)⁻¹) S :=
  (F.principal_smooth ξ hξ).inv₀ (fun z hz => (F.principal_pos ξ hξ z hz).ne')

theorem quadratic_jets_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r (F₁.quadratic ξ) z = normalJet r (F₂.quadratic ξ) z := by
  intro r hr
  have h₁ := normalJet_clm_eqOn (normalQuadraticRead ξ) S.isOpen F₁.inverse_smooth r hz
  have h₂ := normalJet_clm_eqOn (normalQuadraticRead ξ) S.isOpen F₂.inverse_smooth r hz
  exact h₁.trans ((congrArg (normalQuadraticRead ξ) (hA r hr)).trans h₂.symm)

theorem principal_jets_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r (F₁.principal ξ) z = normalJet r (F₂.principal ξ) z :=
  normalJet_sqrt_eq S.isOpen (F₁.quadratic_smooth ξ) (F₂.quadratic_smooth ξ)
    (F₁.quadratic_pos ξ hξ) (F₂.quadratic_pos ξ hξ) hz L
    (quadratic_jets_eq F₁ F₂ hz ξ L hA)

theorem inverse_principal_jets_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r (fun y => (F₁.principal ξ y)⁻¹) z =
      normalJet r (fun y => (F₂.principal ξ y)⁻¹) z :=
  normalJet_reciprocal_eq S.isOpen (F₁.principal_smooth ξ hξ) (F₂.principal_smooth ξ hξ)
    (fun y hy => (F₁.principal_pos ξ hξ y hy).ne') (fun y hy => (F₂.principal_pos ξ hξ y hy).ne')
    hz L (principal_jets_eq F₁ F₂ hz ξ hξ L hA)

theorem frequency_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ (F.frequency ξ) S := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight ξ
  exact L.contDiff.contMDiff.comp_contMDiffOn (F.inverse_principal_smooth ξ hξ)

theorem frequency_jets_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r (F₁.frequency ξ) z = normalJet r (F₂.frequency ξ) z := by
  let B : ℝ →L[ℝ] (Fin n → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight ξ
  intro r hr
  have h₁ := normalJet_clm_eqOn B S.isOpen (F₁.inverse_principal_smooth ξ hξ) r hz
  have h₂ := normalJet_clm_eqOn B S.isOpen (F₂.inverse_principal_smooth ξ hξ) r hz
  have hi := inverse_principal_jets_eq F₁ F₂ hz ξ hξ L hA r hr
  exact h₁.trans ((congrArg B hi).trans h₂.symm)

theorem principal_analyticOn (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω F.inverse S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω (F.principal ξ) S :=
  (normalQuadratic_contMDiffOn ξ hA).sqrt (fun z hz => (F.quadratic_pos ξ hξ z hz).ne')

theorem inverse_principal_analyticOn (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω F.inverse S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω (fun z => (F.principal ξ z)⁻¹) S :=
  (F.principal_analyticOn ξ hξ hA).inv₀ (fun z hz => (F.principal_pos ξ hξ z hz).ne')

theorem frequency_analyticOn (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (hA : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω F.inverse S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ω (F.frequency ξ) S := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight ξ
  exact L.contDiff.contMDiff.comp_contMDiffOn (F.inverse_principal_analyticOn ξ hξ hA)
end NormalMetricField
end ConformalPoisson

end RefPart_NormalPrincipalJets

/- Interface support: NormalBilinearJets.lean, SHA256 ea27a06783614c92214784f713a7cb6b691e8a9cf9904dd219a84466be56b4ec -/
noncomputable section RefPart_NormalBilinearJets

/-! Native normal jets of arbitrary continuous real bilinear pairings.
In particular, this covers multiplication of COMPLEX symbol functions. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

theorem normalBilinear_contMDiffOn (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {f : EuclideanHalfSpace (n + 1) → F₁} {g : EuclideanHalfSpace (n + 1) → F₂}
    {S : Set (EuclideanHalfSpace (n + 1))} {k : ℕ∞ω}
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) k f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) k g S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₃) k (fun z => B (f z) (g z)) S :=
  (B.contDiff.contMDiff.comp_contMDiffOn hf).clm_apply hg

theorem normalDeriv_bilinear (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {f : EuclideanHalfSpace (n + 1) → F₁} {g : EuclideanHalfSpace (n + 1) → F₂}
    {z : EuclideanHalfSpace (n + 1)}
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) f z)
    (hg : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) g z) :
    normalDeriv (fun y => B (f y) (g y)) z =
      B (f z) (normalDeriv g z) + B (normalDeriv f z) (g z) := by
  have hA : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, F₂ →L[ℝ] F₃) (fun y => B (f y)) z :=
    B.differentiableAt.mdifferentiableAt.comp z hf
  have h := mvfderiv_clm_apply hA hg (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
  have hB : mvfderiv (𝓡∂ (n + 1)) (fun y => B (f y)) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) = B (normalDeriv f z) :=
    B.mvfderiv_comp_apply hf _
  rw [hB] at h
  exact h.trans (add_comm _ _)

omit [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℝ F₃] in
theorem normalBilinear_binomial_step (B : F₁ → F₂ → F₃) (a : ℕ → F₁) (b : ℕ → F₂) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), k.choose i • B (a i) (b (k - i + 1))) +
      (∑ i ∈ Finset.range (k + 1), k.choose i • B (a (i + 1)) (b (k - i))) =
    ∑ i ∈ Finset.range (k + 2), (k + 1).choose i • B (a i) (b (k + 1 - i)) := by
  have hleft : (∑ i ∈ Finset.range (k + 1), k.choose i • B (a i) (b (k - i + 1))) =
      (∑ i ∈ Finset.range k, k.choose (i + 1) • B (a (i + 1)) (b (k - i))) + B (a 0) (b (k + 1)) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have he : k - (i + 1) + 1 = k - i := by omega
      rw [he]
    · simp
  have hright : (∑ i ∈ Finset.range (k + 2), (k + 1).choose i • B (a i) (b (k + 1 - i))) =
      (∑ i ∈ Finset.range (k + 1), k.choose i • B (a (i + 1)) (b (k - i))) +
      (∑ i ∈ Finset.range k, k.choose (i + 1) • B (a (i + 1)) (b (k - i))) + B (a 0) (b (k + 1)) := by
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, add_nsmul,
      Finset.sum_add_distrib, Nat.choose_zero_right, one_nsmul, Nat.sub_zero]
    rw [Finset.sum_range_succ (fun i => k.choose (i + 1) • B (a (i + 1)) (b (k - i)))]
    simp
  rw [hleft, hright]
  abel

theorem normalJet_bilinear_eqOn (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    {f : EuclideanHalfSpace (n + 1) → F₁} {g : EuclideanHalfSpace (n + 1) → F₂}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (fun z => B (f z) (g z)))
      (fun z => ∑ i ∈ Finset.range (k + 1), k.choose i • B (normalJet i f z) (normalJet (k - i) g z)) S := by
  induction k generalizing f g with
  | zero => intro z hz; simp [normalJet]
  | succ k ih =>
    have hNf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) ∞ (normalDeriv f) S :=
      normalJet_contMDiffOn hS hf 1
    have hNg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) ∞ (normalDeriv g) S :=
      normalJet_contMDiffOn hS hg 1
    have hp : EqOn (normalDeriv (fun y => B (f y) (g y)))
        ((fun y => B (f y) (normalDeriv g y)) + (fun y => B (normalDeriv f y) (g y))) S := by
      intro z hz
      exact normalDeriv_bilinear B
        (((hf z hz).contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by decide))
        (((hg z hz).contMDiffAt (hS.mem_nhds hz)).mdifferentiableAt (by decide))
    intro z hz
    have he := normalJet_eqOn hS hp k hz
    have ha := normalJet_add_eqOn hS (normalBilinear_contMDiffOn B hf hNg)
      (normalBilinear_contMDiffOn B hNf hg) k hz
    have hfirst := ih hf hNg hz
    have hsecond := ih hNf hg hz
    simp_rw [← normalJet_succ'] at hfirst hsecond
    rw [normalJet_succ']
    exact he.trans (ha.trans ((congrArg₂ (· + ·) hfirst hsecond).trans
      (normalBilinear_binomial_step (fun u v => B u v)
        (fun j => normalJet j f z) (fun j => normalJet j g z) k)))
end ConformalPoisson

end RefPart_NormalBilinearJets

/- Interface support: NormalBilinearJetComparison.lean, SHA256 906497e7c219e0fb1f749bdcace14b2ed3727574766194888c5dafb34f30a535 -/
noncomputable section RefPart_NormalBilinearJetComparison

/-! The precise finite jet dependencies of a bilinear pairing, including
isolation of its highest first-factor jet. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {f₁ f₂ : EuclideanHalfSpace (n + 1) → F₁}
  {g₁ g₂ : EuclideanHalfSpace (n + 1) → F₂}
  {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
  (hf₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) ∞ f₁ S)
  (hf₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₁) ∞ f₂ S)
  (hg₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) ∞ g₁ S)
  (hg₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F₂) ∞ g₂ S)
  (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
  {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S)

include hS hf₁ hf₂ hg₁ hg₂ hz

theorem normalJet_bilinear_congr (L : ℕ)
    (hf : ∀ r ≤ L, normalJet r f₁ z = normalJet r f₂ z)
    (hg : ∀ r ≤ L, normalJet r g₁ z = normalJet r g₂ z) :
    normalJet L (fun y => B (f₁ y) (g₁ y)) z =
      normalJet L (fun y => B (f₂ y) (g₂ y)) z := by
  rw [normalJet_bilinear_eqOn B hS hf₁ hg₁ L hz,
    normalJet_bilinear_eqOn B hS hf₂ hg₂ L hz]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r < L + 1 := Finset.mem_range.mp hr
  rw [hf r (by omega), hg (L - r) (by omega)]

theorem normalJet_bilinear_top_eq (L : ℕ)
    (hf : ∀ r < L, normalJet r f₁ z = normalJet r f₂ z)
    (hg : ∀ r ≤ L, normalJet r g₁ z = normalJet r g₂ z)
    (hproduct : normalJet L (fun y => B (f₁ y) (g₁ y)) z =
      normalJet L (fun y => B (f₂ y) (g₂ y)) z) :
    B (normalJet L f₁ z) (g₁ z) = B (normalJet L f₂ z) (g₁ z) := by
  rw [normalJet_bilinear_eqOn B hS hf₁ hg₁ L hz,
    normalJet_bilinear_eqOn B hS hf₂ hg₂ L hz] at hproduct
  dsimp only at hproduct
  rw [Finset.sum_range_succ (fun r => L.choose r • B (normalJet r f₁ z) (normalJet (L - r) g₁ z)) L,
    Finset.sum_range_succ (fun r => L.choose r • B (normalJet r f₂ z) (normalJet (L - r) g₂ z)) L] at hproduct
  have hlow : (∑ r ∈ Finset.range L, L.choose r • B (normalJet r f₁ z) (normalJet (L - r) g₁ z)) =
      ∑ r ∈ Finset.range L, L.choose r • B (normalJet r f₂ z) (normalJet (L - r) g₂ z) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < L := Finset.mem_range.mp hr
    rw [hf r hr', hg (L - r) (by omega)]
  rw [hlow] at hproduct
  have htop := add_left_cancel hproduct
  simp only [Nat.choose_self, one_nsmul, Nat.sub_self, normalJet_zero] at htop
  have hg0 : g₁ z = g₂ z := hg 0 (Nat.zero_le L)
  exact htop.trans (congrArg (B (normalJet L f₂ z)) hg0.symm)
end ConformalPoisson

end RefPart_NormalBilinearJetComparison

/- Interface support: NormalCoordinatePairings.lean, SHA256 0bffeb7707cc622d9bc6f0079d7ddcd58edde09d43f833d0826a32a7a7f3d24b -/
noncomputable section RefPart_NormalCoordinatePairings

/-! Canonical finite-dimensional bilinear interfaces for the actual
coordinate matrix action and covector quadratic evaluation. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson

def finiteBilinearToContinuous
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap.comp B).toContinuousLinearMap

@[simp] theorem finiteBilinearToContinuous_apply
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (x : E) (y : F) : finiteBilinearToContinuous B x y = B x y := rfl

variable {n : ℕ}

def normalMatrixAction : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  finiteBilinearToContinuous (Matrix.mulVecBilin ℝ ℝ)

@[simp] theorem normalMatrixAction_apply (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    normalMatrixAction A v = Matrix.mulVec A v := rfl

def normalCoordinateDot : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  finiteBilinearToContinuous (dotProductBilin ℝ ℝ)

@[simp] theorem normalCoordinateDot_apply (u v : Fin n → ℝ) :
    normalCoordinateDot u v = dotProduct u v := rfl

def normalMatrixPairedAction (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (Fin n → ℝ) ℝ (normalCoordinateDot w)).comp normalMatrixAction

@[simp] theorem normalMatrixPairedAction_apply (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    normalMatrixPairedAction w A v = dotProduct w (Matrix.mulVec A v) := rfl

theorem normalQuadratic_eq_pairing (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    normalMatrixQuadratic A v = normalCoordinateDot.flip (normalMatrixAction A v) v :=
  normalMatrixQuadratic_eq_dot A v
end ConformalPoisson

end RefPart_NormalCoordinatePairings

/- Interface support: NormalQuadraticJetComparison.lean, SHA256 0370c5304eb3cb89efd72559acd2ee62d50a1896390ecd9c5d0fde86c57411ba -/
noncomputable section RefPart_NormalQuadraticJetComparison

/-! Isolate the highest matrix jet inside the ACTUAL variable-frequency
quadratic expression using two bilinear highest-jet comparisons. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_quadratic_top_eq
    {K₁ K₂ : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ}
    {w₁ w₂ : EuclideanHalfSpace (n + 1) → (Fin n → ℝ)}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hK₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ K₁ S)
    (hK₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞ K₂ S)
    (hw₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ w₁ S)
    (hw₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ w₂ S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hK : ∀ r < L, normalJet r K₁ z = normalJet r K₂ z)
    (hw : ∀ r ≤ L, normalJet r w₁ z = normalJet r w₂ z)
    (hq : normalJet L (fun y => normalMatrixQuadratic (K₁ y) (w₁ y)) z =
      normalJet L (fun y => normalMatrixQuadratic (K₂ y) (w₂ y)) z) :
    normalMatrixQuadratic (normalJet L K₁ z) (w₁ z) =
      normalMatrixQuadratic (normalJet L K₂ z) (w₁ z) := by
  let V₁ : EuclideanHalfSpace (n + 1) → (Fin n → ℝ) := fun y => normalMatrixAction (K₁ y) (w₁ y)
  let V₂ : EuclideanHalfSpace (n + 1) → (Fin n → ℝ) := fun y => normalMatrixAction (K₂ y) (w₂ y)
  have hV₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ V₁ S :=
    normalBilinear_contMDiffOn normalMatrixAction hK₁ hw₁
  have hV₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, Fin n → ℝ) ∞ V₂ S :=
    normalBilinear_contMDiffOn normalMatrixAction hK₂ hw₂
  have hV : ∀ r < L, normalJet r V₁ z = normalJet r V₂ z := by
    intro r hr
    exact normalJet_bilinear_congr hS hK₁ hK₂ hw₁ hw₂ normalMatrixAction hz r
      (fun j hj => hK j (by omega)) (fun j hj => hw j (by omega))
  have hfun₁ : (fun y => normalMatrixQuadratic (K₁ y) (w₁ y)) =
      (fun y => normalCoordinateDot.flip (V₁ y) (w₁ y)) := by
    funext y
    exact normalQuadratic_eq_pairing (K₁ y) (w₁ y)
  have hfun₂ : (fun y => normalMatrixQuadratic (K₂ y) (w₂ y)) =
      (fun y => normalCoordinateDot.flip (V₂ y) (w₂ y)) := by
    funext y
    exact normalQuadratic_eq_pairing (K₂ y) (w₂ y)
  rw [hfun₁, hfun₂] at hq
  have htop := normalJet_bilinear_top_eq hS hV₁ hV₂ hw₁ hw₂ normalCoordinateDot.flip hz L hV hw hq
  have hpaired : normalJet L (fun y => normalMatrixPairedAction (w₁ z) (K₁ y) (w₁ y)) z =
      normalJet L (fun y => normalMatrixPairedAction (w₁ z) (K₂ y) (w₂ y)) z := by
    have h₁ := normalJet_clm_eqOn (normalCoordinateDot (w₁ z)) hS hV₁ L hz
    have h₂ := normalJet_clm_eqOn (normalCoordinateDot (w₁ z)) hS hV₂ L hz
    exact h₁.trans (htop.trans h₂.symm)
  have hKtop := normalJet_bilinear_top_eq hS hK₁ hK₂ hw₁ hw₂
    (normalMatrixPairedAction (w₁ z)) hz L hK hw hpaired
  exact (normalMatrixQuadratic_eq_dot _ _).trans
    (hKtop.trans (normalMatrixQuadratic_eq_dot _ _).symm)
end ConformalPoisson

end RefPart_NormalQuadraticJetComparison

/- Interface support: NormalMetricLowerJets.lean, SHA256 b2eec37de53b2e4ce453b5898c1916d105bece6b23d773e930da10b980fd9e37 -/
noncomputable section RefPart_NormalMetricLowerJets

/-! Lower K jets are already determined by the available inverse metric
jets. This is a project producer for the known terms in symbol extraction. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

theorem K_jet_eq_of_inverse_jets (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ j ≤ L, normalJet j F₁.inverse z = normalJet j F₂.inverse z)
    (r : ℕ) (hr : r + 1 ≤ L) : normalJet r F₁.K z = normalJet r F₂.K z := by
  rw [F₁.normalJet_K r hz, F₂.normalJet_K r hz, hA (r + 1) hr]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < r + 1 := Finset.mem_range.mp hj
  rw [tau_jet_eq_of_inverse_jets F₁ F₂ hz L hA j (by omega), hA (r - j) (by omega)]

theorem ell_jet_eq_of_inverse_jets (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ j ≤ L, normalJet j F₁.inverse z = normalJet j F₂.inverse z)
    (r : ℕ) (hr : r + 2 ≤ L) : normalJet r F₁.ell z = normalJet r F₂.ell z := by
  rw [F₁.normalJet_ell, F₂.normalJet_ell]
  exact congrArg (fun D : Matrix (Fin n) (Fin n) ℝ => (1 / 4 : ℝ) • D)
    (K_jet_eq_of_inverse_jets F₁ F₂ hz L hA (r + 1) (by omega))
end ConformalPoisson.NormalMetricField

end RefPart_NormalMetricLowerJets

/- Interface support: NormalMetricQuadraticExtraction.lean, SHA256 4c8b78629e52f9a107b9e9c17c726d579490c0a79b133dc6029384880468b26e -/
noncomputable section RefPart_NormalMetricQuadraticExtraction

/-! The actual variable-frequency quadratic jet comparison produces the K
quadratic needed by the checked next-metric-jet caller. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def KQuadratic (F : NormalMetricField S) (ξ : Fin n → ℝ) : EuclideanHalfSpace (n + 1) → ℝ :=
  fun z => normalMatrixQuadratic (F.K z) (F.frequency ξ z)

theorem KQuadratic_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (F.KQuadratic ξ) S := by
  have hV := normalBilinear_contMDiffOn normalMatrixAction F.K_smooth (F.frequency_smooth ξ hξ)
  have hQ := normalBilinear_contMDiffOn normalCoordinateDot.flip hV (F.frequency_smooth ξ hξ)
  have heq : F.KQuadratic ξ = (fun z => normalCoordinateDot.flip
      (normalMatrixAction (F.K z) (F.frequency ξ z)) (F.frequency ξ z)) := by
    funext z
    exact normalQuadratic_eq_pairing (F.K z) (F.frequency ξ z)
  rw [heq]
  exact hQ

theorem K_quadratic_eq_of_quadratic_jet_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z)
    (hQ : normalJet L (F₁.KQuadratic ξ) z = normalJet L (F₂.KQuadratic ξ) z) :
    normalMatrixQuadratic (normalJet L F₁.K z) (normalFrequency (F₁.inverse z) ξ) =
      normalMatrixQuadratic (normalJet L F₂.K z) (normalFrequency (F₁.inverse z) ξ) :=
  normalJet_quadratic_top_eq S.isOpen F₁.K_smooth F₂.K_smooth
    (F₁.frequency_smooth ξ hξ) (F₂.frequency_smooth ξ hξ) hz L
    (fun r hr => K_jet_eq_of_inverse_jets F₁ F₂ hz L hA r (by omega))
    (frequency_jets_eq F₁ F₂ hz ξ hξ L hA) hQ

theorem inverse_jet_step_of_quadratic_jet_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (hn : 2 ≤ n) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z)
    (hQ : ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
      normalJet L (F₁.KQuadratic ξ) z = normalJet L (F₂.KQuadratic ξ) z) :
    normalJet (L + 1) F₁.inverse z = normalJet (L + 1) F₂.inverse z := by
  have hK : normalJet L F₁.K z = normalJet L F₂.K z :=
    normalMatrix_eq_of_normalized_quadratic_eq (F₁.inverse z) _ _ (F₁.inverse_posDef z hz)
      (F₁.K_normalJet_symmetric L hz) (F₂.K_normalJet_symmetric L hz)
      (fun ξ hξ => K_quadratic_eq_of_quadratic_jet_eq F₁ F₂ hz ξ hξ L hA (hQ ξ hξ))
  exact inverse_jet_step F₁ F₂ hz hn L hA hK
end ConformalPoisson.NormalMetricField

end RefPart_NormalMetricQuadraticExtraction

/- Interface support: NormalPrincipalDerivative.lean, SHA256 c5a02f17cf47d6886cbbb6738318e22cde7f810b215dd374bfa76800b2aef00f -/
noncomputable section RefPart_NormalPrincipalDerivative

/-! The actual normal derivative of the principal root and the exact
normalized K quadratic used by the raw degree-zero symbol equation. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalMatrixQuadratic_sub (A B : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    normalMatrixQuadratic (A - B) ξ = normalMatrixQuadratic A ξ - normalMatrixQuadratic B ξ :=
  (normalQuadraticRead ξ).map_sub A B

theorem normalMatrixQuadratic_smul_matrix (r : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    normalMatrixQuadratic (r • A) ξ = r * normalMatrixQuadratic A ξ := by
  exact (normalQuadraticRead ξ).map_smul r A

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

theorem normalDeriv_quadratic (F : NormalMetricField S) (ξ : Fin n → ℝ)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalDeriv (F.quadratic ξ) z = normalMatrixQuadratic (normalDeriv F.inverse z) ξ :=
  normalJet_clm_eqOn (normalQuadraticRead ξ) S.isOpen F.inverse_smooth 1 hz

theorem principal_square (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    F.principal ξ z * F.principal ξ z = F.quadratic ξ z :=
  Real.mul_self_sqrt (F.quadratic_pos ξ hξ z hz).le

theorem principal_normal_product (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    (2 * F.principal ξ z) * normalDeriv (F.principal ξ) z =
      normalMatrixQuadratic (normalDeriv F.inverse z) ξ := by
  have hsq : EqOn (F.principal ξ * F.principal ξ) (F.quadratic ξ) S :=
    fun y hy => F.principal_square ξ hξ hy
  have he := normalDeriv_eq_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (S.isOpen.mem_nhds hz) hsq)
  have hs := ((F.principal_smooth ξ hξ z hz).contMDiffAt
    (S.isOpen.mem_nhds hz)).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  rw [normalDeriv_mul hs hs, F.normalDeriv_quadratic ξ hz] at he
  nlinarith [he]

theorem normalDeriv_principal (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalDeriv (F.principal ξ) z =
      normalMatrixQuadratic (normalDeriv F.inverse z) ξ / (2 * F.principal ξ z) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (F.principal_pos ξ hξ z hz).ne')).mpr
  rw [mul_comm]
  exact F.principal_normal_product ξ hξ hz

theorem frequency_unit (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalMatrixQuadratic (F.inverse z) (F.frequency ξ z) = 1 := by
  change normalMatrixQuadratic (F.inverse z) ((F.principal ξ z)⁻¹ • ξ) = 1
  rw [normalMatrixQuadratic_smul, ← normalPrincipal_sq (F.inverse z) (F.inverse_posDef z hz) ξ hξ]
  have hs := (F.principal_pos ξ hξ z hz).ne'
  change (F.principal ξ z)⁻¹ ^ 2 * (F.principal ξ z) ^ 2 = 1
  field_simp

theorem KQuadratic_formula (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    F.KQuadratic ξ z = normalMatrixQuadratic (normalDeriv F.inverse z) ξ /
      (F.principal ξ z) ^ 2 - F.tau z := by
  change normalMatrixQuadratic (normalDeriv F.inverse z - F.tau z • F.inverse z) (F.frequency ξ z) = _
  rw [normalMatrixQuadratic_sub, normalMatrixQuadratic_smul_matrix, F.frequency_unit ξ hξ hz, mul_one]
  change normalMatrixQuadratic (normalDeriv F.inverse z) ((F.principal ξ z)⁻¹ • ξ) - F.tau z = _
  rw [normalMatrixQuadratic_smul]
  have hs := (F.principal_pos ξ hξ z hz).ne'
  field_simp
end NormalMetricField
end ConformalPoisson

end RefPart_NormalPrincipalDerivative

/- Interface support: NormalJetRecoveryCaller.lean, SHA256 0733cffa56ca0da391352f39d91ad6d33f94068b4de4f02e496a68caea82af0d -/
noncomputable section RefPart_NormalJetRecoveryCaller

/-! Checked CONDITIONAL callers exposing the precise outstanding symbol
producer. These hypotheses are not declared literature premises: the actual
symbol recursion must produce them from the actual localized DN operator.
Every order concerns the SAME boundary set B inside the SAME open source S. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

theorem all_normalJets_of_inverse_step (F₁ F₂ : NormalMetricField S)
    (B : Set (EuclideanHalfSpace (n + 1))) (hB : B ⊆ S)
    (hbase : EqOn F₁.inverse F₂.inverse B)
    (hstep : ∀ L : ℕ,
      (∀ r ≤ L, EqOn (normalJet r F₁.inverse) (normalJet r F₂.inverse) B) →
      EqOn (normalJet (L + 1) F₁.inverse) (normalJet (L + 1) F₂.inverse) B) :
    ∀ k : ℕ, EqOn (normalJet k F₁.inverse) (normalJet k F₂.inverse) B ∧
      EqOn (normalJet k F₁.gram) (normalJet k F₂.gram) B := by
  have hall : ∀ k : ℕ, ∀ r ≤ k, EqOn (normalJet r F₁.inverse) (normalJet r F₂.inverse) B := by
    intro k
    induction k with
    | zero =>
      intro r hr
      have he : r = 0 := by omega
      subst r
      exact hbase
    | succ k ih =>
      intro r hr
      by_cases hle : r ≤ k
      · exact ih r hle
      · have he : r = k + 1 := by omega
        subst r
        intro z hz
        exact hstep k ih hz
  intro k
  refine ⟨hall k k le_rfl, ?_⟩
  intro z hz
  exact inverse_jet_transfer F₁ F₂ (hB hz) k (fun r hr => hall k r hr hz) k le_rfl

theorem all_normalJets_of_K_recovery (F₁ F₂ : NormalMetricField S)
    (B : Set (EuclideanHalfSpace (n + 1))) (hB : B ⊆ S) (hn : 2 ≤ n)
    (hbase : EqOn F₁.inverse F₂.inverse B)
    (hK : ∀ L : ℕ,
      (∀ r ≤ L, EqOn (normalJet r F₁.inverse) (normalJet r F₂.inverse) B) →
      EqOn (normalJet L F₁.K) (normalJet L F₂.K) B) :
    ∀ k : ℕ, EqOn (normalJet k F₁.inverse) (normalJet k F₂.inverse) B ∧
      EqOn (normalJet k F₁.gram) (normalJet k F₂.gram) B := by
  apply all_normalJets_of_inverse_step F₁ F₂ B hB hbase
  intro L hA z hz
  exact inverse_jet_step F₁ F₂ (hB hz) hn L (fun r hr => hA r hr hz) (hK L hA hz)

theorem all_normalJets_of_quadratic_K_recovery (F₁ F₂ : NormalMetricField S)
    (B : Set (EuclideanHalfSpace (n + 1))) (hB : B ⊆ S) (hn : 2 ≤ n)
    (hprincipal : ∀ z ∈ B, ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
      normalPrincipal (F₁.inverse z) ξ = normalPrincipal (F₂.inverse z) ξ)
    (hquadratic : ∀ L : ℕ,
      (∀ r ≤ L, EqOn (normalJet r F₁.inverse) (normalJet r F₂.inverse) B) →
      ∀ z ∈ B, ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
        normalMatrixQuadratic (normalJet L F₁.K z) (normalFrequency (F₁.inverse z) ξ) =
        normalMatrixQuadratic (normalJet L F₂.K z) (normalFrequency (F₁.inverse z) ξ)) :
    ∀ k : ℕ, EqOn (normalJet k F₁.inverse) (normalJet k F₂.inverse) B ∧
      EqOn (normalJet k F₁.gram) (normalJet k F₂.gram) B := by
  have hbase : EqOn F₁.inverse F₂.inverse B := by
    intro z hz
    exact normalMatrix_eq_of_principal_eq _ _ (F₁.inverse_posDef z (hB hz))
      (F₂.inverse_posDef z (hB hz)) (hprincipal z hz)
  apply all_normalJets_of_K_recovery F₁ F₂ B hB hn hbase
  intro L hA z hz
  exact normalMatrix_eq_of_normalized_quadratic_eq (F₁.inverse z)
    (normalJet L F₁.K z) (normalJet L F₂.K z) (F₁.inverse_posDef z (hB hz))
    (F₁.K_normalJet_symmetric L (hB hz)) (F₂.K_normalJet_symmetric L (hB hz))
    (hquadratic L hA z hz)
end ConformalPoisson.NormalMetricField

end RefPart_NormalJetRecoveryCaller

/- Interface support: NativeNormalChartCoordinates.lean, SHA256 24b7e36b48dc6f1fd7434f8b4ff8b3f27b2addc69c1da7cb7fc3351495a9e2a4 -/
noncomputable section RefPart_NativeNormalChartCoordinates

/-! Actual original chart-domain and coordinate labels of the SAME normal map.
These bind the later boundary identification to actual boundary-chart inverses. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}
  (R : NativeMetricAmbientExtension g (α : M))

local instance : RiemannianBundle (fun x : R.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R.metric.toRiemannianMetric⟩
local instance : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
  IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)

variable {D : BoundaryNormalMapData R.domain R.boundaryBase}
  {Q : BoundaryNormalRectangle R.domain D} (A : NormalModelChartData R.domain D Q)


theorem NativeMetricAmbientExtension.normalChart_image_in_original_source
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) :
    R.normalChart A z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source := by
  rw [R.normalChart_apply]
  exact (extChartAt (𝓡∂ (n + 1)) (α : M)).map_target
    (hcompat (A.chart z.1) (A.image_mem z.1 hz) ((A.side z.1 hz).mpr z.property))

theorem NativeMetricAmbientExtension.normalChart_coordinate
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) :
    extChartAt (𝓡∂ (n + 1)) (α : M) (R.normalChart A z) = A.chart z.1 := by
  rw [R.normalChart_apply]
  exact (extChartAt (𝓡∂ (n + 1)) (α : M)).right_inv
    (hcompat (A.chart z.1) (A.image_mem z.1 hz) ((A.side z.1 hz).mpr z.property))

theorem NativeMetricAmbientExtension.normalChart_boundary_coordinate
    (hcompat : ∀ z ∈ R.domain, 0 ≤ z 0 → z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).target)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ A.chart.source) (hzero : z.1 0 = 0) :
    extChartAt (𝓡∂ (n + 1)) (α : M) (R.normalChart A z) = z.1 :=
  (R.normalChart_coordinate A hcompat hz).trans (A.boundary_identity R.domain hz hzero)
end ConformalPoisson

end RefPart_NativeNormalChartCoordinates

/- Interface support: NormalChartLabels.lean, SHA256 707194e63bc101a849041a02c846b92befbf533011d120fd6b5541690b6ba267 -/
noncomputable section RefPart_NormalChartLabels

/-! The actual original boundary labels, including chart-source membership.
These identify the intrinsic boundary coordinates used by beta. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

structure NormalChartLabels
    (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)
    (α : (𝓡∂ (n + 1)).boundary M) : Prop where
  source : ∀ z ∈ χ.source, χ z ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source
  boundary_value : ∀ z ∈ χ.source, z.1 0 = 0 →
    χ z = (extChartAt (𝓡∂ (n + 1)) (α : M)).symm z.1
  boundary_coordinate : ∀ z ∈ χ.source, z.1 0 = 0 →
    extChartAt (𝓡∂ (n + 1)) (α : M) (χ z) = z.1

variable {χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω}
  {α : (𝓡∂ (n + 1)).boundary M} (L : NormalChartLabels χ α)

include L

theorem NormalChartLabels.boundary_source
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (hzero : z.1 0 = 0) :
    (⟨χ z, partialDiffeomorph_halfSpace_boundary χ hz hzero⟩ : (𝓡∂ (n + 1)).boundary M) ∈
      (extChartAt (𝓡 n) α).source := by
  simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using L.source z hz

theorem NormalChartLabels.boundary_read
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ χ.source) (hzero : z.1 0 = 0) :
    extChartAt (𝓡 n) α
      (⟨χ z, partialDiffeomorph_halfSpace_boundary χ hz hzero⟩ : (𝓡∂ (n + 1)).boundary M) =
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 := by
  have h := (boundaryParam_extChartAt (L.boundary_source hz hzero)).trans
    (L.boundary_coordinate z hz hzero)
  have hp := congrArg (euclideanHalfSpaceBoundaryProj n) h
  simpa only [euclideanHalfSpaceBoundaryProj_param,
    euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_fst] using hp
end ConformalPoisson

end RefPart_NormalChartLabels

/- Interface support: BoundaryCoordinateChange.lean, SHA256 351116c5747e63da04d74ef707259bf33d51d1116ca96fda46e7587f71aca19b -/
noncomputable section RefPart_BoundaryCoordinateChange

/-! The ACTUAL analytic boundary identification, in the selected preferred
boundary charts, is an actual analytic Euclidean partial diffeomorphism. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

theorem exists_boundaryCoordinateChange
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) :
    ∃ B : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω,
      extChartAt (𝓡 n) α α ∈ B.source ∧
      B (extChartAt (𝓡 n) α α) = extChartAt (𝓡 n) (β α) (β α) ∧
      B.source ⊆ (extChartAt (𝓡 n) α).target ∧
      ∀ z ∈ B.source,
        β ((extChartAt (𝓡 n) α).symm z) ∈ (extChartAt (𝓡 n) (β α)).source ∧
        B z = extChartAt (𝓡 n) (β α) (β ((extChartAt (𝓡 n) α).symm z)) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  let cS := extChartPartialDiffeomorph (𝓡 n) ω α
  let cT := extChartPartialDiffeomorph (𝓡 n) ω (β α)
  let b : PartialDiffeomorph (𝓡 n) (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω :=
    { toPartialEquiv := β.toHomeomorph.toEquiv.toPartialEquiv
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := β.contMDiff.contMDiffOn
      contMDiffOn_invFun := β.symm.contMDiff.contMDiffOn }
  let B := cS.symm.trans (b.trans cT)
  have hs : α ∈ cS.source :=
    (mem_extChartPartialDiffeomorph_source _ _ _).mpr BoundarylessManifold.isInteriorPoint
  have ht : β α ∈ cT.source :=
    (mem_extChartPartialDiffeomorph_source _ _ _).mpr BoundarylessManifold.isInteriorPoint
  have hreadS : cS α = extChartAt (𝓡 n) α α := by simp only [cS, coe_extChartPartialDiffeomorph]
  have hinv : cS.symm (extChartAt (𝓡 n) α α) = α := by
    rw [← hreadS]
    exact cS.left_inv hs
  have hbase : extChartAt (𝓡 n) α α ∈ B.source := by
    rw [PartialDiffeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · change extChartAt (𝓡 n) α α ∈ cS.target
      rw [← hreadS]
      exact cS.map_source hs
    · change cS.symm (extChartAt (𝓡 n) α α) ∈ (b.trans cT).source
      rw [hinv, PartialDiffeomorph.trans_source]
      exact ⟨mem_univ _, ht⟩
  have hvalue (z : EuclideanSpace ℝ (Fin n)) :
      B z = extChartAt (𝓡 n) (β α) (β ((extChartAt (𝓡 n) α).symm z)) := by
    dsimp only [B]
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply,
      PartialDiffeomorph.coe_trans, Function.comp_apply,
      coe_extChartPartialDiffeomorph]
    have hsymm : cS.symm z = (extChartAt (𝓡 n) α).symm z :=
      extChartPartialDiffeomorph_symm_apply _ _ _ _
    rw [hsymm]
    rfl
  have hmem (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ B.source) :
      β ((extChartAt (𝓡 n) α).symm z) ∈ (extChartAt (𝓡 n) (β α)).source := by
    have hz' : z ∈ cS.target ∧ cS.symm z ∈ (b.trans cT).source := by
      rw [PartialDiffeomorph.trans_source] at hz
      exact hz
    have hr := hz'.2
    rw [PartialDiffeomorph.trans_source] at hr
    have ht' : β (cS.symm z) ∈ cT.source := hr.2
    have hsymm : cS.symm z = (extChartAt (𝓡 n) α).symm z :=
      extChartPartialDiffeomorph_symm_apply _ _ _ _
    rw [hsymm] at ht'
    rw [extChartPartialDiffeomorph_source] at ht'
    exact ht'.1
  refine ⟨B, hbase, ?_, ?_, (fun z hz => ⟨hmem z hz, hvalue z⟩)⟩
  · rw [hvalue, extChartAt_to_inv]
  · intro z hz
    have hzs : z ∈ cS.target := hz.1
    rw [extChartPartialDiffeomorph_target] at hzs
    exact interior_subset hzs

structure BoundaryCoordinateChangeData
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) where
  chart : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω
  base_mem : extChartAt (𝓡 n) α α ∈ chart.source
  base_value : chart (extChartAt (𝓡 n) α α) = extChartAt (𝓡 n) (β α) (β α)
  source_subset : chart.source ⊆ (extChartAt (𝓡 n) α).target
  reads : ∀ z ∈ chart.source,
    β ((extChartAt (𝓡 n) α).symm z) ∈ (extChartAt (𝓡 n) (β α)).source ∧
      chart z = extChartAt (𝓡 n) (β α) (β ((extChartAt (𝓡 n) α).symm z))

theorem exists_boundaryCoordinateChangeData
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) : Nonempty (BoundaryCoordinateChangeData β α) := by
  obtain ⟨B, hb, hv, hs, hr⟩ := exists_boundaryCoordinateChange β α
  exact ⟨⟨B, hb, hv, hs, hr⟩⟩

end ConformalPoisson

end RefPart_BoundaryCoordinateChange

/- Interface support: SpatialCoordinateLift.lean, SHA256 502e3ae1a29bbe1e2c051d42e69d5641766f13b860315c12485d6d36825e47ed -/
noncomputable section RefPart_SpatialCoordinateLift

/-! Lift an actual analytic change of boundary coordinates while keeping the
inward time parameter unchanged. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

def spatialProductDiffeomorph
    (B : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
      (EuclideanSpace ℝ (Fin n) × ℝ) (EuclideanSpace ℝ (Fin n) × ℝ) ω where
  toPartialEquiv := B.toPartialEquiv.prod (PartialEquiv.refl ℝ)
  open_source := B.open_source.prod isOpen_univ
  open_target := B.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    apply contMDiffOn_iff_contDiffOn.mpr
    exact (B.contMDiffOn_toFun.contDiffOn.comp (s := B.source ×ˢ (Set.univ : Set ℝ)) contDiff_fst.contDiffOn
      (fun p hp => hp.1)).prodMk contDiff_snd.contDiffOn
  contMDiffOn_invFun := by
    apply contMDiffOn_iff_contDiffOn.mpr
    exact (B.contMDiffOn_invFun.contDiffOn.comp (s := B.target ×ˢ (Set.univ : Set ℝ)) contDiff_fst.contDiffOn
      (fun p hp => hp.1)).prodMk contDiff_snd.contDiffOn

theorem spatialProductDiffeomorph_apply
    (B : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) : spatialProductDiffeomorph B p = (B p.1, p.2) := rfl

def spatialCoordinateLift
    (B : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω :=
  ((euclideanHalfSpaceBoundaryNormalEquiv n).symm.toPartialDiffeomorph (n := ω)).trans
    ((spatialProductDiffeomorph B).trans
      (euclideanHalfSpaceBoundaryNormalEquiv n).toPartialDiffeomorph (n := ω))

section Computations
variable (B : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω)

theorem spatialProductDiffeomorph_symm_apply (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    (spatialProductDiffeomorph B).symm p = (B.symm p.1, p.2) := rfl

theorem spatialCoordinateLift_apply (z : EuclideanSpace ℝ (Fin (n + 1))) :
    spatialCoordinateLift B z = euclideanHalfSpaceBoundaryNormalEquiv n
      (B (((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).1),
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).2) := by
  simp only [spatialCoordinateLift, PartialDiffeomorph.coe_trans, Function.comp_apply,
    ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  rfl

theorem spatialCoordinateLift_time (z : EuclideanSpace ℝ (Fin (n + 1))) :
    spatialCoordinateLift B z 0 = z 0 := by
  rw [spatialCoordinateLift_apply, euclideanHalfSpaceBoundaryNormalEquiv_apply_zero,
    euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd]

theorem spatialCoordinateLift_symm_apply (z : EuclideanSpace ℝ (Fin (n + 1))) :
    (spatialCoordinateLift B).symm z = euclideanHalfSpaceBoundaryNormalEquiv n
      (B.symm (((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).1),
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).2) := by
  rw [spatialCoordinateLift, PartialDiffeomorph.coe_trans_symm, Function.comp_apply,
    PartialDiffeomorph.coe_trans_symm, Function.comp_apply]
  simp only [PartialDiffeomorph.symm_toPartialEquiv,
    ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  rfl

theorem spatialCoordinateLift_symm_time (z : EuclideanSpace ℝ (Fin (n + 1))) :
    (spatialCoordinateLift B).symm z 0 = z 0 := by
  rw [spatialCoordinateLift_symm_apply, euclideanHalfSpaceBoundaryNormalEquiv_apply_zero,
    euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd]


theorem spatialCoordinateLift_source :
    (spatialCoordinateLift B).source =
      {z | ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).1 ∈ B.source} := by
  ext z
  simp [spatialCoordinateLift,
    ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv, spatialProductDiffeomorph,
    PartialEquiv.prod_source]

def halfSpaceSpatialCoordinateLift :
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) ω :=
  halfSpacePartialDiffeomorph (spatialCoordinateLift B)
    (fun z _ => by rw [spatialCoordinateLift_time])
    (fun z _ => by rw [spatialCoordinateLift_symm_time])

theorem halfSpaceSpatialCoordinateLift_source :
    (halfSpaceSpatialCoordinateLift B).source =
      {z : EuclideanHalfSpace (n + 1) |
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 ∈ B.source} := by
  rw [halfSpaceSpatialCoordinateLift, halfSpacePartialDiffeomorph_source, spatialCoordinateLift_source]
  rfl

theorem halfSpaceSpatialCoordinateLift_value {z : EuclideanHalfSpace (n + 1)}
    (hz : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 ∈ B.source) :
    (halfSpaceSpatialCoordinateLift B z).1 = spatialCoordinateLift B z.1 := by
  apply halfSpacePartialDiffeomorph_coe_apply
  rw [spatialCoordinateLift_source]
  exact hz
end Computations

end ConformalPoisson

end RefPart_SpatialCoordinateLift

/- Interface support: HalfSpaceDifferential.lean, SHA256 61d2d6030621f6725fbf02600cb54c55e602d0414404fb3e8b91e45f59987e82 -/
noncomputable section RefPart_HalfSpaceDifferential

/-! The actual native differential of a half-space restriction reads the
ordinary differential of the same ambient map, including at time zero. -/

open Filter Set Topology TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem halfSpacePartialDiffeomorph_mfderiv_apply
    (C : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ω)
    (hf : ∀ z ∈ C.source, 0 ≤ C z 0 ↔ 0 ≤ z 0)
    (hb : ∀ z ∈ C.target, 0 ≤ C.symm z 0 ↔ 0 ≤ z 0)
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 ∈ C.source)
    (v : TangentSpace (𝓡∂ (n + 1)) z) :
    (show EuclideanSpace ℝ (Fin (n + 1)) from
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (halfSpacePartialDiffeomorph C hf hb) z v) =
      fderiv ℝ C z.1 v := by
  let e := halfSpacePartialDiffeomorph C hf hb
  have hsource := halfSpacePartialDiffeomorph_source C hf hb
  have hze : z ∈ e.source := by rw [hsource]; exact hz
  have heq : ((𝓡∂ (n + 1)) ∘ e) =ᶠ[nhds z]
      (C ∘ (𝓡∂ (n + 1))) := by
    filter_upwards [e.open_source.mem_nhds hze] with w hw
    have hw' : w.1 ∈ C.source := by rw [hsource] at hw; exact hw
    exact halfSpacePartialDiffeomorph_coe_apply C hf hb hw'
  have hC : DifferentiableAt ℝ C z.1 :=
    ((C.contMDiffOn_toFun z.1 hz).contMDiffAt (C.open_source.mem_nhds hz)).contDiffAt.differentiableAt
      (by decide : (ω : ℕ∞ω) ≠ 0)
  have hdI (x : EuclideanHalfSpace (n + 1)) (w : TangentSpace (𝓡∂ (n + 1)) x) :
      mvfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) x w = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply, (𝓡∂ (n + 1)).hasMFDerivAt.mfderiv]
    rfl
  have hleft := mvfderiv_comp_apply z (𝓡∂ (n + 1)).hasMFDerivAt.mdifferentiableAt
    (e.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hze) v
  have hright := TauCeti.mvfderiv_comp_apply_of_differentiableAt hC
    (𝓡∂ (n + 1)).hasMFDerivAt.mdifferentiableAt v
  have hread := hdI (e z) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) e z v)
  exact hread.symm.trans (hleft.symm.trans
    ((congrArg (fun L => L v) heq.mvfderiv_eq).trans
      (hright.trans (congrArg (fderiv ℝ C z.1) (hdI z v)))))
end ConformalPoisson

end RefPart_HalfSpaceDifferential

/- Interface support: SpatialCoordinateDifferential.lean, SHA256 ff93b1114241446cc03a14256e5318d372f7f802727d8b91581512368b63d8d0 -/
noncomputable section RefPart_SpatialCoordinateDifferential

/-! The actual lift keeps the time differential fixed and sends each spatial
vector to the spatial derivative of the actual boundary coordinate change. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}
variable (B : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω)

theorem spatialCoordinateLift_fderiv_apply
    {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).1 ∈ B.source)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    fderiv ℝ (spatialCoordinateLift B) z (euclideanHalfSpaceBoundaryNormalEquiv n (v, t)) =
      euclideanHalfSpaceBoundaryNormalEquiv n
        (fderiv ℝ B ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z).1 v, t) := by
  let A := euclideanHalfSpaceBoundaryNormalEquiv n
  let q := A.symm z
  have hB : DifferentiableAt ℝ B q.1 :=
    ((B.contMDiffOn_toFun q.1 hz).contMDiffAt (B.open_source.mem_nhds hz)).contDiffAt.differentiableAt
      (by decide : (ω : ℕ∞ω) ≠ 0)
  have hprod : HasFDerivAt (Prod.map B (id : ℝ → ℝ))
      ((fderiv ℝ B q.1).prodMap (ContinuousLinearMap.id ℝ ℝ)) q :=
    HasFDerivAt.prodMap q hB.hasFDerivAt (hasFDerivAt_id q.2)
  have h := A.hasFDerivAt.comp z (hprod.comp z A.symm.hasFDerivAt)
  have heq : spatialCoordinateLift B =ᶠ[nhds z] (A ∘ Prod.map B (id : ℝ → ℝ) ∘ A.symm) := by
    exact Filter.Eventually.of_forall (spatialCoordinateLift_apply B)
  have hτ := h.congr_of_eventuallyEq heq
  have hval := congrArg (fun L => L (A (v, t))) hτ.fderiv
  simpa [ContinuousLinearMap.prodMap, A, q] using hval

set_option backward.isDefEq.respectTransparency false in
theorem halfSpaceSpatialCoordinateLift_mfderiv_apply
    {z : EuclideanHalfSpace (n + 1)}
    (hz : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 ∈ B.source)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (show EuclideanSpace ℝ (Fin (n + 1)) from
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (halfSpaceSpatialCoordinateLift B) z
        (euclideanHalfSpaceBoundaryNormalEquiv n (v, t))) =
      euclideanHalfSpaceBoundaryNormalEquiv n
        (fderiv ℝ B ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 v, t) := by
  have hp : z.1 ∈ (spatialCoordinateLift B).source := by
    rw [spatialCoordinateLift_source]
    exact hz
  exact (halfSpacePartialDiffeomorph_mfderiv_apply (spatialCoordinateLift B)
    (fun y _ => by rw [spatialCoordinateLift_time])
    (fun y _ => by rw [spatialCoordinateLift_symm_time]) hp
    (euclideanHalfSpaceBoundaryNormalEquiv n (v, t))).trans
      (spatialCoordinateLift_fderiv_apply B hz v t)

theorem halfSpaceSpatialCoordinateLift_time
    {z : EuclideanHalfSpace (n + 1)}
    (hz : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 ∈ B.source) :
    (halfSpaceSpatialCoordinateLift B z).1 0 = z.1 0 :=
  (congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w 0)
    (halfSpaceSpatialCoordinateLift_value B hz)).trans (spatialCoordinateLift_time B z.1)

theorem halfSpaceSpatialCoordinateLift_time_differential
    {z : EuclideanHalfSpace (n + 1)}
    (hz : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 ∈ B.source) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (halfSpaceSpatialCoordinateLift B) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) =
        (show TangentSpace (𝓡∂ (n + 1)) (halfSpaceSpatialCoordinateLift B z) from
          euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  have h := halfSpaceSpatialCoordinateLift_mfderiv_apply B hz 0 1
  have hz0 : fderiv ℝ B ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 0 = 0 := map_zero _
  exact h.trans (congrArg (fun w : EuclideanSpace ℝ (Fin n) => euclideanHalfSpaceBoundaryNormalEquiv n (w, 1)) hz0)
end ConformalPoisson

end RefPart_SpatialCoordinateDifferential

/- Interface support: CommonBoundaryLabels.lean, SHA256 115ed0f0b8b17d74290c2469e10c88d06ee963f51a1f57cbcdd74eafc44d63eb -/
noncomputable section RefPart_CommonBoundaryLabels

/-! The lifted ACTUAL analytic boundary identification aligns the two actual
normal charts pointwise on the boundary, preserving the prescribed beta. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

set_option backward.isDefEq.respectTransparency false in
theorem common_normalChart_boundary_value
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) (B : BoundaryCoordinateChangeData β α)
    (χ₁ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M₁ ω)
    (χ₂ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M₂ ω)
    (L₁ : NormalChartLabels χ₁ α) (L₂ : NormalChartLabels χ₂ (β α))
    {z : EuclideanHalfSpace (n + 1)} (hz₁ : z ∈ χ₁.source)
    (hz₂ : z ∈ ((halfSpaceSpatialCoordinateLift B.chart).trans χ₂).source) (hzero : z.1 0 = 0) :
    ((halfSpaceSpatialCoordinateLift B.chart).trans χ₂) z =
      (β ⟨χ₁ z, partialDiffeomorph_halfSpace_boundary χ₁ hz₁ hzero⟩ : M₂) := by
  let η := halfSpaceSpatialCoordinateLift B.chart
  let y₁ : (𝓡∂ (n + 1)).boundary M₁ := ⟨χ₁ z, partialDiffeomorph_halfSpace_boundary χ₁ hz₁ hzero⟩
  let ξ := ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1
  have hp : z ∈ η.source ∧ η z ∈ χ₂.source := by
    rw [PartialDiffeomorph.trans_source] at hz₂
    exact hz₂
  have hB : ξ ∈ B.chart.source := by
    have h := hp.1
    rw [halfSpaceSpatialCoordinateLift_source] at h
    exact h
  have hξ : extChartAt (𝓡 n) α y₁ = ξ := L₁.boundary_read hz₁ hzero
  have hxinv : (extChartAt (𝓡 n) α).symm ξ = y₁ := by
    rw [← hξ]
    exact (extChartAt (𝓡 n) α).left_inv (L₁.boundary_source hz₁ hzero)
  obtain ⟨hβmem, hBval⟩ := B.reads ξ hB
  rw [hxinv] at hβmem hBval
  have hηzero : (η z).1 0 = 0 := (halfSpaceSpatialCoordinateLift_time B.chart hB).trans hzero
  have hηval : (η z).1 = extChartAt (𝓡∂ (n + 1)) (β α : M₂) (β y₁ : M₂) := by
    calc
      (η z).1 = spatialCoordinateLift B.chart z.1 := halfSpaceSpatialCoordinateLift_value B.chart hB
      _ = euclideanHalfSpaceBoundaryNormalEquiv n (B.chart ξ, 0) := by
        rw [spatialCoordinateLift_apply, euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd, hzero]
      _ = euclideanHalfSpaceBoundaryParam n (extChartAt (𝓡 n) (β α) (β y₁)) := by
        rw [hBval, euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
      _ = extChartAt (𝓡∂ (n + 1)) (β α : M₂) (β y₁ : M₂) := boundaryParam_extChartAt hβmem
  have hβM : (β y₁ : M₂) ∈ (extChartAt (𝓡∂ (n + 1)) (β α : M₂)).source := by
    simpa only [extChartAt_source, boundaryChartedSpace_chartAt_source, mem_preimage] using hβmem
  calc
    (η.trans χ₂) z = χ₂ (η z) := congrFun (PartialDiffeomorph.coe_trans η χ₂) z
    _ = (extChartAt (𝓡∂ (n + 1)) (β α : M₂)).symm (η z).1 := L₂.boundary_value (η z) hp.2 hηzero
    _ = (extChartAt (𝓡∂ (n + 1)) (β α : M₂)).symm
        (extChartAt (𝓡∂ (n + 1)) (β α : M₂) (β y₁ : M₂)) :=
      congrArg (extChartAt (𝓡∂ (n + 1)) (β α : M₂)).symm hηval
    _ = (β y₁ : M₂) := (extChartAt (𝓡∂ (n + 1)) (β α : M₂)).left_inv hβM
end ConformalPoisson

end RefPart_CommonBoundaryLabels

/- Interface support: NormalChartData.lean, SHA256 ffb1843460b65129b75f65155f04ba4bd477db0008a72e004669a4499d6a99c3 -/
noncomputable section RefPart_NormalChartData

/-! One actual analytic normal chart with its original base/labels and all
proved native metric/normal/DN geometry. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

structure NormalChartData (g : Metric (n := n) (M := M)) (α : (𝓡∂ (n + 1)).boundary M) where
  chart : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω
  geometry : NormalChartGeometry g chart
  labels : NormalChartLabels chart α
  base_mem : chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M) ∈ chart.source
  base_value : chart (chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M)) = (α : M)

theorem exists_normalChartData
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : (𝓡∂ (n + 1)).boundary M} (hα : (α : M) ∈ U) :
    Nonempty (NormalChartData g α) := by
  obtain ⟨R⟩ := exists_native_metric_ambient_extension g U hg hα
  obtain ⟨R', _, _, hcompat⟩ := R.exists_domain_in_chart
  let : RiemannianBundle (fun x : R'.domain =>
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) := ⟨R'.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 1
    (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : R'.domain => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) x) :=
      IsContMDiffRiemannianBundle.of_le (n := ω) (by decide)
  obtain ⟨⟨D, Q⟩⟩ := R'.exists_normalRectangle
  obtain ⟨A⟩ := exists_normalModelChartData R'.domain D Q
  have hsource {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ (R'.normalChart A).source) :
      z.1 ∈ A.chart.source := by
    rw [R'.normalChart_source A hcompat] at hz
    exact hz
  refine ⟨⟨R'.normalChart A, ?_, ?_, R'.normalChart_base_mem A hcompat,
    R'.normalChart_base_value A⟩⟩
  · exact ⟨(fun z hz => R'.normalChart_time_inner A hcompat (hsource hz)),
      (fun z hz v => R'.normalChart_spatial_time_inner A hcompat (hsource hz) v),
      (fun z hz hzero ν hν => R'.normalChart_outwardNormal A hcompat (hsource hz) hzero ν hν)⟩
  · exact ⟨(fun z hz => R'.normalChart_image_in_original_source A hcompat (hsource hz)),
      (fun z hz hzero => R'.normalChart_boundary_value A (hsource hz) hzero),
      (fun z hz hzero => R'.normalChart_boundary_coordinate A hcompat (hsource hz) hzero)⟩
end ConformalPoisson

end RefPart_NormalChartData

/- Interface support: CommonNormalBase.lean, SHA256 c6625ce96ca5bede6b3fd5b3c0f35cf91e6d66b6499fb6c02ecf4184fecedec0 -/
noncomputable section RefPart_CommonNormalBase

/-! The actual lifted boundary identification aligns the actual original base
points, giving a nonempty common domain for the normal charts. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M M₁ M₂ : Type*} [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

theorem boundaryNormalBase_read (α : (𝓡∂ (n + 1)).boundary M) :
    (chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M)).1 =
      euclideanHalfSpaceBoundaryNormalEquiv n (extChartAt (𝓡 n) α α, 0) := by
  change extChartAt (𝓡∂ (n + 1)) (α : M) (α : M) = _
  rw [euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
  exact (boundaryParam_extChartAt (mem_extChartAt_source α)).symm

theorem boundaryCoordinateLift_base
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) (B : BoundaryCoordinateChangeData β α) :
    let z₁ := chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)
    let z₂ := chartAt (EuclideanHalfSpace (n + 1)) (β α : M₂) (β α : M₂)
    z₁ ∈ (halfSpaceSpatialCoordinateLift B.chart).source ∧
      halfSpaceSpatialCoordinateLift B.chart z₁ = z₂ := by
  let z₁ := chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)
  let z₂ := chartAt (EuclideanHalfSpace (n + 1)) (β α : M₂) (β α : M₂)
  have hB : ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z₁.1).1 ∈ B.chart.source := by
    rw [boundaryNormalBase_read α, ContinuousLinearEquiv.symm_apply_apply]
    exact B.base_mem
  refine ⟨?_, ?_⟩
  · rw [halfSpaceSpatialCoordinateLift_source]
    exact hB
  · apply Subtype.ext
    refine (halfSpaceSpatialCoordinateLift_value B.chart hB).trans ?_
    rw [spatialCoordinateLift_apply, boundaryNormalBase_read α,
      ContinuousLinearEquiv.symm_apply_apply, B.base_value]
    exact (boundaryNormalBase_read (β α)).symm

theorem aligned_normalChart_base
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁) (B : BoundaryCoordinateChangeData β α)
    {g₂ : Metric (n := n) (M := M₂)} (D₂ : NormalChartData g₂ (β α)) :
    let z := chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)
    z ∈ ((halfSpaceSpatialCoordinateLift B.chart).trans D₂.chart).source ∧
      ((halfSpaceSpatialCoordinateLift B.chart).trans D₂.chart) z = (β α : M₂) := by
  obtain ⟨hs, hv⟩ := boundaryCoordinateLift_base β α B
  refine ⟨?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    refine ⟨hs, ?_⟩
    change halfSpaceSpatialCoordinateLift B.chart
      (chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)) ∈ D₂.chart.source
    rw [hv]
    exact D₂.base_mem
  · exact (congrFun (PartialDiffeomorph.coe_trans (halfSpaceSpatialCoordinateLift B.chart) D₂.chart) _).trans
      ((congrArg D₂.chart hv).trans D₂.base_value)
end ConformalPoisson

end RefPart_CommonNormalBase

/- Interface support: NormalChartRestriction.lean, SHA256 a8a76bbcdf08486461d61e79c8e08f6b4584f471fc6e04ad30ef400864c4d059 -/
noncomputable section RefPart_NormalChartRestriction

/-! Restrict an actual normal chart while retaining the same geometry and DN
interpretation. This makes the local zero-potential/gauge domain explicit. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)}
  {χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω}

theorem NormalChartGeometry.restrOpen (G : NormalChartGeometry g χ)
    (S : Set (EuclideanHalfSpace (n + 1))) (hS : IsOpen S) :
    NormalChartGeometry g (χ.restrOpen S hS) := by
  have hsource := PartialDiffeomorph.restrOpen_source χ hS
  have hfun : ((χ.restrOpen S hS).toPartialEquiv : EuclideanHalfSpace (n + 1) → M) = χ.toPartialEquiv :=
    PartialDiffeomorph.coe_restrOpen χ hS
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ χ.source := (hsource ▸ hz).1
    dsimp only
    rw [hfun]
    exact G.time_inner z hz'
  · intro z hz v
    have hz' : z ∈ χ.source := (hsource ▸ hz).1
    dsimp only
    rw [hfun]
    exact G.spatial_time_inner z hz' v
  · intro z hz hzero ν hν
    have hz' : z ∈ χ.source := (hsource ▸ hz).1
    let P : (EuclideanHalfSpace (n + 1) → M) → Prop := fun f =>
      ∀ hB : f z ∈ (𝓡∂ (n + 1)).boundary M,
        ν ⟨f z, hB⟩ = -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) f z
          (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
    have hP : P χ.toPartialEquiv := fun _ => G.normal z hz' hzero ν hν
    have hP' : P (χ.restrOpen S hS).toPartialEquiv := (congrArg P hfun).mpr hP
    exact hP' _

theorem NormalChartGeometry.exists_restriction_target
    (G : NormalChartGeometry g χ) (U : TopologicalSpace.Opens M)
    {x : EuclideanHalfSpace (n + 1)} (hx : x ∈ χ.source) (hxU : χ x ∈ U) :
    ∃ χ' : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
        (EuclideanHalfSpace (n + 1)) M ω,
      NormalChartGeometry g χ' ∧ x ∈ χ'.source ∧ χ'.target ⊆ U ∧
      (χ' : EuclideanHalfSpace (n + 1) → M) = χ ∧ χ'.source ⊆ χ.source := by
  let S : Set (EuclideanHalfSpace (n + 1)) := χ.source ∩ χ ⁻¹' U
  have hS : IsOpen S := χ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage χ.open_source U.isOpen
  let χ' := χ.restrOpen S hS
  have hs : (χ'.source : Set (EuclideanHalfSpace (n + 1))) = χ.source ∩ S :=
    PartialDiffeomorph.restrOpen_source χ hS
  refine ⟨χ', G.restrOpen S hS, ?_, ?_, PartialDiffeomorph.coe_restrOpen χ hS, ?_⟩
  · rw [hs]
    exact ⟨hx, hx, hxU⟩
  · intro y hy
    have ht : (χ'.target : Set M) = χ.target ∩ χ.toPartialEquiv.symm ⁻¹' S :=
      PartialDiffeomorph.restrOpen_target χ hS
    have hy' := ht ▸ hy
    have hU : χ (χ.symm y) ∈ U := hy'.2.2
    have hr : χ (χ.symm y) = y := χ.right_inv hy'.1
    exact (congrArg (fun w : M => w ∈ U) hr).mp hU
  · intro z hz
    exact (hs ▸ hz).1

end ConformalPoisson

end RefPart_NormalChartRestriction

/- Interface support: NormalChartDataRestriction.lean, SHA256 3e8d0d7a7485b872b7be4b9c0344431d44b295fc8a837335f0cf0ec78339d78d -/
noncomputable section RefPart_NormalChartDataRestriction

/-! Keep the same actual normal chart, original labels and base while putting
its whole actual target in a prescribed open gauge neighborhood. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {g : Metric (n := n) (M := M)} {α : (𝓡∂ (n + 1)).boundary M}

theorem NormalChartData.exists_restriction_target (D : NormalChartData g α)
    (U : TopologicalSpace.Opens M) (hα : (α : M) ∈ U) :
    ∃ D' : NormalChartData g α, D'.chart.target ⊆ U ∧
      (D'.chart : EuclideanHalfSpace (n + 1) → M) = D.chart := by
  have hxU : D.chart (chartAt (EuclideanHalfSpace (n + 1)) (α : M) (α : M)) ∈ U := by
    rw [D.base_value]
    exact hα
  obtain ⟨χ, hG, hx, htarget, hfun, hsource⟩ :=
    D.geometry.exists_restriction_target U D.base_mem hxU
  let D' : NormalChartData g α :=
    { chart := χ
      geometry := hG
      labels :=
        { source := fun z hz => (congrArg (fun y : M =>
            y ∈ (extChartAt (𝓡∂ (n + 1)) (α : M)).source) (congrFun hfun z)).mpr
              (D.labels.source z (hsource hz))
          boundary_value := fun z hz hzero =>
            (congrFun hfun z).trans (D.labels.boundary_value z (hsource hz) hzero)
          boundary_coordinate := fun z hz hzero =>
            (congrArg (extChartAt (𝓡∂ (n + 1)) (α : M)) (congrFun hfun z)).trans
              (D.labels.boundary_coordinate z (hsource hz) hzero) }
      base_mem := hx
      base_value := (congrFun hfun _).trans D.base_value }
  exact ⟨D', htarget, hfun⟩

theorem exists_normalChartData_target
    (g : Metric (n := n) (M := M)) (U : TopologicalSpace.Opens M)
    (hg : MetricAnalyticOn g U) {α : (𝓡∂ (n + 1)).boundary M} (hα : (α : M) ∈ U) :
    ∃ D : NormalChartData g α, D.chart.target ⊆ U := by
  obtain ⟨D⟩ := exists_normalChartData g U hg hα
  obtain ⟨D', htarget, _⟩ := D.exists_restriction_target U hα
  exact ⟨D', htarget⟩
end ConformalPoisson

end RefPart_NormalChartDataRestriction

/- Interface support: NormalParameterChange.lean, SHA256 3a3219eaecb3e4894c70ed4aafe1e8886b463273e08b4ca0e1a7d3f74a7d4290 -/
noncomputable section RefPart_NormalParameterChange

/-! Actual analytic changes of normal parameters preserving time and spatial
slices. The boundary-identification lift has these properties by project proof. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ}

structure NormalParameterChange
    (η : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) ω) : Prop where
  time : ∀ z ∈ η.source, (η z).1 0 = z.1 0
  time_differential : ∀ z ∈ η.source,
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) η z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) =
        (show TangentSpace (𝓡∂ (n + 1)) (η z) from euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
  spatial_differential : ∀ z ∈ η.source, ∀ v : EuclideanSpace ℝ (Fin n),
    ∃ w : EuclideanSpace ℝ (Fin n),
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) η z
        (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)) =
          (show TangentSpace (𝓡∂ (n + 1)) (η z) from euclideanHalfSpaceBoundaryNormalEquiv n (w, 0))

theorem normalParameterChange_spatialLift
    (B : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ω) :
    NormalParameterChange (halfSpaceSpatialCoordinateLift B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [halfSpaceSpatialCoordinateLift_source] at hz
    exact halfSpaceSpatialCoordinateLift_time B hz
  · intro z hz
    rw [halfSpaceSpatialCoordinateLift_source] at hz
    exact halfSpaceSpatialCoordinateLift_time_differential B hz
  · intro z hz v
    rw [halfSpaceSpatialCoordinateLift_source] at hz
    exact ⟨fderiv ℝ B ((euclideanHalfSpaceBoundaryNormalEquiv n).symm z.1).1 v,
      halfSpaceSpatialCoordinateLift_mfderiv_apply B hz v 0⟩
end ConformalPoisson

end RefPart_NormalParameterChange

/- Interface support: NormalChartReparameterization.lean, SHA256 5d217b238aacddc7536beff5d37d7a03cefab90df3d2acf5aafe51c64fad20d6 -/
noncomputable section RefPart_NormalChartReparameterization

/-! An actual analytic change of spatial parameters preserving time retains
the SAME metric Gauss form, supplied normal and native DN interpretation. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  {η : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
    (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) ω}
  (C : NormalParameterChange η)
  (χ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M ω)

include C

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
theorem NormalParameterChange.comp_time_differential
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ η.source) (hχ : η z ∈ χ.source) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (χ ∘ η) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) =
        mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ (η z)
          (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  exact (mfderiv_comp_apply z
    (χ.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hχ)
    (η.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hz)
    (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))).trans
      (congrArg (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ (η z)) (C.time_differential z hz))

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
theorem NormalParameterChange.comp_spatial_differential
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ η.source) (hχ : η z ∈ χ.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ w : EuclideanSpace ℝ (Fin n),
      mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (χ ∘ η) z
        (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0)) =
          mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ (η z)
            (euclideanHalfSpaceBoundaryNormalEquiv n (w, 0)) := by
  obtain ⟨w, hw⟩ := C.spatial_differential z hz v
  exact ⟨w, (mfderiv_comp_apply z
    (χ.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hχ)
    (η.mdifferentiableAt (by decide : (ω : ℕ∞ω) ≠ 0) hz)
    (euclideanHalfSpaceBoundaryNormalEquiv n (v, 0))).trans
      (congrArg (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) χ (η z)) hw)⟩

theorem NormalChartGeometry.reparameterize
    {g : Metric (n := n) (M := M)} (G : NormalChartGeometry g χ) :
    NormalChartGeometry g (η.trans χ) := by
  have hfun : ((η.trans χ).toPartialEquiv : EuclideanHalfSpace (n + 1) → M) = χ ∘ η :=
    PartialDiffeomorph.coe_trans η χ
  have hdomain {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ (η.trans χ).source) :
      z ∈ η.source ∧ η z ∈ χ.source := by
    rw [PartialDiffeomorph.trans_source] at hz
    exact hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hp := hdomain hz
    have ht := C.comp_time_differential χ hp.1 hp.2
    dsimp only
    rw [hfun]
    exact (congrArg₂ (fun v w => g.inner (χ (η z)) v w) ht ht).trans
      (G.time_inner (η z) hp.2)
  · intro z hz v
    have hp := hdomain hz
    have ht := C.comp_time_differential χ hp.1 hp.2
    obtain ⟨w, hw⟩ := C.comp_spatial_differential χ hp.1 hp.2 v
    dsimp only
    rw [hfun]
    exact (congrArg₂ (fun v w => g.inner (χ (η z)) v w) hw ht).trans
      (G.spatial_time_inner (η z) hp.2 w)
  · intro z hz hzero ν hν
    have hp := hdomain hz
    have ht := C.comp_time_differential χ hp.1 hp.2
    have hηzero : (η z).1 0 = 0 := (C.time z hp.1).trans hzero
    let P : (EuclideanHalfSpace (n + 1) → M) → Prop := fun f =>
      ∀ hB : f z ∈ (𝓡∂ (n + 1)).boundary M,
        ν ⟨f z, hB⟩ = -mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) f z
          (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1))
    have hP : P (χ ∘ η) := fun _ =>
      (G.normal (η z) hp.2 hηzero ν hν).trans (congrArg Neg.neg ht.symm)
    have hP' : P (η.trans χ).toPartialEquiv := (congrArg P hfun).mpr hP
    exact hP' _
end ConformalPoisson

end RefPart_NormalChartReparameterization

/- Interface support: CommonNormalCharts.lean, SHA256 d668fd30cb41ee4604beb4da505059593ad8ba6512a5c9e7309fcee2efd5e09b -/
noncomputable section RefPart_CommonNormalCharts

/-! TWO actual analytic normal charts on ONE nonempty relative open source,
with exactly the prescribed boundary identification, actual Gauss/DN geometry,
and entire targets in the actual two chosen gauge neighborhoods. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

structure CommonNormalCharts
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁)
    (g₁ : Metric (n := n) (M := M₁)) (g₂ : Metric (n := n) (M := M₂))
    (U₁ : TopologicalSpace.Opens M₁) (U₂ : TopologicalSpace.Opens M₂) where
  chart₁ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M₁ ω
  chart₂ : PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (EuclideanHalfSpace (n + 1)) M₂ ω
  geometry₁ : NormalChartGeometry g₁ chart₁
  geometry₂ : NormalChartGeometry g₂ chart₂
  source_eq : chart₁.source = chart₂.source
  base_mem : chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁) ∈ chart₁.source
  base₁ : chart₁ (chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)) = (α : M₁)
  base₂ : chart₂ (chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁)) = (β α : M₂)
  target₁ : chart₁.target ⊆ U₁
  target₂ : chart₂.target ⊆ U₂
  boundary : ∀ z ∈ chart₁.source, z.1 0 = 0 →
    ∀ hB : chart₁ z ∈ (𝓡∂ (n + 1)).boundary M₁, chart₂ z = (β ⟨chart₁ z, hB⟩ : M₂)

theorem commonNormalCharts_of_data
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁)
    {g₁ : Metric (n := n) (M := M₁)} {g₂ : Metric (n := n) (M := M₂)}
    (U₁ : TopologicalSpace.Opens M₁) (U₂ : TopologicalSpace.Opens M₂)
    (D₁ : NormalChartData g₁ α) (D₂ : NormalChartData g₂ (β α))
    (hD₁ : D₁.chart.target ⊆ U₁) (hD₂ : D₂.chart.target ⊆ U₂)
    (B : BoundaryCoordinateChangeData β α) : Nonempty (CommonNormalCharts β α g₁ g₂ U₁ U₂) := by
  let η := halfSpaceSpatialCoordinateLift B.chart
  let ψ₂ := η.trans D₂.chart
  let S := D₁.chart.source ∩ ψ₂.source
  have hS : IsOpen S := D₁.chart.open_source.inter ψ₂.open_source
  let χ₁ := D₁.chart.restrOpen S hS
  let χ₂ := ψ₂.restrOpen S hS
  have hs₁ : (χ₁.source : Set (EuclideanHalfSpace (n + 1))) = S :=
    (PartialDiffeomorph.restrOpen_source D₁.chart hS).trans (inter_eq_right.mpr inter_subset_left)
  have hs₂ : (χ₂.source : Set (EuclideanHalfSpace (n + 1))) = S :=
    (PartialDiffeomorph.restrOpen_source ψ₂ hS).trans (inter_eq_right.mpr inter_subset_right)
  have hf₁ : (χ₁.toPartialEquiv : EuclideanHalfSpace (n + 1) → M₁) = D₁.chart.toPartialEquiv :=
    PartialDiffeomorph.coe_restrOpen D₁.chart hS
  have hf₂ : (χ₂.toPartialEquiv : EuclideanHalfSpace (n + 1) → M₂) = ψ₂.toPartialEquiv :=
    PartialDiffeomorph.coe_restrOpen ψ₂ hS
  have hbase := aligned_normalChart_base β α B D₂
  have hb : chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁) ∈ S := ⟨D₁.base_mem, hbase.1⟩
  have hG₂ : NormalChartGeometry g₂ ψ₂ :=
    NormalChartGeometry.reparameterize (normalParameterChange_spatialLift B.chart) D₂.chart D₂.geometry
  refine ⟨⟨χ₁, χ₂, D₁.geometry.restrOpen S hS, hG₂.restrOpen S hS, hs₁.trans hs₂.symm,
    (hs₁.symm ▸ hb), (congrFun hf₁ _).trans D₁.base_value,
    (congrFun hf₂ _).trans hbase.2, ?_, ?_, ?_⟩⟩
  · intro y hy
    have ht := PartialDiffeomorph.restrOpen_target D₁.chart hS
    exact hD₁ (ht ▸ hy).1
  · intro y hy
    have ht := PartialDiffeomorph.restrOpen_target ψ₂ hS
    have hyψ : y ∈ ψ₂.target := (ht ▸ hy).1
    rw [PartialDiffeomorph.trans_target] at hyψ
    exact hD₂ hyψ.1
  · intro z hz hzero hB
    have hzS : z ∈ S := hs₁ ▸ hz
    have h := common_normalChart_boundary_value β α B D₁.chart D₂.chart D₁.labels D₂.labels
      hzS.1 hzS.2 hzero
    let P : (EuclideanHalfSpace (n + 1) → M₁) → Prop := fun f =>
      ∀ hB : f z ∈ (𝓡∂ (n + 1)).boundary M₁, ψ₂ z = (β ⟨f z, hB⟩ : M₂)
    have hP : P D₁.chart.toPartialEquiv := fun _ => h
    have hP' : P χ₁.toPartialEquiv := (congrArg P hf₁).mpr hP
    exact (congrFun hf₂ z).trans (hP' hB)

theorem exists_commonNormalCharts
    (β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (α : (𝓡∂ (n + 1)).boundary M₁)
    (g₁ : Metric (n := n) (M := M₁)) (g₂ : Metric (n := n) (M := M₂))
    (U₁ : TopologicalSpace.Opens M₁) (U₂ : TopologicalSpace.Opens M₂)
    (hg₁ : MetricAnalyticOn g₁ U₁) (hg₂ : MetricAnalyticOn g₂ U₂)
    (hα₁ : (α : M₁) ∈ U₁) (hα₂ : (β α : M₂) ∈ U₂) :
    Nonempty (CommonNormalCharts β α g₁ g₂ U₁ U₂) := by
  obtain ⟨D₁, hD₁⟩ := exists_normalChartData_target g₁ U₁ hg₁ hα₁
  obtain ⟨D₂, hD₂⟩ := exists_normalChartData_target g₂ U₂ hg₂ hα₂
  obtain ⟨B⟩ := exists_boundaryCoordinateChangeData β α
  exact commonNormalCharts_of_data β α U₁ U₂ D₁ D₂ hD₁ hD₂ B
end ConformalPoisson

end RefPart_CommonNormalCharts

/- Interface support: CommonNormalCoefficients.lean, SHA256 5507e902628cd01007007e380f8a3d900b620ffc3c9eeb611ebe30c36fa95f23 -/
noncomputable section RefPart_CommonNormalCoefficients

/-! Bind the matrix recursion to the SAME actual paired normal charts.
The original chart/Gauss witnesses remain explicit in C. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.CommonNormalCharts
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]
  {β : Diffeomorph (𝓡 n) (𝓡 n) ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω}
  {α : (𝓡∂ (n + 1)).boundary M₁}
  {g₁ : Metric (n := n) (M := M₁)} {g₂ : Metric (n := n) (M := M₂)}
  {U₁ : TopologicalSpace.Opens M₁} {U₂ : TopologicalSpace.Opens M₂}
  (C : CommonNormalCharts β α g₁ g₂ U₁ U₂)

def coefficientDomain : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1)) :=
  ⟨C.chart₁.source, C.chart₁.open_source⟩

def metricField₁ : NormalMetricField C.coefficientDomain :=
  NormalMetricField.fromChart g₁ C.chart₁ C.coefficientDomain (fun _ hz => hz)

def metricField₂ : NormalMetricField C.coefficientDomain :=
  NormalMetricField.fromChart g₂ C.chart₂ C.coefficientDomain (fun _ hz => C.source_eq ▸ hz)

theorem metricField₁_analytic (hg : MetricAnalyticOn g₁ U₁)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ C.coefficientDomain) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω C.metricField₁.gram z ∧
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω C.metricField₁.inverse z := by
  have hU := C.target₁ (C.chart₁.map_source hz)
  exact ⟨normalTangentialGram_analyticAt g₁ C.chart₁ U₁ hg hz hU,
    normalTangentialInverse_analyticAt g₁ C.chart₁ U₁ hg hz hU⟩

theorem metricField₂_analytic (hg : MetricAnalyticOn g₂ U₂)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ C.coefficientDomain) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω C.metricField₂.gram z ∧
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ω C.metricField₂.inverse z := by
  have h₂ : z ∈ C.chart₂.source := C.source_eq ▸ hz
  have hU := C.target₂ (C.chart₂.map_source h₂)
  exact ⟨normalTangentialGram_analyticAt g₂ C.chart₂ U₂ hg h₂ hU,
    normalTangentialInverse_analyticAt g₂ C.chart₂ U₂ hg h₂ hU⟩

def boundaryDomain : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨EuclideanHalfSpace.boundaryParam n ⁻¹' C.coefficientDomain,
    C.coefficientDomain.isOpen.preimage EuclideanHalfSpace.continuous_boundaryParam⟩

def boundaryBase (_C : CommonNormalCharts β α g₁ g₂ U₁ U₂) : EuclideanSpace ℝ (Fin n) := extChartAt (𝓡 n) α α

theorem boundaryBase_map : EuclideanHalfSpace.boundaryParam n C.boundaryBase =
    chartAt (EuclideanHalfSpace (n + 1)) (α : M₁) (α : M₁) := by
  apply Subtype.ext
  rw [EuclideanHalfSpace.boundaryParam_coe, boundaryNormalBase_read α,
    euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam]
  rfl

theorem boundaryBase_mem : C.boundaryBase ∈ C.boundaryDomain := by
  change EuclideanHalfSpace.boundaryParam n C.boundaryBase ∈ C.chart₁.source
  rw [C.boundaryBase_map]
  exact C.base_mem

theorem boundaryDomain_map_source {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : W ⊆ C.boundaryDomain) :
    EuclideanHalfSpace.boundaryParam n '' W ⊆ C.coefficientDomain := by
  rintro z ⟨y, hy, rfl⟩
  exact hW hy
end ConformalPoisson.CommonNormalCharts

end RefPart_CommonNormalCoefficients

/- Interface support: ModelDirectionalDerivatives.lean, SHA256 d2912fded1b933cd93ff7deabe3f3e243736eac55c2b6996a9a200c6da9d7018 -/
noncomputable section RefPart_ModelDirectionalDerivatives

/-! Constant native directional derivatives on a model with corners. This
also applies to the product model used for spatial/frequency symbols. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def modelDirectionalDeriv (v : E) (f : H → F) (x : H) : F := mvfderiv I f x v

theorem model_constTangent_contMDiffAt (v : E) (x : H) (k : ℕ∞ω) :
    ContMDiffAt I I.tangent k
      (fun y : H => (⟨y, (show TangentSpace I y from v)⟩ : TangentBundle I H)) x := by
  apply (contMDiffAt_section_iff x).mpr
  simpa only [trivializationAt_model_space_apply] using
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, E) k (fun _ : H => v) x)

theorem modelDirectionalDeriv_contMDiffAt (v : E) {f : H → F} {x : H} {k m : ℕ∞ω}
    (hf : ContMDiffAt I 𝓘(ℝ, F) k f x) (hmk : m + 1 ≤ k) :
    ContMDiffAt I 𝓘(ℝ, F) m (modelDirectionalDeriv I v f) x := by
  have hd := hf.contMDiffAt_mvfderiv_apply
    (p := (⟨x, v⟩ : TangentBundle I H)) hmk
  exact hd.comp x (model_constTangent_contMDiffAt I v x m)

theorem modelDirectionalDeriv_eq_of_eventuallyEq (v : E) {f g : H → F} {x : H}
    (h : f =ᶠ[𝓝 x] g) : modelDirectionalDeriv I v f x = modelDirectionalDeriv I v g x :=
  congrArg (fun A => A v) (h.mvfderiv_eq (I := I))

theorem modelDirectionalDeriv_ambient (v : E) {G : E → F} {x : H}
    (hG : DifferentiableAt ℝ G (I x)) :
    modelDirectionalDeriv I v (G ∘ I) x = fderiv ℝ G (I x) v := by
  have hI : MDifferentiableAt I 𝓘(ℝ, E) I x :=
    (contMDiffAt_extChartAt (I := I) (n := 1) (x := x)).mdifferentiableAt one_ne_zero
  have h := mvfderiv_comp_apply_of_differentiableAt hG hI v
  have hIv : mvfderiv I I x v = v :=
    mvfderiv_apply_of_eventuallyEq_extChartAt (Filter.EventuallyEq.rfl) v
  exact h.trans (congrArg (fderiv ℝ G (I x)) hIv)

theorem model_exists_analytic_extension [CompleteSpace F] {f : H → F} {x : H}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ω f x) :
    ∃ G : E → F, AnalyticAt ℝ G (I x) ∧ f = G ∘ I := by
  have hc := contMDiffAt_iff_source.mp hf
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hc
  have hc' : ContDiffWithinAt ℝ ω (f ∘ I.symm) (range I) (I x) := hc
  obtain ⟨G, hbase, heq, hG⟩ := hc'.analyticWithinAt.exists_analyticAt
  refine ⟨G, hG, ?_⟩
  funext y
  have h := heq (mem_insert_of_mem (I x) (mem_range_self y))
  simpa only [Function.comp_apply, I.left_inv] using h
end ConformalPoisson

end RefPart_ModelDirectionalDerivatives

/- Interface support: ModelDirectionalSymmetry.lean, SHA256 85795ffc1594a58be417c1b55884c4e1cda480aab00c821f1b46cf2742a0f2f0 -/
noncomputable section RefPart_ModelDirectionalSymmetry

/-! Constant native derivatives commute for actual analytic functions on
models with corners, using a genuine analytic ambient representative. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem modelDirectionalDeriv_ambient_eventually (v : E) {G : E → F} {x : H}
    (hG : AnalyticAt ℝ G (I x)) :
    modelDirectionalDeriv I v (G ∘ I) =ᶠ[𝓝 x] (fun y => fderiv ℝ G (I y) v) := by
  have hn := I.continuous.continuousAt.eventually hG.eventually_analyticAt
  filter_upwards [hn] with y hy
  exact modelDirectionalDeriv_ambient I v hy.differentiableAt

theorem modelDirectionalDeriv_ambient_second (u v : E) {G : E → F} {x : H}
    (hG : AnalyticAt ℝ G (I x)) :
    modelDirectionalDeriv I v (modelDirectionalDeriv I u (G ∘ I)) x =
      fderiv ℝ (fderiv ℝ G) (I x) v u := by
  have hDu : DifferentiableAt ℝ (fun y => fderiv ℝ G y u) (I x) :=
    hG.fderiv.differentiableAt.clm_apply (differentiableAt_const u)
  have he := modelDirectionalDeriv_eq_of_eventuallyEq I v
    (modelDirectionalDeriv_ambient_eventually I u hG)
  calc
    _ = modelDirectionalDeriv I v ((fun y => fderiv ℝ G y u) ∘ I) x := he
    _ = fderiv ℝ (fun y => fderiv ℝ G y u) (I x) v := modelDirectionalDeriv_ambient I v hDu
    _ = _ := by
      rw [fderiv_clm_apply hG.fderiv.differentiableAt (differentiableAt_const u)]
      simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply]

theorem modelDirectionalDeriv_comm (u v : E) {f : H → F} {x : H}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ω f x) :
    modelDirectionalDeriv I u (modelDirectionalDeriv I v f) x =
      modelDirectionalDeriv I v (modelDirectionalDeriv I u f) x := by
  obtain ⟨G, hG, hrepr⟩ := model_exists_analytic_extension I hf
  rw [hrepr, modelDirectionalDeriv_ambient_second I v u hG,
    modelDirectionalDeriv_ambient_second I u v hG]
  exact (hG.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq u v
end ConformalPoisson

end RefPart_ModelDirectionalSymmetry

/- Interface support: NormalAnalyticJets.lean, SHA256 53ed40d91ef3e36bb0f31b16aa47eb78d27f686c73554d9365309e1ac2c6e3ae -/
noncomputable section RefPart_NormalAnalyticJets

/-! Fixed-domain analytic native normal jets and commutation with constant
spatial directions. These are project calculus results, not symbol inputs. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalJet_analyticOn {f : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ω f S) (k : ℕ) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ω (normalJet k f) S := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro z hz
    exact (normalDeriv_contMDiffAt ((ih z hz).contMDiffAt (hS.mem_nhds hz))
      (le_top : (ω : ℕ∞ω) + 1 ≤ ω)).contMDiffWithinAt

theorem modelDirectionalDeriv_analyticOn
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (v : E) {f : H → F} {S : Set H} (hS : IsOpen S)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ω f S) :
    ContMDiffOn I 𝓘(ℝ, F) ω (modelDirectionalDeriv I v f) S := by
  intro x hx
  exact (modelDirectionalDeriv_contMDiffAt I v
    ((hf x hx).contMDiffAt (hS.mem_nhds hx)) (le_top : (ω : ℕ∞ω) + 1 ≤ ω)).contMDiffWithinAt

theorem normalJet_directional_comm_eqOn [CompleteSpace F]
    (v : EuclideanSpace ℝ (Fin (n + 1))) {f : EuclideanHalfSpace (n + 1) → F}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F) ω f S) (k : ℕ) :
    EqOn (normalJet k (modelDirectionalDeriv (𝓡∂ (n + 1)) v f))
      (modelDirectionalDeriv (𝓡∂ (n + 1)) v (normalJet k f)) S := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
    intro z hz
    have he := normalDeriv_eq_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hS.mem_nhds hz) ih)
    have hk := ((normalJet_analyticOn hS hf k) z hz).contMDiffAt (hS.mem_nhds hz)
    have hc := modelDirectionalDeriv_comm (𝓡∂ (n + 1))
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) v hk
    exact he.trans hc
end ConformalPoisson

end RefPart_NormalAnalyticJets

/- Interface support: NormalComplexJets.lean, SHA256 2182b39f948455d0759fd0219d8166ee31481d3bdb9f2a81dc5602af9ceec47d -/
noncomputable section RefPart_NormalComplexJets

/-! Concrete real-to-complex and complex-product native normal-jet APIs for
the actual homogeneous symbols. Their base derivatives remain REAL native
manifold derivatives; no complex structure on the spatial manifold is used. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

theorem normalJet_complex_mul_eqOn
    {f g : EuclideanHalfSpace (n + 1) → ℂ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ f S)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ g S) (k : ℕ) :
    EqOn (normalJet k (fun z => f z * g z))
      (fun z => ∑ r ∈ Finset.range (k + 1),
        k.choose r • (normalJet r f z * normalJet (k - r) g z)) S := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    normalJet_bilinear_eqOn (ContinuousLinearMap.mul ℝ ℂ) hS hf hg k

theorem normalJet_ofReal_eqOn {f : EuclideanHalfSpace (n + 1) → ℝ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f S) (k : ℕ) :
    EqOn (normalJet k (fun z => (f z : ℂ))) (fun z => Complex.ofReal (normalJet k f z)) S := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    normalJet_clm_eqOn Complex.ofRealCLM hS hf k

theorem normalJet_complex_const_mul_eqOn (c : ℂ)
    {f : EuclideanHalfSpace (n + 1) → ℂ}
    {S : Set (EuclideanHalfSpace (n + 1))} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ f S) (k : ℕ) :
    EqOn (normalJet k (fun z => c * f z)) (fun z => c * normalJet k f z) S := by
  simpa only [Function.comp_def, ContinuousLinearMap.mul_apply'] using
    normalJet_clm_eqOn (ContinuousLinearMap.mul ℝ ℂ c) hS hf k
end ConformalPoisson

end RefPart_NormalComplexJets

/- Interface support: DegreeZeroAlgebra.lean, SHA256 dbe0cc6e9eede16ad34571e5e4412e6555c96643fbfc621a24c618e96485f51a -/
noncomputable section RefPart_DegreeZeroAlgebra

/-! Raw complex factorization algebra retaining the unrestricted trace E.
This is a project consequence of the primitive degree-zero recurrence. -/

namespace ConformalPoisson

theorem degreeZero_complex_algebra (s a τ : ℝ) (hs : s ≠ 0) (b U : ℂ)
    (hraw : (Complex.ofReal (2 * s)) * b =
      -Complex.ofReal (a / (2 * s)) + Complex.ofReal (τ / 2) * Complex.ofReal s + U) :
    b = (-1 / 4 : ℝ) • Complex.ofReal (a / s ^ 2 - τ) +
      Complex.ofReal ((2 * s)⁻¹) * U := by
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  apply mul_left_cancel₀ (show Complex.ofReal (2 * s) ≠ 0 by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hs))
  rw [hraw, Complex.real_smul]
  push_cast
  field_simp
  ring
end ConformalPoisson

end RefPart_DegreeZeroAlgebra

/- Interface support: DegreeZeroRemainder.lean, SHA256 8d489313fbca4932de10d4c92a213a71207c4d86a460401ec5070fbbca677e17 -/
noncomputable section RefPart_DegreeZeroRemainder

/-! The actual degree-zero tangential remainder: the composition term minus
the first-order tangential symbol, divided by twice the actual principal root. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def inverseTwicePrincipal (F : NormalMetricField S) (ξ : Fin n → ℝ) :
    EuclideanHalfSpace (n + 1) → ℝ :=
  (1 / 2 : ℝ) • (fun z => (F.principal ξ z)⁻¹)

theorem inverseTwicePrincipal_apply (F : NormalMetricField S) (ξ : Fin n → ℝ)
    (z : EuclideanHalfSpace (n + 1)) : F.inverseTwicePrincipal ξ z = (2 * F.principal ξ z)⁻¹ := by
  change (1 / 2 : ℝ) * (F.principal ξ z)⁻¹ = (2 * F.principal ξ z)⁻¹
  rw [mul_inv_rev, one_div]
  exact mul_comm _ _

theorem inverseTwicePrincipal_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (F.inverseTwicePrincipal ξ) S := by
  let C : ℝ →L[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  exact C.contDiff.contMDiff.comp_contMDiffOn (F.inverse_principal_smooth ξ hξ)

theorem inverseTwicePrincipal_jets_eq (F₁ F₂ : NormalMetricField S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z) :
    ∀ r ≤ L, normalJet r (F₁.inverseTwicePrincipal ξ) z = normalJet r (F₂.inverseTwicePrincipal ξ) z := by
  intro r hr
  unfold inverseTwicePrincipal
  rw [normalJet_const_smul, normalJet_const_smul]
  exact congrArg (fun v : ℝ => (1 / 2 : ℝ) • v) (inverse_principal_jets_eq F₁ F₂ hz ξ hξ L hA r hr)

def degreeZeroRemainder (F : NormalMetricField S) (ξ : Fin n → ℝ)
    (S₀ Q₁ : EuclideanHalfSpace (n + 1) → ℂ) : EuclideanHalfSpace (n + 1) → ℂ :=
  fun z => Complex.ofReal (F.inverseTwicePrincipal ξ z) * (S₀ z - Q₁ z)

theorem degreeZeroRemainder_smooth (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {S₀ Q₁ : EuclideanHalfSpace (n + 1) → ℂ}
    (hS₀ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ S₀ S)
    (hQ₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ Q₁ S) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ (F.degreeZeroRemainder ξ S₀ Q₁) S := by
  have hc : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞
      (Complex.ofReal ∘ F.inverseTwicePrincipal ξ) S :=
    Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn (F.inverseTwicePrincipal_smooth ξ hξ)
  exact normalBilinear_contMDiffOn (ContinuousLinearMap.mul ℝ ℂ) hc (hS₀.sub hQ₁)

theorem degreeZeroRemainder_jets_eq (F₁ F₂ : NormalMetricField S)
    (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {S₀₁ Q₁₁ S₀₂ Q₁₂ : EuclideanHalfSpace (n + 1) → ℂ}
    (hS₀₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ S₀₁ S)
    (hQ₁₁ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ Q₁₁ S)
    (hS₀₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ S₀₂ S)
    (hQ₁₂ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, ℂ) ∞ Q₁₂ S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) (L : ℕ)
    (hA : ∀ r ≤ L, normalJet r F₁.inverse z = normalJet r F₂.inverse z)
    (hS₀ : ∀ r ≤ L, normalJet r S₀₁ z = normalJet r S₀₂ z)
    (hQ₁ : ∀ r ≤ L, normalJet r Q₁₁ z = normalJet r Q₁₂ z) :
    normalJet L (F₁.degreeZeroRemainder ξ S₀₁ Q₁₁) z =
      normalJet L (F₂.degreeZeroRemainder ξ S₀₂ Q₁₂) z := by
  have hc₁ := Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn (F₁.inverseTwicePrincipal_smooth ξ hξ)
  have hc₂ := Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn (F₂.inverseTwicePrincipal_smooth ξ hξ)
  apply normalJet_bilinear_congr S.isOpen hc₁ hc₂ (hS₀₁.sub hQ₁₁) (hS₀₂.sub hQ₁₂)
    (ContinuousLinearMap.mul ℝ ℂ) hz L
  · intro r hr
    have h₁ := normalJet_ofReal_eqOn S.isOpen (F₁.inverseTwicePrincipal_smooth ξ hξ) r hz
    have h₂ := normalJet_ofReal_eqOn S.isOpen (F₂.inverseTwicePrincipal_smooth ξ hξ) r hz
    exact h₁.trans ((congrArg Complex.ofReal (inverseTwicePrincipal_jets_eq F₁ F₂ hz ξ hξ L hA r hr)).trans h₂.symm)
  · intro r hr
    have h₁ := normalJet_sub_eqOn S.isOpen hS₀₁ hQ₁₁ r hz
    have h₂ := normalJet_sub_eqOn S.isOpen hS₀₂ hQ₁₂ r hz
    exact h₁.trans ((congrArg₂ (· - ·) (hS₀ r hr) (hQ₁ r hr)).trans h₂.symm)
end ConformalPoisson.NormalMetricField

end RefPart_DegreeZeroRemainder

/- Interface support: NativeDegreeZeroFormula.lean, SHA256 1286676059105ec41e28ab22ca9d1ddcb0ca0d3f262a8003f55dd52ce2b45edb -/
noncomputable section RefPart_NativeDegreeZeroFormula

/-! Substitute the actual negative principal branch into the primitive raw
degree-zero recurrence. The -1/4 K identity is a PROJECT consequence. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

theorem normalDeriv_negative_principal (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    {b : EuclideanHalfSpace (n + 1) → ℂ}
    (hbranch : EqOn b ((-1 : ℝ) • (Complex.ofReal ∘ F.principal ξ)) S)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ S) :
    normalDeriv b z = -Complex.ofReal (normalDeriv (F.principal ξ) z) := by
  have hb := normalJet_eqOn S.isOpen hbranch 1 hz
  rw [normalJet_const_smul] at hb
  have hc := normalJet_ofReal_eqOn S.isOpen (F.principal_smooth ξ hξ) 1 hz
  have he := hb.trans (congrArg (fun v : ℂ => (-1 : ℝ) • v) hc)
  simpa only [normalJet_succ, normalJet_zero, neg_one_smul] using he

theorem degreeZero_relation_of_raw (F : NormalMetricField S) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (bPrincipal bDegreeZero S₀ Q₁ : EuclideanHalfSpace (n + 1) → ℂ)
    (hbranch : EqOn bPrincipal ((-1 : ℝ) • (Complex.ofReal ∘ F.principal ξ)) S)
    (hraw : ∀ z ∈ S, Complex.ofReal (2 * F.principal ξ z) * bDegreeZero z =
      normalDeriv bPrincipal z - Complex.ofReal (F.tau z / 2) * bPrincipal z + S₀ z - Q₁ z) :
    EqOn bDegreeZero
      ((-1 / 4 : ℝ) • (Complex.ofReal ∘ F.KQuadratic ξ) + F.degreeZeroRemainder ξ S₀ Q₁) S := by
  intro z hz
  have hp : bPrincipal z = -Complex.ofReal (F.principal ξ z) := by
    simpa only [Pi.smul_apply, Function.comp_apply, neg_one_smul] using hbranch hz
  have hr := hraw z hz
  rw [F.normalDeriv_negative_principal ξ hξ hbranch hz, hp, F.normalDeriv_principal ξ hξ hz] at hr
  have hrec : Complex.ofReal (2 * F.principal ξ z) * bDegreeZero z =
      -Complex.ofReal (normalMatrixQuadratic (normalDeriv F.inverse z) ξ / (2 * F.principal ξ z)) +
      Complex.ofReal (F.tau z / 2) * Complex.ofReal (F.principal ξ z) + (S₀ z - Q₁ z) := by
    simpa only [mul_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_assoc] using hr
  have he := degreeZero_complex_algebra (F.principal ξ z)
    (normalMatrixQuadratic (normalDeriv F.inverse z) ξ) (F.tau z)
    (F.principal_pos ξ hξ z hz).ne' (bDegreeZero z) (S₀ z - Q₁ z) hrec
  change bDegreeZero z = (-1 / 4 : ℝ) • Complex.ofReal (F.KQuadratic ξ z) +
    Complex.ofReal (F.inverseTwicePrincipal ξ z) * (S₀ z - Q₁ z)
  rw [F.KQuadratic_formula ξ hξ hz, F.inverseTwicePrincipal_apply ξ z]
  exact he
end ConformalPoisson.NormalMetricField

end RefPart_NativeDegreeZeroFormula

/- Interface support: NormalMetricFieldRestriction.lean, SHA256 fd09ce9075b678f356450e2df929c0c7a4154aae0e6a2aff577860a6769aa24a -/
noncomputable section RefPart_NormalMetricFieldRestriction

/-! Restrict certificates to a smaller open source while retaining the
EXACT SAME coefficient functions and their actual native derivatives. -/

open Bundle Set TauCeti
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson.NormalMetricField
variable {n : ℕ} {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

def restrict (F : NormalMetricField S) (U : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1)))
    (hU : U ≤ S) : NormalMetricField U where
  gram := F.gram
  inverse := F.inverse
  gram_smooth := F.gram_smooth.mono hU
  inverse_smooth := F.inverse_smooth.mono hU
  gram_posDef := fun z hz => F.gram_posDef z (hU hz)
  inverse_posDef := fun z hz => F.inverse_posDef z (hU hz)
  gram_inverse := fun _ hz => F.gram_inverse (hU hz)
  inverse_gram := fun _ hz => F.inverse_gram (hU hz)

@[simp] theorem restrict_gram (F : NormalMetricField S)
    (U : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))) (hU : U ≤ S) :
    (F.restrict U hU).gram = F.gram := rfl

@[simp] theorem restrict_inverse (F : NormalMetricField S)
    (U : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))) (hU : U ≤ S) :
    (F.restrict U hU).inverse = F.inverse := rfl
end ConformalPoisson.NormalMetricField

end RefPart_NormalMetricFieldRestriction

/- Interface support: NativeSymbolDefinitions.lean, SHA256 0e1967a6cd8b55702146c601393b733f0ee0524b4d491fa95f09f7391b8f1759 -/
noncomputable section RefPart_NativeSymbolDefinitions

/-! ACTUAL differential operators and finite composition sum for homogeneous
left symbols. Indices r>=0 have degree 1-r; D_x=-i partial_x is accounted
for by (-i)^|alpha| in the composition coefficient. No symbol analyticity,
boundary metric jet, germ or seed is stipulated here. -/

open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ}

abbrev NativeSymbol (n : ℕ) := (Fin n → ℝ) → EuclideanHalfSpace (n + 1) → ℂ

def symbolBaseDeriv (i : Fin n) (b : NativeSymbol n) : NativeSymbol n :=
  fun ξ => modelDirectionalDeriv (𝓡∂ (n + 1))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single i 1)) (b ξ)

def symbolFrequencyDeriv (i : Fin n) (b : NativeSymbol n) : NativeSymbol n :=
  fun ξ z => fderiv ℝ (fun η => b η z) ξ (Pi.single i 1)

def symbolMultiDeriv (D : Fin n → NativeSymbol n → NativeSymbol n)
    (α : Fin n → ℕ) (b : NativeSymbol n) : NativeSymbol n :=
  (List.finRange n).foldl (fun f i => (D i)^[α i] f) b

def symbolCompositionRemainder (b : ℕ → NativeSymbol n) (r : ℕ) : NativeSymbol n :=
  fun ξ z => ∑ p ∈ Finset.range (r + 1), ∑ q ∈ Finset.range (r + 1),
    if p + q ≤ r + 1 then
      ∑ α ∈ Finset.Nat.antidiagonalTuple n (r + 1 - (p + q)),
        ((-Complex.I) ^ (∑ i, α i) / ((∏ i, Nat.factorial (α i) : ℕ) : ℂ)) *
          symbolMultiDeriv symbolFrequencyDeriv α (b p) ξ z *
          symbolMultiDeriv symbolBaseDeriv α (b q) ξ z
    else 0

def SymbolContMDiffOn (S : Set (EuclideanHalfSpace (n + 1))) (k : ℕ∞ω) (b : NativeSymbol n) : Prop :=
  ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, ℂ) k
    (fun p : ModelProd (EuclideanHalfSpace (n + 1)) (Fin n → ℝ) => b p.2 p.1)
    (S ×ˢ {ξ | ξ ≠ 0})

def tangentialMatrixDeriv (i : Fin n)
    (A : EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ) :
    EuclideanHalfSpace (n + 1) → Matrix (Fin n) (Fin n) ℝ :=
  modelDirectionalDeriv (𝓡∂ (n + 1))
    (euclideanHalfSpaceBoundaryParam n (EuclideanSpace.single i 1)) A

namespace NormalMetricField
variable {S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1))}

/-- The actual tangential first-order symbol, in the Jacobi trace form of
`partial log det G = trace(A partial G)`. No normal derivatives occur. -/
def firstOrderSymbol (F : NormalMetricField S) : NativeSymbol n :=
  fun ξ z => -Complex.I * Complex.ofReal
    (∑ a, (∑ b, (tangentialMatrixDeriv b F.inverse z b a +
      (1 / 2 : ℝ) * F.inverse z b a *
        metricJetTrace (F.inverse z) (tangentialMatrixDeriv b F.gram z))) * ξ a)

/-- Raw homogeneous components, as an ordinary mathematical data object.
The analytical source must construct this for the ACTUAL native coefficients.
There is deliberately no higher-jet/remainder/germ/seed conclusion. -/
structure RawSymbolFamily (F : NormalMetricField S) where
  component : ℕ → NativeSymbol n
  smooth : ∀ r, SymbolContMDiffOn S ∞ (component r)
  homogeneous : ∀ r z, z ∈ S → ∀ ξ : Fin n → ℝ, ξ ≠ 0 → ∀ t : ℝ, 0 < t →
    component r (t • ξ) z = (t : ℂ) ^ (1 - (r : ℤ)) * component r ξ z
  principal : ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    EqOn (component 0 ξ) ((-1 : ℝ) • (Complex.ofReal ∘ F.principal ξ)) S
  recurrence : ∀ r ξ, ξ ≠ 0 → ∀ z, z ∈ S →
    Complex.ofReal (2 * F.principal ξ z) * component (r + 1) ξ z =
      normalDeriv (component r ξ) z - Complex.ofReal (F.tau z / 2) * component r ξ z +
      symbolCompositionRemainder component r ξ z - (if r = 0 then F.firstOrderSymbol ξ z else 0)

theorem RawSymbolFamily.degreeZero_relation {F : NormalMetricField S} (B : RawSymbolFamily F)
    (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) :
    EqOn (B.component 1 ξ) ((-1 / 4 : ℝ) • (Complex.ofReal ∘ F.KQuadratic ξ) +
      F.degreeZeroRemainder ξ (symbolCompositionRemainder B.component 0 ξ) (F.firstOrderSymbol ξ)) S := by
  apply F.degreeZero_relation_of_raw ξ hξ (B.component 0 ξ) (B.component 1 ξ)
    (symbolCompositionRemainder B.component 0 ξ) (F.firstOrderSymbol ξ) (B.principal ξ hξ)
  intro z hz
  simpa only [Nat.zero_add, ite_true] using B.recurrence 0 ξ hξ z hz
end NormalMetricField
end ConformalPoisson

end RefPart_NativeSymbolDefinitions

/- Interface support: PositiveGaugeCutoff.lean, SHA256 75baebefd9de0413ec6bb3aa15a33a0d7fa8e29399ca472e85a22f875fa8b9ca -/
noncomputable section RefPart_PositiveGaugeCutoff

/-! Positive global gauges which agree with a given local boundary solution near a point. -/


open Set Filter
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- A chart bump extends a locally positive boundary solution to a globally positive gauge. -/
theorem exists_positive_gauge_agreeing_near
    (w : M → ℝ) (hw : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ w)
    (x : (𝓡∂ (n + 1)).boundary M) (V : TopologicalSpace.Opens M) (hx : (x : M) ∈ V)
    (htrace : ∀ z : (𝓡∂ (n + 1)).boundary M, (z : M) ∈ V → w z = 1) :
    ∃ c : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c ∧ (∀ z, 0 < c z) ∧
      (∀ z : (𝓡∂ (n + 1)).boundary M, c z = 1) ∧
      ∃ W : TopologicalSpace.Opens M, (x : M) ∈ W ∧ (W : Set M) ⊆ V ∧ EqOn c w W := by
  let A : Set M := (V : Set M) ∩ {z | 0 < w z}
  have hA : IsOpen A := V.isOpen.inter (isOpen_lt continuous_const hw.continuous)
  have hxA : (x : M) ∈ A := ⟨hx, by change 0 < w x; rw [htrace x hx]; exact zero_lt_one⟩
  obtain ⟨b, _, hbA⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡∂ (n + 1)) (x : M)).mem_iff.mp
    (hA.mem_nhds hxA)
  let c : M → ℝ := fun z => 1 + b z * (w z - 1)
  have hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c :=
    contMDiff_const.add (b.contMDiff.mul (hw.sub contMDiff_const))
  have hpos (z : M) : 0 < c z := by
    by_cases hb : b z = 0
    · simp only [c, hb, zero_mul, add_zero, zero_lt_one]
    · have hwpos := (hbA (subset_tsupport b hb)).2
      have hbpos : 0 < b z := lt_of_le_of_ne b.nonneg (Ne.symm hb)
      have hcomp : 0 ≤ 1 - b z := sub_nonneg.mpr b.le_one
      have h := add_pos_of_pos_of_nonneg (mul_pos hbpos hwpos) hcomp
      have heq : c z = b z * w z + (1 - b z) := by dsimp only [c]; ring
      rw [heq]
      exact h
  have hcb (z : (𝓡∂ (n + 1)).boundary M) : c z = 1 := by
    by_cases hb : b z = 0
    · simp only [c, hb, zero_mul, add_zero]
    · have hzV := (hbA (subset_tsupport b hb)).1
      simp only [c, htrace z hzV, sub_self, mul_zero, add_zero]
  let W : TopologicalSpace.Opens M :=
    ⟨interior {z | b z = 1} ∩ A, isOpen_interior.inter hA⟩
  have hxW : (x : M) ∈ W := ⟨mem_interior_iff_mem_nhds.mpr b.eventuallyEq_one, hxA⟩
  refine ⟨c, hc, hpos, hcb, W, hxW, fun z hz => hz.2.1, ?_⟩
  intro z hz
  have hb : b z = 1 := interior_subset hz.1
  simp only [c, hb, one_mul]
  ring

end ConformalPoisson

end RefPart_PositiveGaugeCutoff

/- Interface support: NativeRegularity.lean, SHA256 170def25cfc398e7dac8685094547553a549eb3da168d41fd229eca137c45b2f -/
noncomputable section RefPart_NativeRegularity

/-! Smoothness of the actual native forcing of a smooth function. -/


open Bundle
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem contMDiff_schrodinger (g : Metric (n := n) (M := M)) (q w : M → ℝ)
    (hq : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q)
    (hw : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ w) :
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (schrodinger g q w) := by
  let : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M => TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)
  have hL : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞
      (TauCeti.Manifold.laplaceBeltrami (𝓡∂ (n + 1)) w) :=
    TauCeti.Manifold.contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞)
      (by simp) (by simp) hw
  exact hL.neg.add (hq.mul hw)

end ConformalPoisson

end RefPart_NativeRegularity

/- Interface support: GaugeSolutions.lean, SHA256 ac29346367a664799d49f5047cc5c7e264850627974ae354d4e93c29efc9c1ef -/
noncomputable section RefPart_GaugeSolutions

/-! Actual solution and zero-boundary kernel transport through the conformal gauge. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem contMDiff_conformalGaugePotential
    (g : Metric (n := n) (M := M)) (q c : M → ℝ)
    (hq : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x) :
    ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (conformalGaugePotential g q c) := by
  exact ((hc.mul (hc.rpow_const_of_ne (fun x => (hcpos x).ne') _)).inv₀
    (fun x => mul_ne_zero (hcpos x).ne' (Real.rpow_pos_of_pos (hcpos x) _).ne')).mul
      (contMDiff_schrodinger g q c hq hc)

/-- A gauged homogeneous function yields an original homogeneous function by multiplication. -/
theorem conformalGauge_solution_mul
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c v : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v)
    (hLv : ∀ x ∈ (𝓡∂ (n + 1)).interior M,
      schrodinger (conformalGaugeMetric g c hc hcpos) (conformalGaugePotential g q c) v x = 0) :
    ∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q (c * v) x = 0 := by
  intro x hx
  have h := (schrodinger_conformalGauge hdim g q c v hc hcpos hv x).symm.trans (hLv x hx)
  exact (mul_eq_zero.mp h).resolve_left
    (inv_ne_zero (mul_ne_zero (hcpos x).ne' (Real.rpow_pos_of_pos (hcpos x) _).ne'))

/-- Nonresonance is transported for arbitrary positive smooth gauges, independently of their trace. -/
theorem Nonresonant.conformalGauge
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hNR : Nonresonant g q) :
    Nonresonant (conformalGaugeMetric g c hc hcpos) (conformalGaugePotential g q c) := by
  intro v hv
  have hsol : IsDirichletSolution g q 0 (c * v) := by
    refine ⟨hc.mul hv.1, conformalGauge_solution_mul hdim g q c v hc hcpos hv.1 hv.2.1, ?_⟩
    intro x
    simp only [Pi.mul_apply, hv.2.2 x, Pi.zero_apply, mul_zero]
  have hzero := hNR (c * v) hsol
  funext x
  have h := congrFun hzero x
  change c x * v x = 0 at h
  exact (mul_eq_zero.mp h).resolve_left (hcpos x).ne'

/-- Divide an actual solution by the gauge, retaining its full boundary datum when c=1 there. -/
theorem IsDirichletSolution.div_conformalGauge
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c u : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hcb : ∀ x : (𝓡∂ (n + 1)).boundary M, c x = 1)
    {f : ((𝓡∂ (n + 1)).boundary M) → ℝ} (hu : IsDirichletSolution g q f u) :
    IsDirichletSolution (conformalGaugeMetric g c hc hcpos) (conformalGaugePotential g q c)
      f (u / c) := by
  have hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ (u / c) := hu.1.div₀ hc (fun x => (hcpos x).ne')
  have hmul : c * (u / c) = u := by
    funext x
    exact mul_div_cancel₀ (u x) (hcpos x).ne'
  refine ⟨hv, fun x hx => ?_, fun x => ?_⟩
  · rw [schrodinger_conformalGauge hdim g q c (u / c) hc hcpos hv x, hmul, hu.2.1 x hx, mul_zero]
  · simp only [Pi.div_apply, hcb x, div_one, hu.2.2 x]

end ConformalPoisson

end RefPart_GaugeSolutions

/- Interface support: NativeInteriorTopology.lean, SHA256 dce1b171c06658a43b1a7ee762eb26aff68f95978d48582d5f19ec1e70b70ccf -/
noncomputable section RefPart_NativeInteriorTopology

/-! The actual interior is dense, including in every neighborhood of a boundary point. -/

open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem dense_nativeInterior : Dense ((𝓡∂ (n + 1)).interior M) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin (n + 1))) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin (n + 1))) := ⟨rfl⟩
  simpa only [(𝓡∂ (n + 1)).compl_boundary] using
    (TauCeti.isNullSet_boundary (I := 𝓡∂ (n + 1)) (M := M)).dense_compl

end ConformalPoisson

end RefPart_NativeInteriorTopology

/- Interface support: NativeEquationBoundary.lean, SHA256 1bfe933cee28ea560d65e24c54922148197ef9cc6da2571487cc87b436b11e76 -/
noncomputable section RefPart_NativeEquationBoundary

/-! The smooth homogeneous equation extends from the dense interior to the boundary. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem schrodinger_eq_zero_of_interior
    (g : Metric (n := n) (M := M)) (q u : M → ℝ)
    (hq : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ q) (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u)
    (hLu : ∀ x ∈ (𝓡∂ (n + 1)).interior M, schrodinger g q u x = 0) :
    schrodinger g q u = 0 :=
  Continuous.ext_on (dense_nativeInterior (n := n) (M := M))
    (contMDiff_schrodinger g q u hq hu).continuous continuous_const hLu

end ConformalPoisson

end RefPart_NativeEquationBoundary

/- Interface support: LocalPotentialGauge.lean, SHA256 8708076b2888ffbdf63ea76e0df78e96fb793fab4050f7367450aff7980d8db1 -/
noncomputable section RefPart_LocalPotentialGauge

/-!
Actual positive gauges killing the independent potential near an observed boundary point.
The analytic regularity premise is the approved forward input; the cutoff and
operator-locality inferences are project proofs.
-/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

/-- A shared local gauge witness, with its actual solution and allowed neighborhood fixed. -/
structure LocalSolutionGauge (g : Metric (n := n) (M := M)) (q : M → ℝ)
    (S : DirichletSolver g q) (f : ((𝓡∂ (n + 1)).boundary M) → ℝ)
    (x : (𝓡∂ (n + 1)).boundary M) (V : TopologicalSpace.Opens M) where
  multiplier : M → ℝ
  smooth : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ multiplier
  positive : ∀ z, 0 < multiplier z
  boundary_one : ∀ z : (𝓡∂ (n + 1)).boundary M, multiplier z = 1
  neighborhood : TopologicalSpace.Opens M
  point_mem : (x : M) ∈ neighborhood
  subset_allowed : (neighborhood : Set M) ⊆ V
  analytic_local : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω multiplier neighborhood
  agrees_solution : EqOn multiplier (S.solve f) neighborhood
  potential_zero : ∀ z ∈ neighborhood, conformalGaugePotential g q multiplier z = 0

theorem exists_local_potential_zero_gauge
    (hRegularity : BoundaryAnalyticRegularityAssumption (n := n) (M := M))
    (g : Metric (n := n) (M := M) ω) (q : M → ℝ)
    (hq : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω q)
    (S : DirichletSolver (g.ofLE (by decide)) q)
    (f : ((𝓡∂ (n + 1)).boundary M) → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f)
    (x : (𝓡∂ (n + 1)).boundary M) (V : TopologicalSpace.Opens M) (hx : (x : M) ∈ V)
    (hf₁ : ∀ z : (𝓡∂ (n + 1)).boundary M, (z : M) ∈ V → f z = 1) :
    ∃ c : M → ℝ, ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c ∧ (∀ z, 0 < c z) ∧
      (∀ z : (𝓡∂ (n + 1)).boundary M, c z = 1) ∧
      ∃ W : TopologicalSpace.Opens M, (x : M) ∈ W ∧ (W : Set M) ⊆ V ∧
        ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ω c W ∧ EqOn c (S.solve f) W ∧
        (∀ z ∈ W, conformalGaugePotential (g.ofLE (by decide)) q c z = 0) := by
  have hw := S.correct f hf
  have htrace : ∀ z : (𝓡∂ (n + 1)).boundary M, (z : M) ∈ V → S.solve f z = 1 :=
    fun z hz => (hw.2.2 z).trans (hf₁ z hz)
  obtain ⟨c, hc, hpos, hcb, W, hxW, hWV, hcw⟩ :=
    exists_positive_gauge_agreeing_near (S.solve f) hw.1 x V hx htrace
  have hfanalytic : ContMDiffOn (𝓡 n) 𝓘(ℝ) ω f (observedPatch (n := n) V) :=
    contMDiffOn_const.congr hf₁
  have hwanalytic := hRegularity g q hq f (S.solve f) hw V hfanalytic
  have hwall := schrodinger_eq_zero_of_interior (g.ofLE (by decide)) q (S.solve f)
    (hq.of_le (by decide)) hw.1 hw.2.1
  refine ⟨c, hc, hpos, hcb, W, hxW, hWV, (hwanalytic.mono hWV).congr hcw, hcw, ?_⟩
  intro z hz
  have hlocal := schrodinger_eq_of_eventuallyEq (g.ofLE (by decide)) q
    ((hc.of_le (by decide)).contMDiffAt (x := z))
    ((hw.1.of_le (by decide)).contMDiffAt (x := z))
    (hcw.eventuallyEq_of_mem (W.isOpen.mem_nhds hz))
  have hzero : schrodinger (g.ofLE (by decide)) q c z = 0 :=
    hlocal.trans (congrFun hwall z)
  simp only [conformalGaugePotential, hzero, mul_zero]

theorem nonempty_localSolutionGauge
    (hRegularity : BoundaryAnalyticRegularityAssumption (n := n) (M := M))
    (g : Metric (n := n) (M := M) ω) (q : M → ℝ)
    (hq : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω q)
    (S : DirichletSolver (g.ofLE (by decide)) q)
    (f : ((𝓡∂ (n + 1)).boundary M) → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f)
    (x : (𝓡∂ (n + 1)).boundary M) (V : TopologicalSpace.Opens M) (hx : (x : M) ∈ V)
    (hf₁ : ∀ z : (𝓡∂ (n + 1)).boundary M, (z : M) ∈ V → f z = 1) :
    Nonempty (LocalSolutionGauge (g.ofLE (by decide)) q S f x V) := by
  obtain ⟨c, hc, hpos, hb, W, hxW, hWV, han, heq, hzero⟩ :=
    exists_local_potential_zero_gauge hRegularity g q hq S f hf x V hx hf₁
  exact ⟨⟨c, hc, hpos, hb, W, hxW, hWV, han, heq, hzero⟩⟩

end ConformalPoisson

end RefPart_LocalPotentialGauge

/- Interface support: DataTransport.lean, SHA256 08032e2c32b17d1d55e266bfc54bd7883d74ce305a96def2d6b7eb9395114b42 -/
noncomputable section RefPart_DataTransport

/-! Transport of the actual compactly supported test data along the analytic boundary identification. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

variable
  (β : Diffeomorph (𝓡 n) (𝓡 n)
    ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
  {Γ₁ : Set ((𝓡∂ (n + 1)).boundary M₁)}
  {Γ₂ : Set ((𝓡∂ (n + 1)).boundary M₂)}
  (hΓ : ∀ x, x ∈ Γ₁ ↔ β x ∈ Γ₂)

def transportBoundaryDatum (f : BoundaryDatum Γ₁) : BoundaryDatum Γ₂ := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  refine ⟨f.val ∘ β.symm, ?_, ?_, ?_⟩
  · exact f.property.1.comp (β.symm.contMDiff.of_le (by decide))
  · exact f.property.2.1.comp_homeomorph β.symm.toHomeomorph
  · intro y hy
    have hmem := f.property.2.2 (tsupport_comp_subset_preimage f.val β.symm.continuous hy)
    simpa only [Diffeomorph.apply_symm_apply] using (hΓ (β.symm y)).mp hmem

@[simp]
theorem transportBoundaryDatum_val (f : BoundaryDatum Γ₁) :
    (transportBoundaryDatum β hΓ f).val = f.val ∘ β.symm := rfl

def transportBoundaryDatumLinearMap : BoundaryDatum Γ₁ →ₗ[ℝ] BoundaryDatum Γ₂ where
  toFun := transportBoundaryDatum β hΓ
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

include hΓ in
theorem matchingBoundaryPatches_symm :
    ∀ y, y ∈ Γ₂ ↔ β.symm y ∈ Γ₁ := by
  intro y
  simpa only [Diffeomorph.apply_symm_apply] using (hΓ (β.symm y)).symm

/-- Every target datum arises from a source datum, as required for reverse continuation. -/
def transportBoundaryDatumLinearEquiv : BoundaryDatum Γ₁ ≃ₗ[ℝ] BoundaryDatum Γ₂ :=
  { transportBoundaryDatumLinearMap β hΓ with
    invFun := transportBoundaryDatum β.symm (matchingBoundaryPatches_symm β hΓ)
    left_inv := by
      intro f
      apply Subtype.ext
      funext x
      change f.val (β.symm (β x)) = f.val x
      rw [β.symm_apply_apply]
    right_inv := by
      intro f
      apply Subtype.ext
      funext y
      change f.val (β (β.symm y)) = f.val y
      rw [β.apply_symm_apply] }

theorem transportBoundaryDatum_injective :
    Function.Injective (transportBoundaryDatum β hΓ) := by
  intro f h heq
  apply Subtype.ext
  funext x
  have hval := congrArg (fun k : BoundaryDatum Γ₂ => k.val (β x)) heq
  simpa only [transportBoundaryDatum_val, Function.comp_apply,
    Diffeomorph.symm_apply_apply] using hval

theorem boundaryDatum_eq_zero_outside {Γ : Set ((𝓡∂ (n + 1)).boundary M₁)}
    (f : BoundaryDatum Γ) (x : (𝓡∂ (n + 1)).boundary M₁) (hx : x ∉ Γ) :
    f.val x = 0 := by
  by_contra hfx
  exact hx (f.property.2.2 (subset_tsupport f.val hfx))

end ConformalPoisson

end RefPart_DataTransport

/- Interface support: ScalarRecovery.lean, SHA256 7a7c32d1afdf1261bb69a06b90acec06f0466ce06619c61a6c962ac9d630aee7 -/
noncomputable section RefPart_ScalarRecovery

/-!
Algebraic parts of the selected paper's argument.

This development module will be integrated after contract freeze. The first lemma is the
pointwise kernel argument in Proposition 4.1. The remaining lemmas handle the same point
and multiplier across every datum, as needed for the uniqueness part of Theorem 1.1.
-/

namespace ConformalPoisson

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem linearForm_eq_smul_of_ker_le
    (L A : V →ₗ[ℝ] ℝ) (h : L.ker ≤ A.ker)
    (e : V) (he : L e = 1) :
    A = A e • L := by
  ext x
  have hx : x - L x • e ∈ L.ker := by
    simp [LinearMap.mem_ker, he]
  have hAx : A x - L x * A e = 0 := by
    simpa [LinearMap.mem_ker] using h hx
  simpa [mul_comm] using sub_eq_zero.mp hAx

variable {D X Y : Type*}

/-- All data share one map and one multiplier. -/
def ScaledSolutionRelation (u : D → X → ℝ) (v : D → Y → ℝ)
    (J : X → Y) (c : X → ℝ) : Prop :=
  ∀ f x, u f x = c x * v f (J x)

/-- The evaluation family identifies both a point and a nonzero scale. -/
def SeparatesPointAndScale (v : D → Y → ℝ) : Prop :=
  ∀ y z (a b : ℝ), a ≠ 0 → b ≠ 0 →
    (∀ f, a * v f y = b * v f z) → y = z ∧ a = b

theorem SeparatesPointAndScale.precomp_surjective
    {D' : Type*} {v : D → Y → ℝ} (hsep : SeparatesPointAndScale v)
    (T : D' → D) (hT : Function.Surjective T) :
    SeparatesPointAndScale (fun f y => v (T f) y) := by
  intro y z a b ha hb h
  apply hsep y z a b ha hb
  intro f
  obtain ⟨f', rfl⟩ := hT f
  exact h f'

theorem scaledSolutionRelation_unique
    {u : D → X → ℝ} {v : D → Y → ℝ}
    (hsep : SeparatesPointAndScale v)
    {J K : X → Y} {c d : X → ℝ}
    (hc : ∀ x, c x ≠ 0) (hd : ∀ x, d x ≠ 0)
    (hJ : ScaledSolutionRelation u v J c)
    (hK : ScaledSolutionRelation u v K d) :
    J = K ∧ c = d := by
  have h (x : X) : J x = K x ∧ c x = d x := by
    apply hsep (J x) (K x) (c x) (d x) (hc x) (hd x)
    intro f
    exact (hJ f x).symm.trans (hK f x)
  exact ⟨funext fun x => (h x).1, funext fun x => (h x).2⟩

theorem scaledSolutionRelation_comp
    {Z : Type*} {u : D → X → ℝ} {v : D → Y → ℝ} {w : D → Z → ℝ}
    {J : X → Y} {K : Y → Z} {c : X → ℝ} {d : Y → ℝ}
    (hJ : ScaledSolutionRelation u v J c)
    (hK : ScaledSolutionRelation v w K d) :
    ScaledSolutionRelation u w (K ∘ J) (fun x => c x * d (J x)) := by
  intro f x
  rw [hJ f x, hK f (J x)]
  exact (mul_assoc _ _ _).symm

end ConformalPoisson

end RefPart_ScalarRecovery

/- Interface support: ConclusionProperties.lean, SHA256 3c53f9f2bb3dd2e81949afe8b18109bc58ff8196e520e3950872707d6e406601 -/
noncomputable section RefPart_ConclusionProperties

/-! Checks that the concrete conclusion supports the intended local derivatives and uniqueness. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M M₁ M₂ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
/-- The extension in the coefficient formula is analytic locally at every observed point. -/
theorem contMDiffAt_extendFromOpen {k : ℕ∞ω}
    (U : TopologicalSpace.Opens M) (c : U → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) k c) (x : U) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k (extendFromOpen U c) (x : M) := by
  apply contMDiffAt_subtype_iff.mp
  simpa only [extendFromOpen_apply] using hc.contMDiffAt (x := x)

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
/-- Any ambient extension agreeing on the open set has the same germ at its points. -/
theorem extendFromOpen_eventuallyEq (U : TopologicalSpace.Opens M)
    (c : U → ℝ) (v : M → ℝ)
    (hv : ∀ y : U, v y = c y) (x : U) :
    Filter.EventuallyEq (nhds (x : M)) (extendFromOpen U c) v := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  exact (extendFromOpen_apply U c ⟨y, hy⟩).trans (hv ⟨y, hy⟩).symm

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
/-- Normal differentiation of the multiplier depends only on the germ on the observed domain. -/
theorem normalDerivative_eq_of_eventuallyEq
    (ν : (x : (𝓡∂ (n + 1)).boundary M) →
      TangentSpace (𝓡∂ (n + 1)) (x : M))
    {u v : M → ℝ} (x : (𝓡∂ (n + 1)).boundary M)
    (h : Filter.EventuallyEq (nhds (x : M)) u v) :
    normalDerivative ν u x = normalDerivative ν v x := by
  exact congrArg (fun L => L (ν x)) (h.mvfderiv_eq (I := 𝓡∂ (n + 1)))

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
/-- Every relatively open observed boundary patch has the ambient-open representation used here. -/
theorem exists_open_representing_boundary_patch
    (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M)) :
    ∃ V : TopologicalSpace.Opens M, observedPatch (n := n) V = (Γ : Set _) := by
  obtain ⟨V, hV, hΓ⟩ := isOpen_induced_iff.mp Γ.isOpen
  exact ⟨⟨V, hV⟩, hΓ⟩

variable {V₁ : TopologicalSpace.Opens M₁} {V₂ : TopologicalSpace.Opens M₂}

@[ext]
theorem GaugePair.ext {P Q : GaugePair (n := n) V₁ V₂}
    (hmap : P.map = Q.map) (hmul : P.multiplier = Q.multiplier) : P = Q := by
  cases P
  cases Q
  cases hmap
  cases hmul
  rfl

/-- Once projective separation is proved, uniqueness applies to the actual geometric pair. -/
theorem GaugePair.eq_of_solution_relations
    {β : Diffeomorph (𝓡 n) (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω}
    {g₁ : Metric (n := n) (M := M₁)} {g₂ : Metric (n := n) (M := M₂)}
    {q₁ : M₁ → ℝ} {q₂ : M₂ → ℝ}
    {S₁ : DirichletSolver g₁ q₁} {S₂ : DirichletSolver g₂ q₂}
    (ν₁ : (x : (𝓡∂ (n + 1)).boundary M₁) →
      TangentSpace (𝓡∂ (n + 1)) (x : M₁))
    (hsep : SeparatesPointAndScale
      (fun (f : BoundaryDatum (observedPatch (n := n) V₁))
          (y : observedDomain (𝓡∂ (n + 1)) V₂) =>
        S₂.solve (f.val ∘ β.symm) y))
    {P Q : GaugePair (n := n) V₁ V₂}
    (hP : P.RealizesTheorem V₁ V₂ β g₁ g₂ q₁ q₂ S₁ S₂ ν₁)
    (hQ : Q.RealizesTheorem V₁ V₂ β g₁ g₂ q₁ q₂ S₁ S₂ ν₁) : P = Q := by
  have h := scaledSolutionRelation_unique
    (u := fun (f : BoundaryDatum (observedPatch (n := n) V₁))
        (x : observedDomain (𝓡∂ (n + 1)) V₁) => S₁.solve f.val x)
    hsep (fun x => ne_of_gt (P.positive x)) (fun x => ne_of_gt (Q.positive x))
    hP.2.2.2 hQ.2.2.2
  exact GaugePair.ext (DFunLike.coe_injective h.1) h.2

end ConformalPoisson

end RefPart_ConclusionProperties

/- Interface support: BoundaryDataSeparation.lean, SHA256 789e91526c1e12170a2d99eff39469361f8083a51d1dfb9cd5fc994d4813805a -/
noncomputable section RefPart_BoundaryDataSeparation

/-! Actual compactly supported smooth boundary test functions for separation. -/


open Set
open scoped Manifold ContDiff Topology

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

local instance ref_BoundaryDataSeparation_boundaryAnalyticManifold : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := ω) M (by decide)

/-- A supported datum equal to one on a whole boundary neighborhood of the chosen point. -/
theorem exists_boundaryDatum_one_near
    (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M))
    (x : (𝓡∂ (n + 1)).boundary M) (hx : x ∈ Γ) :
    ∃ f : BoundaryDatum (Γ : Set ((𝓡∂ (n + 1)).boundary M)),
      ∃ V : TopologicalSpace.Opens M, (x : M) ∈ V ∧ observedPatch (n := n) V ⊆ Γ ∧
        ∀ z : (𝓡∂ (n + 1)).boundary M, (z : M) ∈ V → f.val z = 1 := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (Γ.isOpen.mem_nhds hx)
  let U : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M) :=
    ⟨interior {z | b z = 1} ∩ (Γ : Set _), isOpen_interior.inter Γ.isOpen⟩
  have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.mpr b.eventuallyEq_one, hx⟩
  obtain ⟨V, hV⟩ := exists_open_representing_boundary_patch U
  refine ⟨⟨b, b.contMDiff, b.hasCompactSupport, hb⟩, V, ?_, ?_, ?_⟩
  · change x ∈ observedPatch (n := n) V
    rwa [hV]
  · rw [hV]
    exact inter_subset_right
  · intro z hz
    have hzU : z ∈ U := by change z ∈ observedPatch (n := n) V at hz; rwa [hV] at hz
    exact interior_subset hzU.1

/-- A boundary datum equal to one at any point of the observed patch. -/
theorem exists_boundaryDatum_value_one
    (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M))
    (x : (𝓡∂ (n + 1)).boundary M) (hx : x ∈ Γ) :
    ∃ f : BoundaryDatum (Γ : Set ((𝓡∂ (n + 1)).boundary M)), f.val x = 1 := by
  obtain ⟨f, V, hxV, _, hf⟩ := exists_boundaryDatum_one_near Γ x hx
  exact ⟨f, hf x hxV⟩

/-- A single datum distinguishes two distinct observed boundary points. -/
theorem exists_boundaryDatum_separating_points
    (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M))
    (x y : (𝓡∂ (n + 1)).boundary M) (hx : x ∈ Γ) (hxy : x ≠ y) :
    ∃ f : BoundaryDatum (Γ : Set ((𝓡∂ (n + 1)).boundary M)),
      f.val x = 1 ∧ f.val y = 0 := by
  let W : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M) :=
    ⟨(Γ : Set _) ∩ {y}ᶜ, Γ.isOpen.inter isClosed_singleton.isOpen_compl⟩
  obtain ⟨f, hf⟩ := exists_boundaryDatum_value_one W x ⟨hx, hxy⟩
  refine ⟨⟨f.val, f.property.1, f.property.2.1, f.property.2.2.trans inter_subset_left⟩,
    hf, ?_⟩
  exact boundaryDatum_eq_zero_outside f y (by simp [W])

omit [T2Space M] in
/-- A positive-dimensional boundary patch still contains a point after deleting one point. -/
theorem exists_boundary_point_in_patch_ne [NeZero n]
    (Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M))
    (hΓ : (Γ : Set ((𝓡∂ (n + 1)).boundary M)).Nonempty)
    (x : (𝓡∂ (n + 1)).boundary M) : ∃ y ∈ Γ, y ≠ x := by
  classical
  obtain ⟨a, ha⟩ := hΓ
  by_cases hax : a = x
  · subst a
    let e := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hopen : IsOpen (e '' (e.source ∩ (Γ : Set _))) :=
      e.isOpen_image_source_inter Γ.isOpen
    have hmem : e x ∈ e '' (e.source ∩ (Γ : Set _)) :=
      ⟨x, ⟨mem_chart_source _ x, ha⟩, rfl⟩
    have hnear : ∀ᶠ z in 𝓝[≠] e x, z ∈ e '' (e.source ∩ (Γ : Set _)) :=
      mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
    obtain ⟨z, hz, hne⟩ := (hnear.and self_mem_nhdsWithin).exists
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy.2, fun heq => hne (congrArg e heq)⟩
  · exact ⟨a, ha, hax⟩

end ConformalPoisson

end RefPart_BoundaryDataSeparation

/- Interface support: GaugeBoundary.lean, SHA256 908657851fc5543fb900048ed7985fa772d8d372b729ef570c7f9a203968ac3d -/
noncomputable section RefPart_GaugeBoundary

/-! Boundary unit normals, actual solver transport and DN correction under the conformal gauge. -/


open Bundle
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ω M]

theorem IsOutwardUnitNormal.conformalGauge
    (g : Metric (n := n) (M := M)) (c : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (x : (𝓡∂ (n + 1)).boundary M) (hcx : c x = 1)
    (ν : TangentSpace (𝓡∂ (n + 1)) (x : M)) (hν : IsOutwardUnitNormal g x ν) :
    IsOutwardUnitNormal (conformalGaugeMetric g c hc hcpos) x ν := by
  refine ⟨hν.1, ?_, fun w => ?_⟩
  · simpa only [conformalGaugeMetric, ContMDiffRiemannianMetric.rescale_inner, hcx,
      Real.one_rpow, one_mul] using hν.2.1
  · simpa only [conformalGaugeMetric, ContMDiffRiemannianMetric.rescale_inner, hcx,
      Real.one_rpow, one_mul] using hν.2.2 w

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
theorem normalDerivative_mul
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    {c v : M → ℝ} (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c)
    (hv : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ v) (y : (𝓡∂ (n + 1)).boundary M) :
    normalDerivative ν (c * v) y = c y * normalDerivative ν v y + v y * normalDerivative ν c y := by
  unfold normalDerivative
  rw [mvfderiv_mul (hc.mdifferentiableAt (by decide)) (hv.mdifferentiableAt (by decide))]
  simp only [add_apply, smul_apply, smul_eq_mul]

omit [IsManifold (𝓡∂ (n + 1)) ω M] in
theorem normalDerivative_div_conformalGauge
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    {c u : M → ℝ} (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c)
    (hcpos : ∀ x, 0 < c x) (hu : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u)
    (y : (𝓡∂ (n + 1)).boundary M) (hcy : c y = 1) :
    normalDerivative ν (u / c) y = normalDerivative ν u y - u y * normalDerivative ν c y := by
  have hv := hu.div₀ hc (fun x => (hcpos x).ne')
  have hmul : c * (u / c) = u := by
    funext x
    exact mul_div_cancel₀ (u x) (hcpos x).ne'
  have h := normalDerivative_mul ν hc hv y
  rw [hmul] at h
  simp only [Pi.div_apply, hcy, div_one, one_mul] at h
  linarith

/-- The gauged full Dirichlet solver is constructed explicitly from the original solver. -/
def DirichletSolver.conformalGauge
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hcb : ∀ x : (𝓡∂ (n + 1)).boundary M, c x = 1) (S : DirichletSolver g q) :
    DirichletSolver (conformalGaugeMetric g c hc hcpos) (conformalGaugePotential g q c) where
  solve f := S.solve f / c
  correct f hf := (S.correct f hf).div_conformalGauge hdim g q c (S.solve f) hc hcpos hcb

/-- The actual DN correction has the outward-normal sign in Lemma 2.1. -/
theorem DirichletSolver.conformalGauge_normalDerivative
    (hdim : 2 ≤ n) (g : Metric (n := n) (M := M)) (q c : M → ℝ)
    (hc : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c) (hcpos : ∀ x, 0 < c x)
    (hcb : ∀ x : (𝓡∂ (n + 1)).boundary M, c x = 1) (S : DirichletSolver g q)
    (ν : (y : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (y : M))
    (f : ((𝓡∂ (n + 1)).boundary M) → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f)
    (y : (𝓡∂ (n + 1)).boundary M) :
    normalDerivative ν ((S.conformalGauge hdim g q c hc hcpos hcb).solve f) y =
      normalDerivative ν (S.solve f) y - f y * normalDerivative ν c y := by
  change normalDerivative ν (S.solve f / c) y = _
  rw [normalDerivative_div_conformalGauge ν hc hcpos (S.correct f hf).1 y (hcb y),
    (S.correct f hf).2.2 y]

end ConformalPoisson

end RefPart_GaugeBoundary

/- Interface support: GaugeMeasurements.lean, SHA256 0ed66b21fb1dbe778ddd97b58a489fdb134ec10b5cb4554fa25f4f5b2345a5fc -/
noncomputable section RefPart_GaugeMeasurements

/-! Matched gauge normal derivatives preserve the actual localized DN equality. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

theorem LocalDNMapsEqual.conformalGauge
    (hdim : 2 ≤ n) (V₁ : TopologicalSpace.Opens M₁)
    (β : Diffeomorph (𝓡 n) (𝓡 n)
      ((𝓡∂ (n + 1)).boundary M₁) ((𝓡∂ (n + 1)).boundary M₂) ω)
    (g₁ : Metric (n := n) (M := M₁)) (g₂ : Metric (n := n) (M := M₂))
    (q₁ c₁ : M₁ → ℝ) (q₂ c₂ : M₂ → ℝ)
    (hc₁ : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c₁) (hpos₁ : ∀ x, 0 < c₁ x)
    (hc₂ : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ c₂) (hpos₂ : ∀ x, 0 < c₂ x)
    (hb₁ : ∀ x : (𝓡∂ (n + 1)).boundary M₁, c₁ x = 1)
    (hb₂ : ∀ x : (𝓡∂ (n + 1)).boundary M₂, c₂ x = 1)
    (S₁ : DirichletSolver g₁ q₁) (S₂ : DirichletSolver g₂ q₂)
    (ν₁ : (x : (𝓡∂ (n + 1)).boundary M₁) → TangentSpace (𝓡∂ (n + 1)) (x : M₁))
    (ν₂ : (x : (𝓡∂ (n + 1)).boundary M₂) → TangentSpace (𝓡∂ (n + 1)) (x : M₂))
    (hDN : LocalDNMapsEqual V₁ β g₁ g₂ q₁ q₂ S₁ S₂ ν₁ ν₂)
    (hnormal : ∀ x : (𝓡∂ (n + 1)).boundary M₁, (x : M₁) ∈ V₁ →
      normalDerivative ν₁ c₁ x = normalDerivative ν₂ c₂ (β x)) :
    LocalDNMapsEqual V₁ β (conformalGaugeMetric g₁ c₁ hc₁ hpos₁)
      (conformalGaugeMetric g₂ c₂ hc₂ hpos₂)
      (conformalGaugePotential g₁ q₁ c₁) (conformalGaugePotential g₂ q₂ c₂)
      (S₁.conformalGauge hdim g₁ q₁ c₁ hc₁ hpos₁ hb₁)
      (S₂.conformalGauge hdim g₂ q₂ c₂ hc₂ hpos₂ hb₂) ν₁ ν₂ := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  intro f x hx
  have hf₂ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (f.val ∘ β.symm) :=
    f.property.1.comp (β.symm.contMDiff.of_le (by decide))
  rw [S₁.conformalGauge_normalDerivative hdim g₁ q₁ c₁ hc₁ hpos₁ hb₁ ν₁ f.val f.property.1 x,
    S₂.conformalGauge_normalDerivative hdim g₂ q₂ c₂ hc₂ hpos₂ hb₂ ν₂
      (f.val ∘ β.symm) hf₂ (β x), hDN f x hx, hnormal x hx]
  simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]

end ConformalPoisson

end RefPart_GaugeMeasurements

/- Interface support: BoundaryGaugePair.lean, SHA256 7269c0cc0d2777f321bb5d7cae14c378466984c386ba71c9e001868deaf76d52 -/
noncomputable section RefPart_BoundaryGaugePair

/-!
Two actual local potential-killing gauges from one original supported datum.
Their normal derivatives match wherever the two chosen neighborhoods meet on
the identified boundary. Later DN-symbol localization uses this smaller patch.
-/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂] [T2Space M₁] [T2Space M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]

structure BoundaryGaugePair
    (A₁ : AnalyticProblem (n := n) (M := M₁)) (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂) (x : (𝓡∂ (n + 1)).boundary M₁) where
  datum : BoundaryDatum (observedPatch (n := n) V₁)
  allowed₁ : TopologicalSpace.Opens M₁
  allowed₂ : TopologicalSpace.Opens M₂
  point_mem₁ : (x : M₁) ∈ allowed₁
  point_mem₂ : (D.boundaryIdentification x : M₂) ∈ allowed₂
  patch_subset : observedPatch (n := n) allowed₁ ⊆ observedPatch (n := n) V₁
  allowed_match : ∀ z : (𝓡∂ (n + 1)).boundary M₁,
    (z : M₁) ∈ allowed₁ ↔ (D.boundaryIdentification z : M₂) ∈ allowed₂
  gauge₁ : LocalSolutionGauge A₁.smoothMetric A₁.potential D.solver₁ datum.val x allowed₁
  gauge₂ : LocalSolutionGauge A₂.smoothMetric A₂.potential D.solver₂
    (datum.val ∘ D.boundaryIdentification.symm) (D.boundaryIdentification x) allowed₂
  normal_match : ∀ z : (𝓡∂ (n + 1)).boundary M₁,
    (z : M₁) ∈ gauge₁.neighborhood → (D.boundaryIdentification z : M₂) ∈ gauge₂.neighborhood →
      normalDerivative D.normal₁ gauge₁.multiplier z =
        normalDerivative D.normal₂ gauge₂.multiplier (D.boundaryIdentification z)

theorem nonempty_boundaryGaugePair
    (hReg₁ : BoundaryAnalyticRegularityAssumption (n := n) (M := M₁))
    (hReg₂ : BoundaryAnalyticRegularityAssumption (n := n) (M := M₂))
    (A₁ : AnalyticProblem (n := n) (M := M₁)) (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂) (x : (𝓡∂ (n + 1)).boundary M₁)
    (hx : (x : M₁) ∈ V₁) : Nonempty (BoundaryGaugePair A₁ A₂ V₁ V₂ D x) := by
  let Γ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M₁) :=
    ⟨observedPatch (n := n) V₁, V₁.isOpen.preimage continuous_subtype_val⟩
  obtain ⟨f, U₁, hx₁, hsub, hf₁⟩ := exists_boundaryDatum_one_near Γ x hx
  let Δ : TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M₂) :=
    ⟨D.boundaryIdentification.symm ⁻¹' observedPatch (n := n) U₁,
      (U₁.isOpen.preimage continuous_subtype_val).preimage D.boundaryIdentification.symm.continuous⟩
  obtain ⟨U₂, hU₂⟩ := exists_open_representing_boundary_patch Δ
  have hmatch : ∀ z : (𝓡∂ (n + 1)).boundary M₁,
      (z : M₁) ∈ U₁ ↔ (D.boundaryIdentification z : M₂) ∈ U₂ := by
    intro z
    change z ∈ observedPatch (n := n) U₁ ↔ D.boundaryIdentification z ∈ observedPatch (n := n) U₂
    rw [hU₂]
    change z ∈ observedPatch (n := n) U₁ ↔
      D.boundaryIdentification.symm (D.boundaryIdentification z) ∈ observedPatch (n := n) U₁
    rw [D.boundaryIdentification.symm_apply_apply]
  have hx₂ := (hmatch x).mp hx₁
  have hf₂ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (f.val ∘ D.boundaryIdentification.symm) :=
    f.property.1.comp (D.boundaryIdentification.symm.contMDiff.of_le (by decide))
  have hf₂one : ∀ z : (𝓡∂ (n + 1)).boundary M₂, (z : M₂) ∈ U₂ →
      (f.val ∘ D.boundaryIdentification.symm) z = 1 := by
    intro z hz
    have hz' : D.boundaryIdentification.symm z ∈ observedPatch (n := n) U₁ := by
      change z ∈ observedPatch (n := n) U₂ at hz
      rwa [hU₂] at hz
    exact hf₁ _ hz'
  obtain ⟨C₁⟩ := nonempty_localSolutionGauge hReg₁ A₁.metric A₁.potential
    A₁.analytic_potential D.solver₁ f.val f.property.1 x U₁ hx₁ hf₁
  obtain ⟨C₂⟩ := nonempty_localSolutionGauge hReg₂ A₂.metric A₂.potential
    A₂.analytic_potential D.solver₂ (f.val ∘ D.boundaryIdentification.symm) hf₂
    (D.boundaryIdentification x) U₂ hx₂ hf₂one
  refine ⟨⟨f, U₁, U₂, hx₁, hx₂, hsub, hmatch, C₁, C₂, ?_⟩⟩
  intro z hz₁ hz₂
  rw [normalDerivative_eq_of_eventuallyEq D.normal₁ z
    (C₁.agrees_solution.eventuallyEq_of_mem (C₁.neighborhood.isOpen.mem_nhds hz₁)),
    normalDerivative_eq_of_eventuallyEq D.normal₂ (D.boundaryIdentification z)
      (C₂.agrees_solution.eventuallyEq_of_mem (C₂.neighborhood.isOpen.mem_nhds hz₂))]
  exact D.local_DN_equal f z (hsub (C₁.subset_allowed hz₁))

end ConformalPoisson

end RefPart_BoundaryGaugePair

/- Interface support: BoundaryGaugePatch.lean, SHA256 e91bb1829a0ea9272ed34b8783d6a18ee2a425886beb5431b3001587a2db733f -/
noncomputable section RefPart_BoundaryGaugePatch

/-!
The common nonempty observation patch of the two independent cutoff gauges.
All original supported data retain matching gauged observations there.
-/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]
  {A₁ : AnalyticProblem (n := n) (M := M₁)} {A₂ : AnalyticProblem (n := n) (M := M₂)}
  {V₁ : TopologicalSpace.Opens M₁} {V₂ : TopologicalSpace.Opens M₂}
  {D : MatchingMeasurements A₁ A₂ V₁ V₂} {x : (𝓡∂ (n + 1)).boundary M₁}

def BoundaryGaugePair.commonPatch (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary M₁) :=
  ⟨{z | (z : M₁) ∈ P.gauge₁.neighborhood ∧
      (D.boundaryIdentification z : M₂) ∈ P.gauge₂.neighborhood},
    (P.gauge₁.neighborhood.isOpen.preimage continuous_subtype_val).inter
      ((P.gauge₂.neighborhood.isOpen.preimage continuous_subtype_val).preimage
        D.boundaryIdentification.continuous)⟩

theorem BoundaryGaugePair.point_mem_commonPatch (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    x ∈ P.commonPatch := ⟨P.gauge₁.point_mem, P.gauge₂.point_mem⟩

theorem BoundaryGaugePair.commonPatch_subset (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    (P.commonPatch : Set _) ⊆ observedPatch (n := n) V₁ :=
  fun _ hz => P.patch_subset (P.gauge₁.subset_allowed hz.1)

/-- The observation patch is smaller, while the quantified data are still the original data. -/
theorem BoundaryGaugePair.gauged_normal_equal
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n)
    (f : BoundaryDatum (observedPatch (n := n) V₁))
    (z : (𝓡∂ (n + 1)).boundary M₁) (hz : z ∈ P.commonPatch) :
    normalDerivative D.normal₁
      ((D.solver₁.conformalGauge hdim A₁.smoothMetric A₁.potential P.gauge₁.multiplier
        P.gauge₁.smooth P.gauge₁.positive P.gauge₁.boundary_one).solve f.val) z =
    normalDerivative D.normal₂
      ((D.solver₂.conformalGauge hdim A₂.smoothMetric A₂.potential P.gauge₂.multiplier
        P.gauge₂.smooth P.gauge₂.positive P.gauge₂.boundary_one).solve
          (f.val ∘ D.boundaryIdentification.symm)) (D.boundaryIdentification z) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) :=
    TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  have hf₂ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (f.val ∘ D.boundaryIdentification.symm) :=
    f.property.1.comp (D.boundaryIdentification.symm.contMDiff.of_le (by decide))
  rw [D.solver₁.conformalGauge_normalDerivative hdim A₁.smoothMetric A₁.potential
    P.gauge₁.multiplier P.gauge₁.smooth P.gauge₁.positive P.gauge₁.boundary_one
    D.normal₁ f.val f.property.1 z,
    D.solver₂.conformalGauge_normalDerivative hdim A₂.smoothMetric A₂.potential
      P.gauge₂.multiplier P.gauge₂.smooth P.gauge₂.positive P.gauge₂.boundary_one
      D.normal₂ (f.val ∘ D.boundaryIdentification.symm) hf₂ (D.boundaryIdentification z),
    D.local_DN_equal f z (P.commonPatch_subset hz), P.normal_match z hz.1 hz.2]
  simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]

theorem BoundaryGaugePair.localDNMapsEqual
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n)
    (U : TopologicalSpace.Opens M₁) (hU : observedPatch (n := n) U = (P.commonPatch : Set _)) :
    LocalDNMapsEqual U D.boundaryIdentification
      (conformalGaugeMetric A₁.smoothMetric P.gauge₁.multiplier P.gauge₁.smooth P.gauge₁.positive)
      (conformalGaugeMetric A₂.smoothMetric P.gauge₂.multiplier P.gauge₂.smooth P.gauge₂.positive)
      (conformalGaugePotential A₁.smoothMetric A₁.potential P.gauge₁.multiplier)
      (conformalGaugePotential A₂.smoothMetric A₂.potential P.gauge₂.multiplier)
      (D.solver₁.conformalGauge hdim A₁.smoothMetric A₁.potential P.gauge₁.multiplier
        P.gauge₁.smooth P.gauge₁.positive P.gauge₁.boundary_one)
      (D.solver₂.conformalGauge hdim A₂.smoothMetric A₂.potential P.gauge₂.multiplier
        P.gauge₂.smooth P.gauge₂.positive P.gauge₂.boundary_one) D.normal₁ D.normal₂ := by
  intro f z hz
  have hsub : observedPatch (n := n) U ⊆ observedPatch (n := n) V₁ := by
    rw [hU]
    exact P.commonPatch_subset
  let original : BoundaryDatum (observedPatch (n := n) V₁) :=
    ⟨f.val, f.property.1, f.property.2.1, f.property.2.2.trans hsub⟩
  have hzP : z ∈ P.commonPatch := by change z ∈ observedPatch (n := n) U at hz; rwa [hU] at hz
  exact P.gauged_normal_equal hdim original z hzP

end ConformalPoisson

end RefPart_BoundaryGaugePatch

/- Interface support: BoundaryGaugeProperties.lean, SHA256 3ff770c8c09ff7242b8b387eda3dc44c043af15e97935ddc4cc18ca798d5b578 -/
noncomputable section RefPart_BoundaryGaugeProperties

/-! Concrete geometric properties of the same paired gauges used by the localized DN caller. -/


open Set
open scoped Manifold ContDiff

namespace ConformalPoisson

variable {n : ℕ} {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁]
  [IsManifold (𝓡∂ (n + 1)) ω M₂]
  {A₁ : AnalyticProblem (n := n) (M := M₁)} {A₂ : AnalyticProblem (n := n) (M := M₂)}
  {V₁ : TopologicalSpace.Opens M₁} {V₂ : TopologicalSpace.Opens M₂}
  {D : MatchingMeasurements A₁ A₂ V₁ V₂} {x : (𝓡∂ (n + 1)).boundary M₁}

theorem BoundaryGaugePair.metricAnalyticOn₁ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    MetricAnalyticOn (conformalGaugeMetric A₁.smoothMetric P.gauge₁.multiplier
      P.gauge₁.smooth P.gauge₁.positive) P.gauge₁.neighborhood :=
  MetricAnalyticOn.conformalGauge A₁.smoothMetric P.gauge₁.neighborhood
    (metricAnalyticOn_of_analytic A₁.metric P.gauge₁.neighborhood)
    P.gauge₁.multiplier P.gauge₁.smooth P.gauge₁.positive P.gauge₁.analytic_local

theorem BoundaryGaugePair.metricAnalyticOn₂ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    MetricAnalyticOn (conformalGaugeMetric A₂.smoothMetric P.gauge₂.multiplier
      P.gauge₂.smooth P.gauge₂.positive) P.gauge₂.neighborhood :=
  MetricAnalyticOn.conformalGauge A₂.smoothMetric P.gauge₂.neighborhood
    (metricAnalyticOn_of_analytic A₂.metric P.gauge₂.neighborhood)
    P.gauge₂.multiplier P.gauge₂.smooth P.gauge₂.positive P.gauge₂.analytic_local

theorem BoundaryGaugePair.normal_spec₁ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x)
    (z : (𝓡∂ (n + 1)).boundary M₁) :
    IsOutwardUnitNormal (conformalGaugeMetric A₁.smoothMetric P.gauge₁.multiplier
      P.gauge₁.smooth P.gauge₁.positive) z (D.normal₁ z) :=
  IsOutwardUnitNormal.conformalGauge A₁.smoothMetric P.gauge₁.multiplier P.gauge₁.smooth
    P.gauge₁.positive z (P.gauge₁.boundary_one z) (D.normal₁ z) (D.normal₁_spec z)

theorem BoundaryGaugePair.normal_spec₂ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x)
    (z : (𝓡∂ (n + 1)).boundary M₂) :
    IsOutwardUnitNormal (conformalGaugeMetric A₂.smoothMetric P.gauge₂.multiplier
      P.gauge₂.smooth P.gauge₂.positive) z (D.normal₂ z) :=
  IsOutwardUnitNormal.conformalGauge A₂.smoothMetric P.gauge₂.multiplier P.gauge₂.smooth
    P.gauge₂.positive z (P.gauge₂.boundary_one z) (D.normal₂ z) (D.normal₂_spec z)

theorem BoundaryGaugePair.exists_common_ambient_patch (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    ∃ U : TopologicalSpace.Opens M₁, (x : M₁) ∈ U ∧
      observedPatch (n := n) U = (P.commonPatch : Set _) := by
  obtain ⟨U, hU⟩ := exists_open_representing_boundary_patch P.commonPatch
  refine ⟨U, ?_, hU⟩
  change x ∈ observedPatch (n := n) U
  rw [hU]
  exact P.point_mem_commonPatch

end ConformalPoisson

end RefPart_BoundaryGaugeProperties

/- Interface support: GaugedNormalCharts.lean, SHA256 af0fd71716942eda541837ea060b95315f1637279571f7bdc995269959a510c9 -/
noncomputable section RefPart_GaugedNormalCharts

/-! Bind the actual local potential-killing gauges of the original two
problems to the SAME common analytic normal charts and original beta. -/

open Set
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]
  {A₁ : AnalyticProblem (n := n) (M := M₁)} {A₂ : AnalyticProblem (n := n) (M := M₂)}
  {V₁ : TopologicalSpace.Opens M₁} {V₂ : TopologicalSpace.Opens M₂}
  {D : MatchingMeasurements A₁ A₂ V₁ V₂} {x : (𝓡∂ (n + 1)).boundary M₁}

abbrev BoundaryGaugePair.metric₁ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) : Metric (n := n) (M := M₁) :=
  conformalGaugeMetric A₁.smoothMetric P.gauge₁.multiplier P.gauge₁.smooth P.gauge₁.positive
abbrev BoundaryGaugePair.metric₂ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) : Metric (n := n) (M := M₂) :=
  conformalGaugeMetric A₂.smoothMetric P.gauge₂.multiplier P.gauge₂.smooth P.gauge₂.positive
abbrev BoundaryGaugePair.potential₁ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) : M₁ → ℝ :=
  conformalGaugePotential A₁.smoothMetric A₁.potential P.gauge₁.multiplier
abbrev BoundaryGaugePair.potential₂ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) : M₂ → ℝ :=
  conformalGaugePotential A₂.smoothMetric A₂.potential P.gauge₂.multiplier
abbrev BoundaryGaugePair.solver₁ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n) :
    DirichletSolver P.metric₁ P.potential₁ :=
  D.solver₁.conformalGauge hdim A₁.smoothMetric A₁.potential P.gauge₁.multiplier
    P.gauge₁.smooth P.gauge₁.positive P.gauge₁.boundary_one
abbrev BoundaryGaugePair.solver₂ (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n) :
    DirichletSolver P.metric₂ P.potential₂ :=
  D.solver₂.conformalGauge hdim A₂.smoothMetric A₂.potential P.gauge₂.multiplier
    P.gauge₂.smooth P.gauge₂.positive P.gauge₂.boundary_one

abbrev BoundaryGaugePair.CommonCharts (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :=
  CommonNormalCharts D.boundaryIdentification x P.metric₁ P.metric₂ P.gauge₁.neighborhood P.gauge₂.neighborhood

theorem BoundaryGaugePair.exists_commonCharts (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) :
    Nonempty P.CommonCharts :=
  exists_commonNormalCharts D.boundaryIdentification x P.metric₁ P.metric₂
    P.gauge₁.neighborhood P.gauge₂.neighborhood P.metricAnalyticOn₁ P.metricAnalyticOn₂
    P.gauge₁.point_mem P.gauge₂.point_mem

theorem BoundaryGaugePair.potential₁_commonCharts (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x)
    (C : P.CommonCharts) (z : EuclideanHalfSpace (n + 1)) (hz : z ∈ C.chart₁.source) :
    P.potential₁ (C.chart₁ z) = 0 :=
  P.gauge₁.potential_zero _ (C.target₁ (C.chart₁.map_source hz))

theorem BoundaryGaugePair.potential₂_commonCharts (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x)
    (C : P.CommonCharts) (z : EuclideanHalfSpace (n + 1)) (hz : z ∈ C.chart₂.source) :
    P.potential₂ (C.chart₂ z) = 0 :=
  P.gauge₂.potential_zero _ (C.target₂ (C.chart₂.map_source hz))
end ConformalPoisson

end RefPart_GaugedNormalCharts

/- Interface support: GaugedCoordinateData.lean, SHA256 5f415651b1c655d65068d28739c5d3823c55623eebe8189d5e9b7d24e8140929 -/
noncomputable section RefPart_GaugedCoordinateData

/-! In the SAME common normal charts, ALL ORIGINAL supported data have matching
actual gauged Dirichlet values and native inward-time derivatives. -/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]
  {A₁ : AnalyticProblem (n := n) (M := M₁)} {A₂ : AnalyticProblem (n := n) (M := M₂)}
  {V₁ : TopologicalSpace.Opens M₁} {V₂ : TopologicalSpace.Opens M₂}
  {D : MatchingMeasurements A₁ A₂ V₁ V₂} {x : (𝓡∂ (n + 1)).boundary M₁}

include D in
theorem BoundaryGaugePair.commonCharts_boundary_in_patch
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (C : P.CommonCharts)
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ C.chart₁.source) (hzero : z.1 0 = 0) :
    let y : (𝓡∂ (n + 1)).boundary M₁ :=
      ⟨C.chart₁ z, partialDiffeomorph_halfSpace_boundary C.chart₁ hz hzero⟩
    y ∈ P.commonPatch ∧ C.chart₂ z = (D.boundaryIdentification y : M₂) := by
  let y : (𝓡∂ (n + 1)).boundary M₁ :=
    ⟨C.chart₁ z, partialDiffeomorph_halfSpace_boundary C.chart₁ hz hzero⟩
  have hval : C.chart₂ z = (D.boundaryIdentification y : M₂) := C.boundary z hz hzero y.property
  have hz₂ : z ∈ C.chart₂.source := by rw [← C.source_eq]; exact hz
  have h₁ : (y : M₁) ∈ P.gauge₁.neighborhood := C.target₁ (C.chart₁.map_source hz)
  have h₂ : (D.boundaryIdentification y : M₂) ∈ P.gauge₂.neighborhood :=
    (congrArg (fun q : M₂ => q ∈ P.gauge₂.neighborhood) hval).mp
      (C.target₂ (C.chart₂.map_source hz₂))
  exact ⟨⟨h₁, h₂⟩, hval⟩

theorem BoundaryGaugePair.commonCharts_value_equal
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n) (C : P.CommonCharts)
    (f : BoundaryDatum (observedPatch (n := n) V₁))
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ C.chart₁.source) (hzero : z.1 0 = 0) :
    (P.solver₁ hdim).solve f.val (C.chart₁ z) =
      (P.solver₂ hdim).solve (f.val ∘ D.boundaryIdentification.symm) (C.chart₂ z) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) := TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) := TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  have hf₂ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (f.val ∘ D.boundaryIdentification.symm) :=
    f.property.1.comp (D.boundaryIdentification.symm.contMDiff.of_le (by decide))
  let y₁ : (𝓡∂ (n + 1)).boundary M₁ := ⟨C.chart₁ z, partialDiffeomorph_halfSpace_boundary C.chart₁ hz hzero⟩
  have hz₂ : z ∈ C.chart₂.source := by rw [← C.source_eq]; exact hz
  let y₂ : (𝓡∂ (n + 1)).boundary M₂ := ⟨C.chart₂ z, partialDiffeomorph_halfSpace_boundary C.chart₂ hz₂ hzero⟩
  have hy : y₂ = D.boundaryIdentification y₁ := Subtype.ext (C.boundary z hz hzero y₁.property)
  have h₁ := ((P.solver₁ hdim).correct f.val f.property.1).2.2 y₁
  have h₂ := ((P.solver₂ hdim).correct (f.val ∘ D.boundaryIdentification.symm) hf₂).2.2 y₂
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  change f.val y₁ = f.val (D.boundaryIdentification.symm y₂)
  rw [hy, Diffeomorph.symm_apply_apply]

theorem BoundaryGaugePair.commonCharts_time_equal
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (hdim : 2 ≤ n) (C : P.CommonCharts)
    (f : BoundaryDatum (observedPatch (n := n) V₁))
    {z : EuclideanHalfSpace (n + 1)} (hz : z ∈ C.chart₁.source) (hzero : z.1 0 = 0) :
    mvfderiv (𝓡∂ (n + 1)) ((P.solver₁ hdim).solve f.val ∘ C.chart₁) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) =
    mvfderiv (𝓡∂ (n + 1))
      ((P.solver₂ hdim).solve (f.val ∘ D.boundaryIdentification.symm) ∘ C.chart₂) z
      (euclideanHalfSpaceBoundaryNormalEquiv n (0, 1)) := by
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₁) := TauCeti.isManifold_boundary (n := n) (k := ω) M₁ (by decide)
  let : IsManifold (𝓡 n) ω ((𝓡∂ (n + 1)).boundary M₂) := TauCeti.isManifold_boundary (n := n) (k := ω) M₂ (by decide)
  have hf₂ : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (f.val ∘ D.boundaryIdentification.symm) :=
    f.property.1.comp (D.boundaryIdentification.symm.contMDiff.of_le (by decide))
  let u₁ := (P.solver₁ hdim).solve f.val
  let u₂ := (P.solver₂ hdim).solve (f.val ∘ D.boundaryIdentification.symm)
  have hu₁ := ((P.solver₁ hdim).correct f.val f.property.1).1
  have hu₂ := ((P.solver₂ hdim).correct (f.val ∘ D.boundaryIdentification.symm) hf₂).1
  have hz₂ : z ∈ C.chart₂.source := by rw [← C.source_eq]; exact hz
  let y₁ : (𝓡∂ (n + 1)).boundary M₁ := ⟨C.chart₁ z, partialDiffeomorph_halfSpace_boundary C.chart₁ hz hzero⟩
  let y₂ : (𝓡∂ (n + 1)).boundary M₂ := ⟨C.chart₂ z, partialDiffeomorph_halfSpace_boundary C.chart₂ hz₂ hzero⟩
  have hy : y₂ = D.boundaryIdentification y₁ := Subtype.ext (C.boundary z hz hzero y₁.property)
  have hpatch : y₁ ∈ P.commonPatch := (P.commonCharts_boundary_in_patch C hz hzero).1
  have hDN : normalDerivative D.normal₁ u₁ y₁ = normalDerivative D.normal₂ u₂ y₂ :=
    (P.gauged_normal_equal hdim f y₁ hpatch).trans
      (congrArg (normalDerivative D.normal₂ u₂) hy).symm
  have h₁ := C.geometry₁.normalDerivative hz hzero D.normal₁ P.normal_spec₁ u₁
    (hu₁.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0) (C.chart₁ z))
  have h₂ := C.geometry₂.normalDerivative hz₂ hzero D.normal₂ P.normal_spec₂ u₂
    (hu₂.mdifferentiable (by decide : (∞ : ℕ∞ω) ≠ 0) (C.chart₂ z))
  exact neg_injective (h₁.symm.trans (hDN.trans h₂))
end ConformalPoisson

end RefPart_GaugedCoordinateData

/- Interface support: LocalizedSymbolInput.lean, SHA256 bcf589af61012c2ac349e1acb1e4888cfb1879339dfe6a7cb97bec59e90e32a1 -/
noncomputable section RefPart_LocalizedSymbolInput

/-! Proposed primitive local DN calculus input. The two raw families belong
to the ACTUAL common normal charts of the ACTUAL paired q-killing gauges.
Only homogeneous boundary values and the raw composition recurrence are
supplied; no normal coefficient jets, analytic germs or seed are supplied.

Source scope: DSFKSU, §8, (8.3)--(8.8), pure metric algebra with the raw
normal first-order coefficient retained. The surrounding Lemma 8.6 has
additional normalizations; this is the unrestricted algebraic extraction,
not an assertion of that lemma verbatim. The analytical input includes
localization of actual supported DN tests and real complexification.
The first-order tangential coefficient is written using Jacobi's identity.
-/

open Set TauCeti
open scoped Manifold ContDiff

namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

/-- Comparative corollary of local factorization, classical symbol
composition, the native DN identification and uniqueness of homogeneous
components modulo smoothing. A single relative-open domain serves ALL
component indices and ALL nonzero frequencies on both sides. -/
def LocalizedDNSymbolAssumption
    [T2Space M₁] [T2Space M₂] [SecondCountableTopology M₁] [SecondCountableTopology M₂] : Prop :=
  IsCompact (univ : Set M₁) → IsCompact (univ : Set M₂) →
  IsConnected (univ : Set M₁) → IsConnected (univ : Set M₂) → 2 ≤ n →
  ∀ (A₁ : AnalyticProblem (n := n) (M := M₁))
    (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂)
    (x : (𝓡∂ (n + 1)).boundary M₁)
    (P : BoundaryGaugePair A₁ A₂ V₁ V₂ D x) (C : P.CommonCharts),
    ∃ (S : TopologicalSpace.Opens (EuclideanHalfSpace (n + 1)))
      (hS : S ≤ C.coefficientDomain),
      EuclideanHalfSpace.boundaryParam n C.boundaryBase ∈ S ∧
      ∃ (B₁ : NormalMetricField.RawSymbolFamily (C.metricField₁.restrict S hS))
        (B₂ : NormalMetricField.RawSymbolFamily (C.metricField₂.restrict S hS)),
        ∀ r ξ, ξ ≠ 0 → ∀ z ∈ S, z.1 0 = 0 →
          B₁.component r ξ z = B₂.component r ξ z
end ConformalPoisson

end RefPart_LocalizedSymbolInput

/- Interface support: CompactNativeTopology.lean, SHA256 65b514d46b6e7a3eeedefb74798c9b73ec03560dc16d8b647a08ac5296db24a7 -/
noncomputable section RefPart_CompactNativeTopology

/-! Countability, compatible metrizability and compact subsequences are
library consequences of the paper's compact Hausdorff manifold geometry.
They are not extra hypotheses in the final theorem. -/

open Set Filter Topology TopologicalSpace
open scoped Manifold

namespace ConformalPoisson
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

include n in
theorem native_secondCountable_of_compact (hM : IsCompact (univ : Set M)) :
    SecondCountableTopology M := by
  let : CompactSpace M := isCompact_univ_iff.mp hM
  let := (𝓡∂ (n + 1)).secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace (n + 1)) M

include n in
theorem native_metrizable_of_compact [T2Space M] (hM : IsCompact (univ : Set M)) :
    MetrizableSpace M := by
  let : CompactSpace M := isCompact_univ_iff.mp hM
  exact Manifold.metrizableSpace (𝓡∂ (n + 1)) M

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [T2Space M₁] [T2Space M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]

include n in
theorem exists_compact_native_image_subsequence
    (hM₁ : IsCompact (univ : Set M₁)) (hM₂ : IsCompact (univ : Set M₂))
    {B : Set M₁} {x : M₁} (hx : x ∈ closure B) (J : M₁ → M₂) :
    ∃ a : ℕ → M₁, (∀ k, a k ∈ B) ∧ Tendsto a atTop (𝓝 x) ∧
      ∃ y : M₂, ∃ b : ℕ → ℕ, StrictMono b ∧
        Tendsto (fun k => J (a (b k))) atTop (𝓝 y) := by
  let := native_metrizable_of_compact (n := n) hM₁
  let := native_metrizable_of_compact (n := n) hM₂
  obtain ⟨a, ha, hax⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨y, _, b, hb, hby⟩ := hM₂.isSeqCompact (fun k : ℕ => mem_univ (J (a k)))
  exact ⟨a, ha, hax, y, b, hb, hby⟩
end ConformalPoisson

end RefPart_CompactNativeTopology

/- Sole selected open claim. -/
noncomputable section
open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [T2Space M₁] [T2Space M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

variable [CompactSpace M₁] [CompactSpace M₂]
  [MeasurableSpace M₁] [BorelSpace M₁] [MeasurableSpace M₂] [BorelSpace M₂]
  [MeasurableSpace ((𝓡∂ (n + 1)).boundary M₁)] [BorelSpace ((𝓡∂ (n + 1)).boundary M₁)]
  [MeasurableSpace ((𝓡∂ (n + 1)).boundary M₂)] [BorelSpace ((𝓡∂ (n + 1)).boundary M₂)]

local instance mainBoundaryCompact₁ : CompactSpace ((𝓡∂ (n + 1)).boundary M₁) := compactSpace_nativeBoundary
local instance mainBoundaryCompact₂ : CompactSpace ((𝓡∂ (n + 1)).boundary M₂) := compactSpace_nativeBoundary

set_option maxHeartbeats 2000000 in
theorem theorem_1_1
    (hn : 2 ≤ n)
    (hconnected₁ : IsConnected (univ : Set M₁)) (hconnected₂ : IsConnected (univ : Set M₂))
    (A₁ : AnalyticProblem (n := n) (M := M₁)) (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂) : TheoremOneOneResult A₁ A₂ V₁ V₂ D := by
  sorry
end ConformalPoisson
end
