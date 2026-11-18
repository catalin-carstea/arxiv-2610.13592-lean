module
public import Solution
noncomputable section
open Bundle Set TauCeti Filter Topology
open scoped Manifold ContDiff
@[expose] public section
namespace ConformalPoisson
variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [T2Space M₁] [T2Space M₂]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M₁] [ChartedSpace (EuclideanHalfSpace (n + 1)) M₂]
  [IsManifold (𝓡∂ (n + 1)) ω M₁] [IsManifold (𝓡∂ (n + 1)) ω M₂]

variable [CompactSpace M₁] [CompactSpace M₂]
  [MeasurableSpace M₁] [BorelSpace M₁] [MeasurableSpace M₂] [BorelSpace M₂]
  [MeasurableSpace ((𝓡∂ (n + 1)).boundary M₁)] [BorelSpace ((𝓡∂ (n + 1)).boundary M₁)]
  [MeasurableSpace ((𝓡∂ (n + 1)).boundary M₂)] [BorelSpace ((𝓡∂ (n + 1)).boundary M₂)]

local instance consumerBoundaryCompact₁ : CompactSpace ((𝓡∂ (n + 1)).boundary M₁) := compactSpace_nativeBoundary
local instance consumerBoundaryCompact₂ : CompactSpace ((𝓡∂ (n + 1)).boundary M₂) := compactSpace_nativeBoundary

theorem commonPointAndScale
    (hn : 2 ≤ n)
    (hconnected₁ : IsConnected (univ : Set M₁)) (hconnected₂ : IsConnected (univ : Set M₂))
    (A₁ : AnalyticProblem (n := n) (M := M₁)) (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂) :
    ∃ P : GaugePair (n := n) V₁ V₂,
      P.RealizesTheorem V₁ V₂ D.boundaryIdentification A₁.smoothMetric A₂.smoothMetric
        A₁.potential A₂.potential D.solver₁ D.solver₂ D.normal₁ ∧
      ∀ x : observedDomain (𝓡∂ (n + 1)) V₁,
        ∃ y : observedDomain (𝓡∂ (n + 1)) V₂, ∃ a : ℝ,
          y = P.map x ∧ a = P.multiplier x ∧ 0 < a ∧
          ∀ f : BoundaryDatum (observedPatch (n := n) V₁),
            D.solver₁.solve f.val x = a * D.solver₂.solve (f.val ∘ D.boundaryIdentification.symm) y := by
  obtain ⟨P, hP, _⟩ := theorem_1_1 hn hconnected₁ hconnected₂ A₁ A₂ V₁ V₂ D
  refine ⟨P, hP, fun x => ⟨P.map x, P.multiplier x, rfl, rfl, P.positive x, ?_⟩⟩
  intro f
  exact hP.2.2.2 f x
end ConformalPoisson
