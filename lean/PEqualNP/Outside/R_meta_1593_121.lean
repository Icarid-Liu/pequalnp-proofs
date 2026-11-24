import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1593_121
    (monotonize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      FanInTwo C →
      circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size)
    (represent : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (D : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      G.edgeFinset.Nonempty →
      Monotone2 D →
      circuitFun n D = graphFun G ∅ →
      ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
        (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (T : List (Finset (Fin n))),
          B = P ++ a :: T →
            ∃ b c : Finset (Fin n), a = b ∪ c ∧
              (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
        (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧
          ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
        (∀ z : Fin n → Bool,
          (∃ i, (∃ u ∈ X i, z u = true) ∧ ∃ v ∈ Y i, z v = true) ↔
            ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
        B.length + 2 * m ≤ D.size + 1) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ A : Finset (Fin n),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) →
      (∃ u v, G.Adj u v) →
      ∀ s, HasCircuitSize n (graphFun G ∅) s →
        ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
          (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n))
              (T : List (Finset (Fin n))),
            B = P ++ a :: T →
              ∃ b c : Finset (Fin n), a = b ∪ c ∧
                (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
          (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧
            ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
          (∀ z : Fin n → Bool,
            (∃ i, (∃ u ∈ X i, z u = true) ∧ ∃ v ∈ Y i, z v = true) ↔
              ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true) ∧
          B.length + 2 * m ≤ s + 1 := by
  intro n G _ A hdegree hgirth hmark hEdge s has
  classical
  obtain ⟨C, fan, size, computes⟩ := has
  have computes' : circuitFun n C = graphFun G ∅ := by
    funext z
    exact computes z
  obtain ⟨D, mono, computesD, sizeD⟩ :=
    monotonize n G A C hdegree hgirth hmark hEdge fan computes'
  have edgeNe : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hEdge
    exact ⟨s(u, v), by simpa [SimpleGraph.mem_edgeFinset] using huv⟩
  obtain ⟨B, m, X, Y, built, ready, truth, cost⟩ :=
    represent n G D hgirth edgeNe mono computesD
  exact ⟨B, m, X, Y, built, ready, truth, by omega⟩
