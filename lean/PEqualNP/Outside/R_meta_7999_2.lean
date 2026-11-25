import PEqualNP.Defs

namespace PEqualNP.Outside

def R_meta_7999_2.Context
    (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  C.size ≤ 27 ∧
  PEqualNP.TopForm.IsAO2 14 C ∧
  (∀ j < C.size,
    PEqualNP.TopForm.opnd C j (0 : Fin 2) ≠
      PEqualNP.TopForm.opnd C j (1 : Fin 2)) ∧
  (∀ x : Fin 14 → Bool,
    C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 7,
        (a = b ∨ a = b + (1 : Fin 7) ∨ a = b + (3 : Fin 7)) ∧
        x (Fin.castAdd 7 a) = true ∧ x (Fin.natAdd 7 b) = true) ∧
  ¬PEqualNP.ReadK.IsSingleRead C 14
    (fun i : ℕ => decide (7 ≤ i)) [((0 : ℕ), (7 : ℕ))]

def R_meta_7999_2.First
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (a b : ℕ) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.gateAt C 0 =
    { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] :
      PEqualNP.CircuitLowerBounds.Gate }

theorem R_meta_7999_2 :
    (∀ C,
      R_meta_7999_2.Context C →
      R_meta_7999_2.First C 0 7 →
      False) →
    (∀ C,
      R_meta_7999_2.Context C →
      R_meta_7999_2.First C 0 11 →
      False) →
    (∀ C,
      R_meta_7999_2.Context C →
      R_meta_7999_2.First C 1 8 →
      False) →
    (∀ C,
      R_meta_7999_2.Context C →
      R_meta_7999_2.First C 2 8 →
      False) →
    (∀ C,
      R_meta_7999_2.Context C →
      (∃ p ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (11 : ℕ)),
          ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (8 : ℕ))],
        R_meta_7999_2.First C p.1 p.2) →
      False) := by
  intro h07 h011 h18 h28 C hC hfirst
  rcases hfirst with ⟨⟨a, b⟩, hmem, hgate⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · cases h
    exact h07 C hC hgate
  · cases h
    exact h011 C hC hgate
  · cases h
    exact h18 C hC hgate
  · cases h
    exact h28 C hC hgate

end PEqualNP.Outside
