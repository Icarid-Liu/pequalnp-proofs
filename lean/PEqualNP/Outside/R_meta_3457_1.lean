import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3457_1
    (minimize : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧
              z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
              PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)
      Good C →
      ∃ M, Good M ∧ ∀ E, Good E → M.size ≤ E.size)
    (improve : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧
              z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
              PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)
      Good C →
      (∃ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ p l : Fin N, ¬ I p l ∧
          (C.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = true) →
      ∃ D, Good D ∧ D.size < C.size) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ p : Fin N,
        (C.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N,
        (C.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
      D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧
            z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = false) ∧
      (∀ j < D.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N,
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N,
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _inst C hexcl hmono hread hfun hsingle
  let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
    PEqualNP.MetaComplexity.Monotone2 D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
    D.size ≤ C.size ∧
    (∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    (∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ p : Fin N,
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N,
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)
  have hCgood : Good C := ⟨hmono, hread, le_rfl, hfun, hsingle⟩
  have hmin : ∃ M, Good M ∧ ∀ E, Good E → M.size ≤ E.size := by
    simpa [Good] using minimize N I C hexcl hCgood
  obtain ⟨M, hMgood, hMin⟩ := hmin
  rcases hMgood with ⟨hMmono, hMread, hMsize, hMfun, hMsingle⟩
  have hMgoodM :
      (fun D =>
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ M.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧
              z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
              PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)) M :=
    ⟨hMmono, hMread, le_rfl, hMfun, hMsingle⟩
  let Bad : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun D =>
    ∃ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∃ p l : Fin N, ¬ I p l ∧
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
            (N + N + j) false = true
  by_cases hbad : Bad M
  · have improve' : ∃ D, Good D ∧ D.size < M.size := by
      obtain ⟨D, hD, hlt⟩ :=
        improve N I M hexcl (by simpa [Good] using hMgoodM) (by simpa [Bad] using hbad)
      rcases hD with ⟨hDmono, hDread, hDsizeM, hDfun, hDsingle⟩
      exact ⟨D, ⟨hDmono, hDread, le_trans hDsizeM hMsize, hDfun, hDsingle⟩, hlt⟩
    obtain ⟨D, hDgood, hlt⟩ := improve'
    exact absurd (hMin D hDgood) (not_le_of_gt hlt)
  · refine ⟨M, hMmono, hMread, hMsize, hMfun, ?_, hMsingle⟩
    intro j hj hop p l hnil
    by_contra hfalse
    have htrue :
        (M.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
            (N + N + j) false = true := by
      cases hb :
          (M.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false
      · exact False.elim (hfalse hb)
      · rfl
    exact hbad ⟨j, hj, hop, p, l, hnil, htrue⟩
