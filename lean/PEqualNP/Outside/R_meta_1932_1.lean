import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1932_1
    (zero : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [false]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (single : ∀ p : Fin 10, ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [GateOp.or.eval
          (List.map (fun i : ℕ => w.getD i false) [p.val])]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (pair : ∀ p q : Fin 10, ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [GateOp.or.eval
          (List.map (fun i : ℕ => w.getD i false) [p.val, q.val])]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
            (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
            (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (orEval : ∀ l : List Bool, l.length ≤ 2 →
      GateOp.or.eval l = l.any id)
    : ∀ (x1 : List ℕ), x1.length ≤ 2 →
      ∀ x3 : Circuit, FanInTwo x3 → x3.size ≤ 13 →
        ∃ x6 : Fin 9 → Bool,
          have x7 : List Bool :=
            List.ofFn x6 ++ [x6 0 && x6 2]
          x3.eval (x7 ++ [GateOp.or.eval
            (List.map (fun x8 : ℕ => x7.getD x8 false) x1)]) ≠
            ((x6 0 && x6 1) || (x6 1 && x6 2) || (x6 2 && x6 3) ||
              (x6 3 && x6 4) || (x6 4 && x6 0) || (x6 0 && x6 5) ||
              (x6 1 && x6 6) || (x6 2 && x6 7) || (x6 3 && x6 8) ||
              (x6 5 && x6 7) || (x6 6 && x6 8) || (x6 8 && x6 5)) := by
  intro pins arity C fan small
  rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · obtain ⟨x, hx⟩ := zero C fan small
    refine ⟨x, ?_⟩
    have hgate : GateOp.or.eval
        (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
          []) =
        (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
          []).any id :=
      orEval _ (by simp)
    dsimp only at ⊢
    rw [hgate]
    simpa using hx
  · by_cases ha : a < 10
    · let p : Fin 10 := ⟨a, ha⟩
      obtain ⟨x, hx⟩ := single p C fan small
      refine ⟨x, ?_⟩
      simp only [p] at hx
      have hgate : GateOp.or.eval
          (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
            [a]) =
          (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
            [a]).any id :=
        orEval _ (by simp)
      have hgateHx : GateOp.or.eval
          (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
            [a]) =
          (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
            [a]).any id :=
        orEval _ (by simp)
      rw [hgateHx] at hx
      dsimp only at ⊢
      rw [hgate]
      simpa using hx
    · obtain ⟨x, hx⟩ := zero C fan small
      refine ⟨x, ?_⟩
      have hfalse : (List.ofFn x ++ [x 0 && x 2]).getD a false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · simp
          omega
      have hgate : GateOp.or.eval
          (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
            [a]) =
          (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
            [a]).any id :=
        orEval _ (by simp)
      dsimp only at ⊢
      rw [hgate]
      simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at ⊢
      rw [hfalse]
      simpa using hx
  · by_cases ha : a < 10
    · by_cases hb : b < 10
      · let p : Fin 10 := ⟨a, ha⟩
        let q : Fin 10 := ⟨b, hb⟩
        obtain ⟨x, hx⟩ := pair p q C fan small
        refine ⟨x, ?_⟩
        simp only [p, q] at hx
        have hgate : GateOp.or.eval
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]) =
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]).any id :=
          orEval _ (by simp)
        have hgateHx : GateOp.or.eval
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [a, b]) =
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [a, b]).any id :=
          orEval _ (by simp)
        rw [hgateHx] at hx
        dsimp only at ⊢
        rw [hgate]
        simpa using hx
      · let p : Fin 10 := ⟨a, ha⟩
        obtain ⟨x, hx⟩ := single p C fan small
        refine ⟨x, ?_⟩
        have hfalse : (List.ofFn x ++ [x 0 && x 2]).getD b false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
          · rfl
          · simp
            omega
        simp only [p] at hx
        have hgate : GateOp.or.eval
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]) =
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]).any id :=
          orEval _ (by simp)
        have hgateHx : GateOp.or.eval
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [a]) =
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [a]).any id :=
          orEval _ (by simp)
        rw [hgateHx] at hx
        dsimp only at ⊢
        rw [hgate]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at ⊢
        rw [hfalse]
        simpa using hx
    · by_cases hb : b < 10
      · let q : Fin 10 := ⟨b, hb⟩
        obtain ⟨x, hx⟩ := single q C fan small
        refine ⟨x, ?_⟩
        have hfalse : (List.ofFn x ++ [x 0 && x 2]).getD a false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
          · rfl
          · simp
            omega
        simp only [q] at hx
        have hgate : GateOp.or.eval
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]) =
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]).any id :=
          orEval _ (by simp)
        have hgateHx : GateOp.or.eval
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [b]) =
            (List.map (fun i : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD i false)
              [b]).any id :=
          orEval _ (by simp)
        rw [hgateHx] at hx
        dsimp only at ⊢
        rw [hgate]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at ⊢
        rw [hfalse]
        simpa using hx
      · obtain ⟨x, hx⟩ := zero C fan small
        refine ⟨x, ?_⟩
        have hfa : (List.ofFn x ++ [x 0 && x 2]).getD a false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
          · rfl
          · simp
            omega
        have hfb : (List.ofFn x ++ [x 0 && x 2]).getD b false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
          · rfl
          · simp
            omega
        have hgate : GateOp.or.eval
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]) =
            (List.map (fun x8 : ℕ => (List.ofFn x ++ [x 0 && x 2]).getD x8 false)
              [a, b]).any id :=
          orEval _ (by simp)
        dsimp only at ⊢
        rw [hgate]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at ⊢
        rw [hfa, hfb]
        simpa using hx
  · simp at arity
