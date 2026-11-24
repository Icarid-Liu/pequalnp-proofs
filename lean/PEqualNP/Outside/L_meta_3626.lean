import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3626

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev Lit (n : ℕ) := Bool × Option (Fin n)

def litEval {n : ℕ} (l : Lit n) (x : Fin n → Bool) : Bool :=
  match l.2 with
  | none => l.1
  | some i => (x i == l.1)

def litNot {n : ℕ} (l : Lit n) : Lit n := (!l.1, l.2)

def initLits {n : ℕ} (xs : List (Fin n)) : List (Lit n) :=
  xs.map fun i => (true, some i)

def litStep {n : ℕ} (ws : List (Lit n)) (g : Gate) : List (Lit n) :=
  ws ++ [match g.inputs.head? with
    | none => (true, none)
    | some i => litNot (ws.getD i (false, none))]

def nonNotGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP nonNotGate

lemma countP_nonNotCount (gs : List Gate) :
    gs.countP (fun g => GateOp.rec Bool.true Bool.true Bool.false
      (fun _ => Bool.true) Bool.true g.op) = nonNotCount gs := by
  unfold nonNotCount nonNotGate
  congr 1
  funext g
  cases g.op <;> rfl

lemma litEval_init {n : ℕ} (xs : List (Fin n)) (x : Fin n → Bool) :
    (initLits xs).map (fun l => litEval l x) = xs.map x := by
  simp [initLits, litEval]

lemma litEval_not {n : ℕ} (l : Lit n) (x : Fin n → Bool) :
    litEval (litNot l) x = !litEval l x := by
  rcases l with ⟨b, o⟩
  cases o with
  | none => simp [litNot, litEval]
  | some i =>
      cases b <;> cases x i <;> simp [litNot, litEval]

lemma litEval_getD_map {n : ℕ} (ws : List (Lit n)) (i : ℕ) (x : Fin n → Bool) :
    litEval (ws.getD i (false, none)) x =
      (ws.map (fun l => litEval l x)).getD i false := by
  induction ws generalizing i with
  | nil => simp [litEval]
  | cons l ws ih =>
      cases i with
      | zero => simp [litEval]
      | succ i =>
          change litEval (ws.getD i (false, none)) x =
            (ws.map (fun l => litEval l x)).getD i false
          exact ih i

lemma litEval_getElem?_map {n : ℕ} (ws : List (Lit n)) (i : ℕ)
    (x : Fin n → Bool) :
    litEval ((ws[i]?).getD (false, none)) x =
      (((ws.map (fun l => litEval l x))[i]?).getD false) := by
  induction ws generalizing i with
  | nil => simp [litEval]
  | cons l ws ih =>
      cases i with
      | zero => simp [litEval]
      | succ i =>
          simpa using ih i

lemma map_litStep {n : ℕ} (ws : List (Lit n)) (g : Gate)
    (notGate : g.op = GateOp.not) (x : Fin n → Bool) :
    (litStep ws g).map (fun l => litEval l x) =
      (ws.map (fun l => litEval l x)) ++
        [g.op.eval (g.inputs.map fun i =>
          (ws.map (fun l => litEval l x)).getD i false)] := by
  rw [notGate]
  cases hins : g.inputs with
  | nil =>
    simp [litStep, hins, GateOp.eval, litEval]
  | cons a as =>
    simp [litStep, hins, GateOp.eval, litEval_not, litEval_getElem?_map]

lemma map_foldl_litStep_from {n : ℕ} (gs : List Gate)
    (allNot : ∀ g ∈ gs, g.op = GateOp.not)
    (ws : List (Lit n)) (x : Fin n → Bool) :
    (gs.foldl litStep ws).map (fun l => litEval l x) =
      gs.foldl (fun ws g => ws ++
        [g.op.eval (g.inputs.map fun i => ws.getD i false)])
        (ws.map (fun l => litEval l x)) := by
  induction gs generalizing ws with
  | nil =>
    rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hh => allNot h (by simp [hh])) (litStep ws g)]
    rw [map_litStep _ _ (allNot g (by simp)) x]

lemma map_foldl_litStep {n : ℕ} (gs : List Gate)
    (allNot : ∀ g ∈ gs, g.op = GateOp.not)
    (xs : List (Fin n)) (x : Fin n → Bool) :
    (gs.foldl litStep (initLits xs)).map (fun l => litEval l x) =
      gs.foldl (fun ws g => ws ++
        [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (xs.map x) := by
  simpa only [litEval_init] using
    map_foldl_litStep_from gs allNot (initLits xs) x

lemma eval_eq_litEval {n : ℕ} (C : Circuit) (xs : List (Fin n))
    (allNot : ∀ g ∈ C.gates, g.op = GateOp.not) (x : Fin n → Bool) :
    C.eval (xs.map x) =
      litEval ((C.gates.foldl litStep (initLits xs)).getD C.output (false, none)) x := by
  unfold Circuit.eval Circuit.wires
  rw [← map_foldl_litStep C.gates allNot xs x]
  exact (litEval_getD_map _ _ _).symm

lemma litEval_update_eq_of_ne {n : ℕ} (l : Lit n) (i : Fin n) (b : Bool)
    (x : Fin n → Bool) (notI : l.2 ≠ some i) :
    litEval l (Function.update x i b) = litEval l x := by
  rcases l with ⟨v, o⟩
  cases o with
  | none =>
    rfl
  | some j =>
    have hji : j ≠ i := by
      intro h
      exact notI (by simp [h])
    simp [litEval, Function.update_of_ne hji]

lemma not_all_not_of_witness {m : ℕ} (C : Circuit) (i : Fin (m + 1))
    (xs : List (Fin (m + 1))) (allNot : ∀ g ∈ C.gates, g.op = GateOp.not)
    (depends : ∃ x : Fin (m + 1) → Bool,
      C.eval (xs.map (Function.update x i true)) ≠
        C.eval (xs.map (Function.update x i false)))
    (restricted : ∃ x y : Fin m → Bool,
      C.eval (xs.map (i.insertNth false x)) ≠
        C.eval (xs.map (i.insertNth false y))) : False := by
  let out := (C.gates.foldl litStep (initLits xs)).getD C.output (false, none)
  have litDepends : ∃ x : Fin (m + 1) → Bool,
      litEval out (Function.update x i true) ≠
        litEval out (Function.update x i false) := by
    obtain ⟨x, hx⟩ := depends
    exact ⟨x, by simpa only [eval_eq_litEval C xs allNot] using hx⟩
  have outputIndex : out.2 = some i := by
    by_contra hne
    obtain ⟨x, hx⟩ := litDepends
    exact hx ((litEval_update_eq_of_ne out i true x hne).trans
      (litEval_update_eq_of_ne out i false x hne).symm)
  obtain ⟨x, y, hxy⟩ := restricted
  apply hxy
  rw [eval_eq_litEval C xs allNot, eval_eq_litEval C xs allNot]
  change litEval out (i.insertNth false x) =
    litEval out (i.insertNth false y)
  rcases out with ⟨v, o⟩
  simp only at outputIndex ⊢
  rw [outputIndex]
  cases v <;> simp [litEval, Fin.insertNth_apply_same]

end PEqualNP.Outside.L_meta_3626

theorem PEqualNP.Outside.L_meta_3626 :
    have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1;
    ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),
      PEqualNP.MetaComplexity.FanInTwo x4 →
        have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);
        (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) →
        (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) →
        ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧
          x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates := by
  intro _countFunction m i C xs hfan _restrictedFun depends restricted
  have hpos : 0 < PEqualNP.Outside.L_meta_3626.nonNotCount C.gates := by
    by_contra hnot
    have hzero : PEqualNP.Outside.L_meta_3626.nonNotCount C.gates = 0 := by omega
    have allNot : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg
      have hgFalse := (List.countP_eq_zero.mp hzero) g hg
      have hop := (hfan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · simp [PEqualNP.Outside.L_meta_3626.nonNotGate, h] at hgFalse
      · simp [PEqualNP.Outside.L_meta_3626.nonNotGate, h] at hgFalse
      · exact h
    exact PEqualNP.Outside.L_meta_3626.not_all_not_of_witness C i xs allNot depends restricted
  refine ⟨⟨[], 0⟩, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · have hcount :
        _countFunction = PEqualNP.Outside.L_meta_3626.nonNotCount := by
      funext gs
      exact PEqualNP.Outside.L_meta_3626.countP_nonNotCount gs
    rw [hcount]
    simpa [PEqualNP.Outside.L_meta_3626.nonNotCount] using hpos
