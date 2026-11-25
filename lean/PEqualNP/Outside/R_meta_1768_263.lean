import PEqualNP.Defs

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- The two bounds are the same statements used for L-meta-5326 and L-meta-5328.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1768_263
    (bothSing : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C,
          wireVal n C (opnd C a 0) (pairInput u u) = true ∧
          wireVal n C (opnd C a 1) (pairInput v v) = true)).card ≤ k * (C.size + 1))
    (oneSing : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ g ∈ junk G C, u ∈ wmax G C g ∧
          gateVal n C g (pairInput u v) = true ∧
          gateVal n C g (pairInput u u) = false ∧
          gateVal n C g (pairInput v v) = false)).card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  -- Wire evaluation and OR reachability are localized from L-meta-3805.
  have foldl_snoc_length {α β : Type} (h : List α → β → α) (gs : List β) (init : List α) :
      (gs.foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + gs.length := by
    induction gs generalizing init with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, List.length_append, List.length_singleton]
      omega

  have foldl_snoc_getD_lt {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
      (i : ℕ) (d : α) (hi : i < init.length) :
      (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD i d = init.getD i d := by
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hi' : i < (init ++ [h init g]).length := by
        rw [List.length_append, List.length_singleton]; omega
      rw [ih (init ++ [h init g]) hi']
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have foldl_snoc_getD_add {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
      (j : ℕ) (d : α) (hj : j < gs.length) :
      (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD (init.length + j) d =
        h ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init) (gs[j]) := by
    induction gs generalizing init j with
    | nil => simp at hj
    | cons g gs ih =>
      cases j with
      | zero =>
        simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, Nat.add_zero]
        have hlt : init.length < (init ++ [h init g]).length := by
          rw [List.length_append, List.length_singleton]; omega
        rw [foldl_snoc_getD_lt h gs (init ++ [h init g]) init.length d hlt]
        simp [List.getD_eq_getElem?_getD]
      | succ j =>
        simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
        have hlen : (init ++ [h init g]).length = init.length + 1 := by simp
        have hj' : j < gs.length := by simp at hj; omega
        have hidx : init.length + (j + 1) = (init ++ [h init g]).length + j := by rw [hlen]; omega
        rw [hidx]
        exact ih (init ++ [h init g]) j hj'

  have foldl_snoc_take_getD {α β : Type} (h : List α → β → α) (gs : List β) (init : List α)
      (j k : ℕ) (d : α) (hj : j ≤ gs.length) (hk : k < init.length + j) :
      ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).getD k d =
        (gs.foldl (fun acc g => acc ++ [h acc g]) init).getD k d := by
    have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    have hlen : ((gs.take j).foldl (fun acc g => acc ++ [h acc g]) init).length = init.length + j := by
      rw [foldl_snoc_length, List.length_take, Nat.min_eq_left hj]
    rw [foldl_snoc_getD_lt h (gs.drop j) _ k d (by omega)]

  have gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
      gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]

  have opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
      opnd C j b ∈ (gateAt C j).inputs := by
    have hlen : (gateAt C j).inputs.length = 2 := by
      rw [gateAt_eq_getElem C j hj]
      exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
    unfold opnd
    have hb : (b : ℕ) < (gateAt C j).inputs.length := by omega
    rw [List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem hb

  have opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
      opnd C j b < n + j :=
    hAO.2.1 j hj (opnd C j b) (opnd_mem_inputs hAO j hj b)

  have inputs_eq_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hlen : (gateAt C j).inputs.length = 2 := by
      rw [gateAt_eq_getElem C j hj]
      exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
    unfold opnd
    rw [hpq]
    rfl

  have wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
      wireVal n C i.val x = x i := by
    unfold wireVal Circuit.wires
    have hlt : i.val < (List.ofFn x).length := by simp
    rw [foldl_snoc_getD_lt (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      C.gates (List.ofFn x) i.val false hlt]
    simp [List.getD_eq_getElem?_getD, i.isLt]

  have gateVal_eq_wireVal {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
      gateVal n C j x = wireVal n C (n + j) x := rfl

  have gateVal_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
      gateVal n C j x = (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
    unfold gateVal Circuit.wires
    let f : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)
    have hlen : (List.ofFn x).length = n := by simp
    have hstep := foldl_snoc_getD_add f C.gates (List.ofFn x) j false hj
    rw [hlen] at hstep
    change (C.gates.foldl (fun acc g => acc ++ [f acc g]) (List.ofFn x)).getD (n + j) false = _
    rw [hstep, ← gateAt_eq_getElem C j hj]
    simp only [f]
    rw [inputs_eq_two hAO j hj]
    simp only [List.map_cons, List.map_nil]
    have h0 : opnd C j 0 < (List.ofFn x).length + j := by rw [hlen]; exact opnd_lt hAO j hj 0
    have h1 : opnd C j 1 < (List.ofFn x).length + j := by rw [hlen]; exact opnd_lt hAO j hj 1
    rw [foldl_snoc_take_getD f C.gates (List.ofFn x) j (opnd C j 0) false (Nat.le_of_lt hj) h0]
    rw [foldl_snoc_take_getD f C.gates (List.ofFn x) j (opnd C j 1) false (Nat.le_of_lt hj) h1]
    rfl

  have gateVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
      gateVal n C j x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
    rw [gateVal_eval hAO j hj x, hand]
    change [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x].all id = _
    simp

  have gateVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
      gateVal n C j x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
    rw [gateVal_eval hAO j hj x, hor]
    change [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x].any id = _
    simp

  have orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
    unfold orSets orStep
    simpa using foldl_snoc_length
      (fun (cs : List (List ℕ)) (g : Gate) =>
        cs.length :: (if g.op = GateOp.or then
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
          else []))
      C.gates []

  have orReaches_iff_gate (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length) :
      OrReaches n C (n + j) g ↔
        g = j ∨ ((gateAt C j).op = GateOp.or ∧
          ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
    let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
      cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq _ _)
        ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []))
        [])
    unfold OrReaches orSets orStep
    simp only [Nat.le_add_right, Nat.add_sub_cancel_left, true_and]
    change g ∈ (C.gates.foldl (fun acc g => acc ++ [f acc g]) []).getD j [] ↔ _
    have hstep := foldl_snoc_getD_add f C.gates [] j [] hj
    simp only [List.length_nil, Nat.zero_add] at hstep
    rw [hstep, ← gateAt_eq_getElem C j hj]
    have hplen : ((C.gates.take j).foldl (fun acc g => acc ++ [f acc g]) []).length = j := by
      rw [foldl_snoc_length, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    simp only [f, hplen, List.mem_cons]
    constructor
    · rintro (rfl | hmem)
      · exact Or.inl rfl
      · right
        split_ifs at hmem with hor
        · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hmem
          rcases hmem with ⟨w, ⟨hw, hnw, hlt⟩, hg⟩
          have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
          rw [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub] at hg
          exact ⟨hor, w, hw, hnw, hlt, hnw, hg⟩
        · simp at hmem
    · rintro (rfl | ⟨hor, w, hw, hnw, hlt, _, hg⟩)
      · exact Or.inl rfl
      · right
        rw [ite_eq_left hor]
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        refine ⟨w, ⟨hw, hnw, hlt⟩, ?_⟩
        have hsub : w - n < ([] : List (List ℕ)).length + j := by simp; omega
        rwa [foldl_snoc_take_getD f C.gates [] j (w - n) [] (Nat.le_of_lt hj) hsub]

  have orReaches_bounds (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
      n ≤ w ∧ w - n < C.gates.length ∧ g ≤ w - n := by
    have hnw : n ≤ w := h.1
    have hlt : w - n < C.gates.length := by
      by_contra hge
      have hge' : (orSets n C).length ≤ w - n := by rw [orSets_length]; omega
      have hmem := h.2
      rw [List.getD_eq_default _ _ hge'] at hmem
      simp at hmem
    suffices ∀ j < C.gates.length, OrReaches n C (n + j) g → g ≤ j by
      have hwn : n + (w - n) = w := Nat.add_sub_of_le hnw
      exact ⟨hnw, hlt, this (w - n) hlt (by rwa [hwn])⟩
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hreach
      rw [orReaches_iff_gate n C j g hj] at hreach
      rcases hreach with rfl | ⟨_, w', _, hnw', hlt', hr'⟩
      · exact le_rfl
      · have hsub : w' - n < j := by omega
        have hwn' : n + (w' - n) = w' := Nat.add_sub_of_le hnw'
        have hle := ih (w' - n) hsub (by omega) (by rwa [hwn'])
        omega

  have orReaches_gateVal {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (w g : ℕ) (x : Fin n → Bool) (h : OrReaches n C w g) (hg : gateVal n C g x = true) :
      wireVal n C w x = true := by
    obtain ⟨hnw, hlt, _⟩ := orReaches_bounds n C w g h
    have hwn : n + (w - n) = w := Nat.add_sub_of_le hnw
    rw [← hwn] at h ⊢
    generalize w - n = j at hlt h ⊢
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rw [orReaches_iff_gate n C j g hlt] at h
      rcases h with rfl | ⟨hor, w', hw', hnw', hlt', hr'⟩
      · exact hg
      · rw [← gateVal_eq_wireVal, gateVal_or hAO j hlt hor x]
        have hwn' : n + (w' - n) = w' := Nat.add_sub_of_le hnw'
        have hwv : wireVal n C w' x = true := by
          rw [← hwn'] at hr' ⊢
          exact ih (w' - n) (by omega) (by omega) hr'
        rw [inputs_eq_two hAO j hlt] at hw'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl
        · simp [hwv]
        · simp [hwv]

  have orIn_sound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
      (w : ℕ) (u : Fin n) (x : Fin n → Bool) (hu : u ∈ orIn n C w) (hx : x u = true) :
      wireVal n C w x = true := by
    unfold orIn at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases hu with rfl | ⟨k, hk, hreach, hor, hmem⟩
    · rw [wireVal_input]; exact hx
    · apply orReaches_gateVal hAO w k x hreach
      rw [gateVal_or hAO k hk hor x]
      rw [inputs_eq_two hAO k hk] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1
      · rw [← h0, wireVal_input]; simp [hx]
      · rw [← h1, wireVal_input]; simp [hx]

  have mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} {a : ℕ} :
      a ∈ tops G C ↔ a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    unfold tops gatesWhere
    simp (config := {congrConsts := false}) only [Finset.mem_filter, Finset.mem_range]

  have graphFun_empty_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    unfold graphFun
    simp

  have top_wmax {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} (hAO : IsAO2 n C) {a g : ℕ} {b : Fin 2} {u : Fin n}
      (ha : a ∈ tops G C) (hu : u ∈ side C a b) (hr : OrReaches n C (opnd C a (1 - b)) g)
      (x : Fin n → Bool) (hxu : x u = true) (hxg : gateVal n C g x = true) :
      ∃ v1 v2 : Fin n, G.Adj v1 v2 ∧ x v1 = true ∧ x v2 = true := by
    obtain ⟨halt, haand, habf⟩ := mem_tops_iff.1 ha
    have h1 : wireVal n C (opnd C a b) x = true := orIn_sound hAO (opnd C a b) u x hu hxu
    have h2 : wireVal n C (opnd C a (1 - b)) x = true := orReaches_gateVal hAO (opnd C a (1 - b)) g x hr hxg
    have ha_true : gateVal n C a x = true := by
      rw [gateVal_and hAO a halt haand x, Bool.and_eq_true]
      fin_cases b
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
    exact (graphFun_empty_true x).1 (habf x ha_true)

  obtain ⟨s, singleBound⟩ := bothSing
  obtain ⟨p, pairBound⟩ := oneSing
  refine ⟨s + p, ?_⟩
  intro n G inst C girth least topForm
  let target := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C, u ∈ side C a b ∧
      OrReaches n C (opnd C a (1-b)) g ∧ gateVal n C g (pairInput u v) = true)
  let singletons := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ a ∈ tops G C, wireVal n C (opnd C a 0) (pairInput u u) = true ∧
      wireVal n C (opnd C a 1) (pairInput v v) = true)
  let pairs := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧
      gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false)
  change target.card ≤ (s + p) * (C.size + 1)
  have cover : target ⊆ singletons ∪ pairs := by
    intro e he
    obtain ⟨heU, u, v, rfl, a, ha, b, g, hg, hu, reach, active⟩ := Finset.mem_filter.mp he
    have guarded : u ∈ wmax G C g := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x gx xu
      exact (graphFun_empty_true x).2 (top_wmax least.1 ha hu reach x xu gx)
    have huOn : pairInput u u u = true := by
      change decide (u = u ∨ u = u) = true
      simp
    have guOff : gateVal n C g (pairInput u u) = false := by
      apply Bool.eq_false_iff.mpr
      intro gu
      obtain ⟨i, j, hij, hi, hj⟩ := top_wmax least.1 ha hu reach (pairInput u u) huOn gu
      change decide (i = u ∨ i = u) = true at hi
      change decide (j = u ∨ j = u) = true at hj
      simp only [decide_eq_true_eq, or_self] at hi hj
      exact G.irrefl (hi ▸ hj ▸ hij)
    cases gv : gateVal n C g (pairInput v v) with
    | false =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨heU, u, v, rfl, g, hg, guarded, active, guOff, gv⟩)
    | true =>
      have leftOn := orIn_sound least.1 (opnd C a b) u (pairInput u u) hu huOn
      have rightOn := orReaches_gateVal least.1 (opnd C a (1-b)) g (pairInput v v) reach gv
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨heU, ?_⟩
      fin_cases b
      · exact ⟨u, v, rfl, a, ha, leftOn, rightOn⟩
      · exact ⟨v, u, Sym2.eq_swap, a, ha, rightOn, leftOn⟩
  calc
    target.card ≤ (singletons ∪ pairs).card := Finset.card_le_card cover
    _ ≤ singletons.card + pairs.card := Finset.card_union_le _ _
    _ ≤ s * (C.size + 1) + p * (C.size + 1) :=
      Nat.add_le_add (singleBound n G C girth least topForm) (pairBound n G C girth least topForm)
    _ = (s + p) * (C.size + 1) := (Nat.add_mul _ _ _).symm
