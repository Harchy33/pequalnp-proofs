import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3314_refutation_aux

open PEqualNP.CircuitLowerBounds

def wires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = wires gs x ++
      [g.op.eval (g.inputs.map fun i => (wires gs x).getD i false)] := by
  simp [wires, List.foldl_append]

lemma wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [wires_snoc]; simp [ih]; omega

lemma getD_snoc (l : List Bool) (a : Bool) (t : ℕ) :
    (l ++ [a]).getD t false =
      if t < l.length then l.getD t false else if t = l.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

lemma eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

lemma wires_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wires gs x).getD i false = true → (wires gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [wires] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (wires gs x).length = (wires gs y).length := by simp [wires_length, hl]
    rw [wires_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (wires gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (wires gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht

lemma wire_top (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin 14 → Bool) (i : ℕ)
    (h : (C.wires (List.ofFn x)).getD i false = true) :
    (C.wires (List.ofFn (fun _ : Fin 14 => true))).getD i false = true := by
  exact wires_mono C.gates (fun g hg => (hC g hg).1)
    (List.ofFn x) (List.ofFn (fun _ : Fin 14 => true)) (by simp)
    (by
      intro j hj
      by_cases hjlt : j < 14
      · change (List.replicate 14 true).getD j false = true
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hjlt,
          Option.getD_some]
      · simp [List.getD_eq_getElem?_getD, hjlt] at hj)
    i h

end PEqualNP.Outside.L_meta_3314_refutation_aux

theorem PEqualNP.Outside.L_meta_3314_refutation : ¬ (∀ (x1 : (Fin (14 : ℕ) → Bool) → Prop),   ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),     PEqualNP.MetaComplexity.Monotone2 x2 ∧       x2.size ≤ (25 : ℕ) ∧         (14 : ℕ) ≤ x4 ∧           x4 < x5 ∧             x5 < (14 : ℕ) + x2.size ∧               (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))]) ∧                 have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;                 have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;                 have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;                 have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];                 x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false) := by
  intro h
  obtain ⟨C, op, a, b, masks, hC, _, _, _, _, ⟨hop, _⟩, hrest⟩ :=
    h (fun _ => False)
  dsimp only at hrest
  obtain ⟨hne, _, _, _, hnegative⟩ := hrest
  have hmax : Maximal (fun _ : Fin 14 → Bool => ¬ False) (fun _ => true) := by
    refine ⟨by trivial, ?_⟩
    intro y _ _
    exact le_top
  have hneg := hnegative (fun _ => true) hmax
  rcases hneg with hbad | hneg
  · have := hbad.1
    rw [hop] at this
    cases this
  · rw [hop] at hneg
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_false_iff] at hneg
    have ha : (C.wires (List.ofFn (fun i : Fin 14 => masks.1.testBit i.val))).getD a false = false := by
      cases hv : (C.wires (List.ofFn (fun i : Fin 14 => masks.1.testBit i.val))).getD a false with
      | false => rfl
      | true =>
        have ht := PEqualNP.Outside.L_meta_3314_refutation_aux.wire_top C hC _ a hv
        exact Bool.noConfusion (ht.symm.trans hneg.1)
    have hb : (C.wires (List.ofFn (fun i : Fin 14 => masks.1.testBit i.val))).getD b false = false := by
      cases hv : (C.wires (List.ofFn (fun i : Fin 14 => masks.1.testBit i.val))).getD b false with
      | false => rfl
      | true =>
        have ht := PEqualNP.Outside.L_meta_3314_refutation_aux.wire_top C hC _ b hv
        exact Bool.noConfusion (ht.symm.trans hneg.2)
    exact hne (ha.trans hb.symm)
