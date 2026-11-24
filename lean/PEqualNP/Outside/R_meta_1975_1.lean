import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_1975_1
    (removeAliases : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (S : Finset ℕ),
      FanInTwo C → S ⊆ Finset.range C.size →
      (∀ j ∈ S, ∃ w < n + j, ∀ x : Fin n → Bool, x v = false →
        (C.wires (List.ofFn x)).getD (n + j) false =
          (C.wires (List.ofFn x)).getD w false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + S.card ≤ C.size ∧
        circuitFun n D = fun x => circuitFun n C (Function.update x v false))
    (findAliases : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = graphFun G A →
      (∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s) →
      (∀ v ∉ A,
        let readers := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        readers.length = 3 ∧ ∀ g ∈ readers, g.op = GateOp.or) →
      ∃ v ∉ A, ∃ S : Finset ℕ, S ⊆ Finset.range C.size ∧ 4 ≤ S.card ∧
        ∀ j ∈ S, ∃ w < n + j, ∀ x : Fin n → Bool, x v = false →
          (C.wires (List.ofFn x)).getD (n + j) false =
            (C.wires (List.ofFn x)).getD w false) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length = (3 : ℕ) ∧ ∀ x17 ∈ x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G A f C hdeg hgirth hisolated hedge hformula hfan heval hmin hread
  have hfeq : f = graphFun G A := by
    funext x
    have he : f x = true ↔ graphFun G A x = true := by
      simpa only [graphFun, Bool.or_eq_true, decide_eq_true_eq] using hformula x
    have boolExt : ∀ a b : Bool, (a = true ↔ b = true) → a = b := by decide
    exact boolExt _ _ he
  have hmin' : ∀ s, HasCircuitSize n (graphFun G A) s → C.size ≤ s := by
    intro s hs
    apply hmin s
    simpa only [hfeq] using hs
  obtain ⟨v, hv, S, hS, hcard, halias⟩ := findAliases n G A C hdeg hgirth
    hisolated hedge hfan (heval.trans hfeq) hmin' hread
  obtain ⟨D, hDfan, hsize, hD⟩ := removeAliases n C v S hfan hS halias
  refine ⟨v, hv, D.size, by omega, D, hDfan, le_rfl, ?_⟩
  intro x
  change circuitFun n D x = f (Function.update x v false)
  rw [hD, heval]
