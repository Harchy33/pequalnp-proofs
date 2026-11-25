import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_1683_831
    (geometry : let offsets : Finset (Fin 13) := {0,1,3,9}
      let R : Fin 13 → Fin 13 → Prop := fun p w => ∃ d ∈ offsets, p = w+d
      (∀ w, ∃ S : Finset (Fin 13), S.card ≤ 4 ∧ ∀ p, R p w → p ∈ S) ∧
       (∀ u w, ∃ p, R p u ∧ R p w) ∧
       (∀ p, ∃ S : Finset (Fin 13), S.card ≤ 4 ∧ ∀ w, R p w → w ∈ S) ∧
       (∀ u p, ∃ w, R u w ∧ R p w))
    (search : let offsets : Finset (Fin 13) := {0,1,3,9}
      let R : Fin 13 → Fin 13 → Prop := fun p w => ∃ d ∈ offsets, p = w+d
      let bits := fun (P L : Finset (Fin 13)) (k : Fin 26) =>
        decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ (∃ w ∈ L, k = Fin.natAdd 13 w))
      let missP := fun (P : Finset (Fin 13)) => Finset.univ.filter fun w => ∀ p ∈ P, ¬ R p w
      let missL := fun (L : Finset (Fin 13)) => Finset.univ.filter fun p => ∀ w ∈ L, ¬ R p w
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
       (∀ p w, R p w → circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
       (∀ w (S : Finset (Fin 13)), (∀ p ∈ S, R p w) → S.card ≤ 3 →
         circuitFun 26 C (bits S (missP S)) = false) ∧
       (∀ p (T : Finset (Fin 13)), (∀ w ∈ T, R p w) → T.card ≤ 3 →
         circuitFun 26 C (bits (missL T) T) = false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  classical
  let offsets : Finset (Fin 13) := {0,1,3,9}
  let R : Fin 13 → Fin 13 → Prop := fun p w => ∃ d ∈ offsets, p = w+d
  let bits := fun (P L : Finset (Fin 13)) (k : Fin 26) =>
    decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ (∃ w ∈ L, k = Fin.natAdd 13 w))
  let missP := fun (P : Finset (Fin 13)) => Finset.univ.filter fun w => ∀ p ∈ P, ¬ R p w
  let missL := fun (L : Finset (Fin 13)) => Finset.univ.filter fun p => ∀ w ∈ L, ¬ R p w
  change (∀ w, ∃ S : Finset (Fin 13), S.card ≤ 4 ∧ ∀ p, R p w → p ∈ S) ∧
   (∀ u w, ∃ p, R p u ∧ R p w) ∧
   (∀ p, ∃ S : Finset (Fin 13), S.card ≤ 4 ∧ ∀ w, R p w → w ∈ S) ∧
   (∀ u p, ∃ w, R u w ∧ R p w) at geometry
  change ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
   (∀ p w, R p w → circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
   (∀ w (S : Finset (Fin 13)), (∀ p ∈ S, R p w) → S.card ≤ 3 →
     circuitFun 26 C (bits S (missP S)) = false) ∧
   (∀ p (T : Finset (Fin 13)), (∀ w ∈ T, R p w) → T.card ≤ 3 →
     circuitFun 26 C (bits (missL T) T) = false) at search
  rcases geometry with ⟨lineCover, meetLines, pointCover, meetPoints⟩
  have lineCard : ∀ w, (Finset.univ.filter fun p => R p w).card ≤ 4 := by
    intro w
    obtain ⟨S, bound, cover⟩ := lineCover w
    apply le_trans (Finset.card_le_card ?_) bound
    intro p hp
    exact cover p (Finset.mem_filter.mp hp).2
  have pointCard : ∀ p, (Finset.univ.filter fun w => R p w).card ≤ 4 := by
    intro p
    obtain ⟨S, bound, cover⟩ := pointCover p
    apply le_trans (Finset.card_le_card ?_) bound
    intro w hw
    exact cover w (Finset.mem_filter.mp hw).2
  rcases search with ⟨C, mono, size, positive, primal, dual⟩
  refine ⟨C, mono, size, positive, ?_⟩
  intro P maximal degenerate
  change (∀ v : Fin 13, v ∉ P → ∃ w, (∀ p ∈ P, ¬ R p w) ∧ R v w) at maximal
  change ((∃ w : Fin 13, ∀ p ∈ P, R p w) ∨
    (∃ v : Fin 13, ∀ w : Fin 13, (∀ p ∈ P, ¬ R p w) → R v w)) at degenerate
  let Q := missP P
  have back : P = missL Q := by
    ext p
    simp only [missL, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp w hw
      exact (Finset.mem_filter.mp hw).2 p hp
    · intro avoid
      by_contra absent
      obtain ⟨w, hw, incident⟩ := maximal p absent
      exact avoid w (by simpa only [Q, missP, Finset.mem_filter, Finset.mem_univ, true_and] using hw) incident
  have input : bits P Q = (fun k : Fin 26 => decide
      ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
       (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ R p w))) := by
    funext k
    simp [bits, Q, missP, and_comm, and_left_comm, and_assoc]
  change circuitFun 26 C (fun k : Fin 26 => decide
      ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
       (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ R p w))) = false
  rw [← input]
  rcases degenerate with ⟨u, sameLine⟩ | ⟨v, samePoint⟩
  · by_cases small : P.card ≤ 3
    · exact primal u P sameLine small
    · let line := Finset.univ.filter fun p => R p u
      have subset : P ⊆ line := by
        intro p hp
        simpa [line] using sameLine p hp
      have equal : P = line := Finset.eq_of_subset_of_card_le subset (by
        have bound := lineCard u
        change line.card ≤ 4 at bound
        omega)
      have empty : Q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        obtain ⟨p, onU, onW⟩ := meetLines u w
        have hp : p ∈ P := by rw [equal]; simp [line, onU]
        exact (Finset.mem_filter.mp hw).2 p hp onW
      have result := dual 0 Q (by simp [empty]) (by simp [empty])
      simpa only [← back] using result
  · have concurrent : ∀ w ∈ Q, R v w := by
      intro w hw
      exact samePoint w (Finset.mem_filter.mp hw).2
    by_cases small : Q.card ≤ 3
    · have result := dual v Q concurrent small
      simpa only [← back] using result
    · let pencil := Finset.univ.filter fun w => R v w
      have subset : Q ⊆ pencil := by
        intro w hw
        simpa [pencil] using concurrent w hw
      have equal : Q = pencil := Finset.eq_of_subset_of_card_le subset (by
        have bound := pointCard v
        change pencil.card ≤ 4 at bound
        omega)
      have empty : P = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨w, onV, onP⟩ := meetPoints v p
        have hw : w ∈ Q := by rw [equal]; simp [pencil, onV]
        exact (Finset.mem_filter.mp hw).2 p hp onP
      exact primal 0 P (by simp [empty]) (by simp [empty])
