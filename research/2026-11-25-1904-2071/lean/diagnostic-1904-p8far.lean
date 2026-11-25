import PEqualNP.Defs

namespace Diagnostic1904
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] NestedCover.gateOpDecEq

def edges : List (ℕ × ℕ) := [(1,2),(0,4),(1,6),(2,7),(3,5),(5,7),(7,4),(4,6),(6,3)]
def graph : SimpleGraph (Fin 8) where
  Adj := fun a b => (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by intro a; fin_cases a <;> decide +kernel⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def witness : Circuit := ⟨[
  ⟨GateOp.or,[1,7]⟩,
  ⟨GateOp.and,[2,8]⟩,
  ⟨GateOp.or,[0,7]⟩,
  ⟨GateOp.or,[6,10]⟩,
  ⟨GateOp.and,[4,11]⟩,
  ⟨GateOp.or,[3,7]⟩,
  ⟨GateOp.and,[5,13]⟩,
  ⟨GateOp.or,[1,3]⟩,
  ⟨GateOp.and,[6,15]⟩,
  ⟨GateOp.or,[9,12]⟩,
  ⟨GateOp.or,[14,17]⟩,
  ⟨GateOp.or,[16,18]⟩],19⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem no_short_cycles :
    (∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a) ∧
    (∀ a b c d : Fin 8, graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a → a=c ∨ b=d) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem exact_clean_upper : Monotone2 witness ∧ witness.size = 12 ∧
    (∀ z : Fin 8 → Bool, witness.eval (List.ofFn z) = decide
      (∃ a b : Fin 8, graph.Adj a b ∧ z a = true ∧ z b = true)) ∧
    (∀ j : Fin 12, (NestedCover.gateAt witness j.val).op = GateOp.and →
      ∀ z : Fin 8 → Bool, (witness.wires (List.ofFn z)).getD (8+j.val) false = true →
        ∃ a b : Fin 8, graph.Adj a b ∧ z a = true ∧ z b = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Monotone2, witness]
  · rfl
  · decide +kernel
  · decide +kernel

end Diagnostic1904
#print axioms Diagnostic1904.no_short_cycles
#print axioms Diagnostic1904.exact_clean_upper
