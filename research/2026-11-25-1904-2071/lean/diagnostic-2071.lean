import PEqualNP.Defs

namespace Diagnostic2071
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
attribute [local instance] NestedCover.gateOpDecEq

def base : Circuit := ⟨[
  ⟨GateOp.or,[13,17]⟩,
  ⟨GateOp.or,[23,25]⟩,
  ⟨GateOp.or,[26,27]⟩,
  ⟨GateOp.and,[0,28]⟩,
  ⟨GateOp.or,[13,14]⟩,
  ⟨GateOp.or,[18,24]⟩,
  ⟨GateOp.or,[30,31]⟩,
  ⟨GateOp.and,[1,32]⟩,
  ⟨GateOp.or,[14,15]⟩,
  ⟨GateOp.or,[19,25]⟩,
  ⟨GateOp.or,[34,35]⟩,
  ⟨GateOp.and,[2,36]⟩,
  ⟨GateOp.or,[13,15]⟩,
  ⟨GateOp.or,[16,20]⟩,
  ⟨GateOp.or,[38,39]⟩,
  ⟨GateOp.and,[3,40]⟩,
  ⟨GateOp.or,[14,16]⟩,
  ⟨GateOp.or,[17,21]⟩,
  ⟨GateOp.or,[42,43]⟩,
  ⟨GateOp.and,[4,44]⟩,
  ⟨GateOp.or,[15,17]⟩,
  ⟨GateOp.or,[18,22]⟩,
  ⟨GateOp.or,[46,47]⟩,
  ⟨GateOp.and,[5,48]⟩,
  ⟨GateOp.or,[16,18]⟩,
  ⟨GateOp.or,[19,23]⟩,
  ⟨GateOp.or,[50,51]⟩,
  ⟨GateOp.and,[6,52]⟩,
  ⟨GateOp.or,[17,19]⟩,
  ⟨GateOp.or,[20,24]⟩,
  ⟨GateOp.or,[54,55]⟩,
  ⟨GateOp.and,[7,56]⟩,
  ⟨GateOp.or,[18,20]⟩,
  ⟨GateOp.or,[21,25]⟩,
  ⟨GateOp.or,[58,59]⟩,
  ⟨GateOp.and,[8,60]⟩,
  ⟨GateOp.or,[13,19]⟩,
  ⟨GateOp.or,[21,22]⟩,
  ⟨GateOp.or,[62,63]⟩,
  ⟨GateOp.and,[9,64]⟩,
  ⟨GateOp.or,[14,20]⟩,
  ⟨GateOp.or,[22,23]⟩,
  ⟨GateOp.or,[66,67]⟩,
  ⟨GateOp.and,[10,68]⟩,
  ⟨GateOp.or,[15,21]⟩,
  ⟨GateOp.or,[23,24]⟩,
  ⟨GateOp.or,[70,71]⟩,
  ⟨GateOp.and,[11,72]⟩,
  ⟨GateOp.or,[16,22]⟩,
  ⟨GateOp.or,[24,25]⟩,
  ⟨GateOp.or,[74,75]⟩,
  ⟨GateOp.and,[12,76]⟩,
  ⟨GateOp.or,[29,33]⟩,
  ⟨GateOp.or,[78,37]⟩,
  ⟨GateOp.or,[79,41]⟩,
  ⟨GateOp.or,[80,45]⟩,
  ⟨GateOp.or,[81,49]⟩,
  ⟨GateOp.or,[82,53]⟩,
  ⟨GateOp.or,[83,57]⟩,
  ⟨GateOp.or,[84,61]⟩,
  ⟨GateOp.or,[85,65]⟩,
  ⟨GateOp.or,[86,69]⟩,
  ⟨GateOp.or,[87,73]⟩,
  ⟨GateOp.or,[88,77]⟩],89⟩
def repeated : Circuit := ⟨[
  ⟨GateOp.or,[13,17]⟩,
  ⟨GateOp.or,[23,25]⟩,
  ⟨GateOp.or,[26,27]⟩,
  ⟨GateOp.and,[0,28]⟩,
  ⟨GateOp.and,[0,29]⟩,
  ⟨GateOp.and,[28,30]⟩,
  ⟨GateOp.or,[13,14]⟩,
  ⟨GateOp.or,[18,24]⟩,
  ⟨GateOp.or,[32,33]⟩,
  ⟨GateOp.and,[1,34]⟩,
  ⟨GateOp.or,[14,15]⟩,
  ⟨GateOp.or,[19,25]⟩,
  ⟨GateOp.or,[36,37]⟩,
  ⟨GateOp.and,[2,38]⟩,
  ⟨GateOp.or,[13,15]⟩,
  ⟨GateOp.or,[16,20]⟩,
  ⟨GateOp.or,[40,41]⟩,
  ⟨GateOp.and,[3,42]⟩,
  ⟨GateOp.or,[14,16]⟩,
  ⟨GateOp.or,[17,21]⟩,
  ⟨GateOp.or,[44,45]⟩,
  ⟨GateOp.and,[4,46]⟩,
  ⟨GateOp.or,[15,17]⟩,
  ⟨GateOp.or,[18,22]⟩,
  ⟨GateOp.or,[48,49]⟩,
  ⟨GateOp.and,[5,50]⟩,
  ⟨GateOp.or,[16,18]⟩,
  ⟨GateOp.or,[19,23]⟩,
  ⟨GateOp.or,[52,53]⟩,
  ⟨GateOp.and,[6,54]⟩,
  ⟨GateOp.or,[17,19]⟩,
  ⟨GateOp.or,[20,24]⟩,
  ⟨GateOp.or,[56,57]⟩,
  ⟨GateOp.and,[7,58]⟩,
  ⟨GateOp.or,[18,20]⟩,
  ⟨GateOp.or,[21,25]⟩,
  ⟨GateOp.or,[60,61]⟩,
  ⟨GateOp.and,[8,62]⟩,
  ⟨GateOp.or,[13,19]⟩,
  ⟨GateOp.or,[21,22]⟩,
  ⟨GateOp.or,[64,65]⟩,
  ⟨GateOp.and,[9,66]⟩,
  ⟨GateOp.or,[14,20]⟩,
  ⟨GateOp.or,[22,23]⟩,
  ⟨GateOp.or,[68,69]⟩,
  ⟨GateOp.and,[10,70]⟩,
  ⟨GateOp.or,[15,21]⟩,
  ⟨GateOp.or,[23,24]⟩,
  ⟨GateOp.or,[72,73]⟩,
  ⟨GateOp.and,[11,74]⟩,
  ⟨GateOp.or,[16,22]⟩,
  ⟨GateOp.or,[24,25]⟩,
  ⟨GateOp.or,[76,77]⟩,
  ⟨GateOp.and,[12,78]⟩,
  ⟨GateOp.or,[31,35]⟩,
  ⟨GateOp.or,[80,39]⟩,
  ⟨GateOp.or,[81,43]⟩,
  ⟨GateOp.or,[82,47]⟩,
  ⟨GateOp.or,[83,51]⟩,
  ⟨GateOp.or,[84,55]⟩,
  ⟨GateOp.or,[85,59]⟩,
  ⟨GateOp.or,[86,63]⟩,
  ⟨GateOp.or,[87,67]⟩,
  ⟨GateOp.or,[88,71]⟩,
  ⟨GateOp.or,[89,75]⟩,
  ⟨GateOp.or,[90,79]⟩,
  ⟨GateOp.and,[0,1]⟩],91⟩
def shifts : Finset (Fin 13) := {0,1,3,9}
def traceAValues : List Bool := [false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,true,true,false,true,false,true,false,false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def traceBValues : List Bool := [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def traceA (w : ℕ) : Bool := traceAValues.getD w false
def traceB (w : ℕ) : Bool := traceBValues.getD w false

theorem local_gadget_identity (p l : Bool) : (l && (p && (p && l))) = (p && l) := by
  cases p <;> cases l <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem legal : PEqualNP.TopForm.IsAO2 26 base ∧ base.size = 64 ∧
    PEqualNP.TopForm.IsAO2 26 repeated ∧ repeated.size = 67 ∧
    (∀ g ∈ repeated.gates, g.inputs.Nodup) ∧
    0 < PEqualNP.TopForm.andPairs 26 repeated := by
  refine ⟨?_,rfl,?_,rfl,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · simp [repeated]
  · unfold PEqualNP.TopForm.andPairs
    apply Finset.card_pos.mpr
    refine ⟨(3,4),?_⟩
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    exact ⟨⟨by decide,by decide⟩,by rfl,by rfl,by decide +kernel⟩

#print axioms legal

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem dirty_and : ∃ j < repeated.gates.length,
    (NestedCover.gateAt repeated j).op = GateOp.and ∧
    ∃ z : Fin 26 → Bool, (repeated.wires (List.ofFn z)).getD (26+j) false = true ∧
      repeated.eval (List.ofFn z) = false := by
  refine ⟨66,by decide,by rfl,(fun i => decide (i=0 ∨ i=1)),?_⟩
  decide +kernel

#print axioms dirty_and

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem traces_checked :
    (∀ i : Fin 26, traceA i.val = decide (i.val = 13) ∧ traceB i.val = decide (i.val = 0)) ∧
    (∀ j : Fin 67,
      let g := NestedCover.gateAt repeated j.val
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      let wp := repeated.wires (List.ofFn fun i : Fin 26 => decide (i=0))
      let wl := repeated.wires (List.ofFn fun i : Fin 26 => decide (i=13))
      (g.op = GateOp.and →
        traceA (26+j.val) = (wp.getD a false && traceA b || traceA a && wp.getD b false) ∧
        traceB (26+j.val) = (wl.getD a false && traceB b || traceB a && wl.getD b false)) ∧
      (g.op = GateOp.or →
        traceA (26+j.val) = (traceA a || traceA b) ∧ traceB (26+j.val) = (traceB a || traceB b))) ∧
    traceA repeated.output = false ∧ traceB repeated.output = false := by
  decide +kernel

end Diagnostic2071
#print axioms Diagnostic2071.legal
#print axioms Diagnostic2071.local_gadget_identity
#print axioms Diagnostic2071.dirty_and
#print axioms Diagnostic2071.traces_checked
