import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50446

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩,
    ⟨GateOp.or, [2, 7]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.or, [4, 10]⟩], 0⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

lemma okOp_mem (o : GateOp) (h : okOp o = true) :
    o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases o <;> simp_all [okOp]

lemma all_ok : ∀ g ∈ circ.gates, okOp g.op = true ∧ g.inputs.length ≤ 2 := by
  decide

lemma fan : FanInTwo circ := fun g hg =>
  ⟨okOp_mem _ (all_ok g hg).1, (all_ok g hg).2⟩

lemma size_le : circ.size ≤ 6 := by decide

lemma readback : PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 circ := by
  decide

lemma notcount : PEqualNP.NotBracket.notCount circ ≤ 2 := by decide

end PEqualNP.Outside.L_meta_50446

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_50446 :
    ¬ (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (36 : Nat).testBit t.val ∧
        w.getD q.val false = (52 : Nat).testBit t.val ∧
        w.getD r.val false = (58 : Nat).testBit t.val)) := by
  intro h
  refine h ⟨PEqualNP.Outside.L_meta_50446.circ,
    ⟨12, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ?_⟩
  exact ⟨PEqualNP.Outside.L_meta_50446.fan,
    PEqualNP.Outside.L_meta_50446.readback,
    PEqualNP.Outside.L_meta_50446.notcount,
    PEqualNP.Outside.L_meta_50446.size_le,
    by decide⟩
