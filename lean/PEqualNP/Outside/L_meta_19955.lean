import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19955 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
      ⟨.or, [8, 9]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 14]⟩,
      ⟨.or, [10, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [12, 15]⟩,
      ⟨.or, [13, 14]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [21, 24]⟩,
      ⟨.or, [16, 21]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [17, 20]⟩,
      ⟨.or, [18, 22]⟩, ⟨.and, [0, 25]⟩, ⟨.and, [1, 26]⟩, ⟨.and, [2, 27]⟩,
      ⟨.and, [3, 28]⟩, ⟨.and, [4, 29]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 31]⟩,
      ⟨.and, [7, 32]⟩, ⟨.or, [33, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩,
      ⟨.or, [39, 40]⟩, ⟨.or, [41, 42]⟩, ⟨.or, [43, 44]⟩, ⟨.or, [45, 46]⟩], 47⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  let ok (g : PEqualNP.CircuitLowerBounds.Gate) :=
    (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)
  have allOk : C.gates.all ok = true := by decide
  intro g hg
  have h := List.all_eq_true.mp allOk g hg
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  cases e : g.op <;> simp [e] at h ⊢
