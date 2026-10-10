import IntegerMultBounds.Machine.RadixControlCleanupList
import IntegerMultBounds.Machine.RadixComplexReadBank

/-! Erase a complete copied marked radix-control bank while preserving an
arbitrary appended frame. No digit count enters the fixed finite program. -/
namespace IntegerMultBounds.Machine.RadixControlCleanupBank
noncomputable section
open RadixLinearCombinationRefresh (controls)
variable {c u q : ℕ}

def slots (c u : ℕ) : List (Fin (c+u)) := List.ofFn (Fin.castAdd u : Fin c → Fin (c+u))

theorem slots_nodup : (slots c u).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  have hv := congrArg (fun k : Fin (c+u) => k.val) h
  exact Fin.ext hv

def program (hc : 0<c) := RadixControlCleanupList.program (q:=q) (by omega : 0<c+u) (slots c u)

def words (xs : ℕ → List (Fin q)) : Fin (c+u) → List (Fin q) :=
  Fin.addCases (fun i => xs i.val) (fun _ => [])

private theorem cleared_eq (xs : ℕ → List (Fin q)) (tail : Tapes u q) :
    BinaryDescriptorCleanupList.cleared (slots c u) ((controls xs).append tail)=
      (RadixLinearCombinationBootstrap.empty c).append tail := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases with
    | left i =>
      have h := BinaryDescriptorCleanupList.cleared_slot (slots c u) slots_nodup
        ((controls xs).append tail) (Fin.castAdd u i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
      first
        | simpa only [Tapes.append,Fin.addCases_left,RadixLinearCombinationBootstrap.empty] using h.1
        | simpa only [Tapes.append,Fin.addCases_left,RadixLinearCombinationBootstrap.empty] using h.2
    | right i =>
      have h := BinaryDescriptorCleanupList.cleared_frame (slots c u)
        ((controls xs).append tail) (Fin.natAdd c i) (by
          intro hm
          obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
          have hv := congrArg Fin.val hj
          have := j.isLt
          dsimp at hv
          omega)
      first
        | simpa only [Tapes.append,Fin.addCases_right] using h.1
        | simpa only [Tapes.append,Fin.addCases_right] using h.2

theorem runs (hc : 0<c) (xs : ℕ → List (Fin q)) (w : ℕ)
    (hw : ∀ j,(xs j).length=w) (tail : Tapes u q) :
    HoareTime (program (q:=q) (u:=u) hc) (fun v => v=(controls xs).append tail)
      (fun v => v=(RadixLinearCombinationBootstrap.empty c).append tail) (c*(2*w+5)) := by
  have h := RadixControlCleanupList.runs (by omega : 0<c+u) (slots c u) slots_nodup
    (words xs) ((controls xs).append tail) (by
      intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      simp [Tapes.append,controls,words])
  have hcost := RadixControlCleanupList.cost_uniform (slots c u) (words xs) w (by
    intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    simpa only [words,Fin.addCases_left] using hw j.val)
  simp only [slots,List.length_ofFn] at hcost
  exact h.consequence (fun _ h => h) (fun _ h => h.trans (cleared_eq xs tail)) hcost.le

end
end IntegerMultBounds.Machine.RadixControlCleanupBank
