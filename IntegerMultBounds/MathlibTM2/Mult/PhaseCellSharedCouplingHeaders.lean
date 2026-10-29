module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCounters

/-! Coupling reads retained master headers through a static register view.
The released native cell workspace supplies its private arithmetic tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def sharedCouplingReg (i : Fin 168) : Fin 168 :=
  if i = 114 then 117 else
  if i = 117 then 114 else
  if i = 112 then 119 else
  if i = 119 then 112 else
  if i = 97 then 121 else
  if i = 121 then 97 else
  if i = 98 then 122 else
  if i = 122 then 98 else
  if i = 99 then 123 else
  if i = 123 then 99 else
  if i = 100 then 124 else
  if i = 124 then 100 else
  if i = 101 then 141 else
  if i = 141 then 101 else
  if i = 103 then 142 else
  if i = 142 then 103 else
  if i = 94 then 130 else
  if i = 130 then 94 else i

theorem sharedCouplingReg_involutive : Function.Involutive sharedCouplingReg := by
  intro i
  by_cases hi : i ∈ [(114 : Fin 168),117,112,119,97,121,98,122,99,123,100,124,101,141,103,142,94,130]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have he : sharedCouplingReg i = i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
      simp_all [sharedCouplingReg]
    rw [he,he]

theorem sharedCouplingReg_injective : Function.Injective sharedCouplingReg :=
  sharedCouplingReg_involutive.injective

@[simp] theorem sharedCouplingReg_rhs : sharedCouplingReg 93 = 93 := by
  unfold sharedCouplingReg
  decide

@[simp] theorem sharedCouplingReg_source : sharedCouplingReg 110 = 110 := by
  unfold sharedCouplingReg
  decide

def sharedCouplingCoreReg (i : Fin 117) : Fin 168 := sharedCouplingReg (packedCellCoreReg i)

theorem sharedCouplingCoreReg_injective : Function.Injective sharedCouplingCoreReg :=
  sharedCouplingReg_injective.comp packedCellCoreReg_injective

theorem sharedCouplingReg_work (k : Fin 168) (hk : k.val < 97) (h94 : k ≠ 94) :
    sharedCouplingReg k = k := by
  have hnot : k ∉ [(114 : Fin 168),117,112,119,97,121,98,122,99,123,100,124,101,141,103,142,94,130] := by
    intro hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact h94 rfl | norm_num at hk
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot
  simp_all [sharedCouplingReg,Equiv.swap_apply_def]

theorem sharedCouplingReg_high (k : Fin 168) (hk : 143 ≤ k.val) : sharedCouplingReg k = k := by
  have hnot : k ∉ [(114 : Fin 168),117,112,119,97,121,98,122,99,123,100,124,101,141,103,142,94,130] := by
    intro hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hk
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot
  simp_all [sharedCouplingReg,Equiv.swap_apply_def]

theorem sharedCouplingHeaders_ready {A P q w s t u band a b : ℕ}
    (S : Stacks 168 A) (rhs borrowed result : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hbank : embStk packedCellCoreReg S = releasedCellBank rhs borrowed result inp out)
    (hP : (S.R 117).length = P) (hq : (S.R 119).length = q)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t)
    (hu : (S.R 123).length = u) (hband : (S.R 124).length = band)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (hw : (S.R 130).length = w)
    (hleft : ∀ k ∈ [(121 : Fin 168),122,123,124], S.L k = []) :
    CouplingReady P q w s t u band a b (rhs++borrowed) (embStk sharedCouplingCoreReg S) := by
  have hR (k : Fin 117) := congrArg (fun B : Stacks 117 A => B.R k) hbank
  have hL (k : Fin 117) : S.L (packedCellCoreReg k) = [] :=
    congrArg (fun B : Stacks 117 A => B.L k) hbank
  have hblank (k : Fin 117) (h93 : k.val ≠ 93) (h110 : k.val ≠ 110) :
      S.R (packedCellCoreReg k) = [] := by
    simpa [embStk,releasedCellBank,h93,h110] using hR k
  have hwork (k : Fin 117) (hk : k.val < 97) (h94 : k.val ≠ 94) :
      sharedCouplingCoreReg k = packedCellCoreReg k :=
    sharedCouplingReg_work _ hk (by
      intro he
      apply h94
      exact congrArg (fun j : Fin 168 => j.val) he)
  constructor
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hP
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hq
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hu
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hs
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using ht
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hband
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using ha
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hb
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hw
  · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def,releasedCellBank] using hR 110
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 92 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 96 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 102 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 104 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 105 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 106 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 108 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 109 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 115 (by decide) (by decide)
    | simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hblank 116 (by decide) (by decide)
  · intro i
    have hi : (mul i).val < 97 := by dsimp [mul]; omega
    have hn : (mul i).val ≠ 94 := by dsimp [mul]; omega
    change S.L (sharedCouplingCoreReg (mul i)) = [] ∧ S.R (sharedCouplingCoreReg (mul i)) = []
    rw [hwork (mul i) hi hn]
    exact ⟨hL _,hblank _ (by dsimp [mul]; omega) (by dsimp [mul]; omega)⟩
  · intro r
    have hr := cr_range r
    change S.R (sharedCouplingCoreReg (cr r)) = []
    rw [hwork (cr r) (by omega) hr.2.2.2]
    exact hblank _ hr.2.2.1 (by omega)
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hleft 121 (by simp)
    · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hleft 122 (by simp)
    · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hleft 123 (by simp)
    · simpa [embStk,sharedCouplingCoreReg,packedCellCoreReg,sharedCouplingReg,Equiv.swap_apply_def] using hleft 124 (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
