module

public import IntegerMultBounds.MathlibTM2.Host.RightWrites
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicResidualBoundary

/-! The net effect of boundary solving, publication and RHS restoration is a
short list of writes. The native scalar core is restored apart from its inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast ScalarPlacement

def periodicRecoveryInputBank {A : ℕ} (S : Stacks 242 A)
    (rhs queue field : List (Fin (A+4))) : Stacks 248 A :=
  writeRight [(143,[]),(132,field),(110,queue),(93,rhs++S.R 93),(116,[]),(167,[]),(231,[])]
    (extendStacks (by decide) S)

/-- Cancel the consumed solution and fresh recovery buffers in the final bank. -/
theorem periodicRecoveryInputBank_eq {A : ℕ} (S : Stacks 242 A) (N : ℕ)
    (solution boundary field rhs queue : List (Fin (A+4))) :
    let G := {S with R := (Function.update (Function.update S.R 143 []) 238 (solution++S.R 238))}
    let H := extendStacks (by decide : 242 ≤ 248) G
    let U := {H with R := (Function.update (Function.update (Function.update H.R 238 (S.R 238)) 231 []) 245 boundary)}
    let Z := {U with R := (Function.update (Function.update (Function.update U.R 246
      (List.replicate N Node.tick)) 245 []) 132 field)}
    {Z with R := (Function.update (Function.update (Function.update (Function.update (Function.update Z.R
      110 queue) 93 (rhs++Z.R 93)) 116 []) 167 []) 246 [])} = periodicRecoveryInputBank S rhs queue field := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k ∈ ([93,110,116,132,143,167,231,238,245,246] : List (Fin 248))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [periodicRecoveryInputBank,writeRight,extendStacks]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff] at hk
    norm_num at hk
    rcases hk with ⟨h93,h110,h116,h132,h143,h167,h231,h238,h245,h246⟩
    by_cases hlow : k.val < 242
    all_goals simp [periodicRecoveryInputBank,writeRight,extendStacks,Function.update_apply,Fin.ext_iff,
      hlow,h93,h110,h116,h132,h143,h167,h231,h238,h245,h246]

theorem periodicRecoveryInputBank_ready {A s precision q w t u band a b : ℕ} [NeZero s]
    (S : Stacks 242 A) (V : ℕ) (D E : ZMod s → GaussianInt)
    (rhsTail rhs queue field raw : List (Fin (A+4)))
    (h : RetainedCouplingReady precision q w s t u band a b raw
      (embStk (Fin.castLE (by decide : 117 ≤ 242)) S)) :
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let F := embOvr e (periodicBoundaryResult (embStk e S) V s t band a b w D E rhsTail).get S
    RetainedCouplingReady precision q w s t u band a b queue
      (embStk (Fin.castLE (by decide : 117 ≤ 248)) (periodicRecoveryInputBank F rhs queue field)) := by
  dsimp only
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  let J := periodicBoundaryResult (embStk e S) V s t band a b w D E rhsTail
  let F := embOvr e J.get S
  let K := periodicRecoveryInputBank F rhs queue field
  have hinj : Function.Injective e := by
    intro i j he; exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have hleft : F.L = S.L := by
    change (embOvr e (embStk e S).get S).L = S.L
    exact congrArg Stacks.L (embOvr_stk (e := e) S)
  apply h.of_source_frame (S' := embStk (Fin.castLE (by decide : 117 ≤ 248)) K)
  · simp [K,periodicRecoveryInputBank,writeRight,embStk]
  · funext i
    have hh := congrArg (fun R => R (Fin.castLE (by decide : 117 ≤ 242) i)) hleft
    have hi := i.isLt
    simpa [K,periodicRecoveryInputBank,writeRight,embStk,extendStacks,Fin.castLE,
      show i.val < 242 by omega] using hh
  · intro k h93 _ _ h110
    have hi := k.isLt
    have h93v : k.val ≠ 93 := fun he => h93 (Fin.ext he)
    have h110v : k.val ≠ 110 := fun he => h110 (Fin.ext he)
    by_cases h116 : k = 116
    · subst k
      have hh := h.fresh 116 (by decide)
      simpa [K,periodicRecoveryInputBank,writeRight,embStk] using hh.symm
    have h116v : k.val ≠ 116 := fun he => h116 (Fin.ext he)
    have hK : K.R (Fin.castLE (by decide : 117 ≤ 248) k) = F.R (Fin.castLE (by decide : 117 ≤ 242) k) := by
      simp [K,periodicRecoveryInputBank,writeRight,extendStacks,Fin.ext_iff,
        h93v,h110v,h116v,show k.val ≠ 143 by omega,show k.val ≠ 132 by omega,
        show k.val ≠ 167 by omega,show k.val ≠ 231 by omega,show k.val < 242 by omega]
      rfl
    change K.R _ = S.R _
    rw [hK]
    let i : Fin 168 := Fin.castLE (by decide : 117 ≤ 168) k
    have hh := embOvr_get hinj J.get S (.rt i)
    change F.R (e i) = (J.R i).map id at hh
    rw [List.map_id] at hh
    have he : e i = Fin.castLE (by decide : 117 ≤ 242) k := Fin.ext rfl
    rw [← he,hh]
    exact periodicBoundaryResult_frame (embStk e S) V s t band a b w D E rhsTail i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
      change ¬ (k.val = 93 ∨ k.val = 110 ∨ k.val = 116 ∨ k.val = 141 ∨ k.val = 143 ∨
        k.val = 148 ∨ k.val = 154 ∨ k.val = 156 ∨ k.val = 160 ∨ k.val = 164 ∨ k.val = 167)
      omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
