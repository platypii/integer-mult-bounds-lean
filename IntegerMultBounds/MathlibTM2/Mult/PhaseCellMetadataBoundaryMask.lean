module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryCouplingSourceIntervalMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! The residual's canonical binary geometry also generates its boundary mask.
Only the emitted mask occupies a new stack; all metadata are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Keep the generated mask outside the live packed residual and cell field. -/
def boundaryMaskPlacement (i : Fin 117) : Fin 168 :=
  if i = 109 then 167 else if i = 100 then 147 else if i = 99 then 148 else if i.val < 96 then ⟨i.val,by omega⟩ else ⟨i.val+48,by omega⟩

theorem boundaryMaskPlacement_injective : Function.Injective boundaryMaskPlacement := by
  intro i j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  unfold boundaryMaskPlacement at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

def metadataBoundaryMask {P U : Type} {Q A : ℕ} : Pr P 168 Q A U :=
  embProg boundaryMaskPlacement Empty.elim
    (binaryIntervalStreamHost (P := Empty) (couplingSourceIntervalMaskCode true))

theorem metadataBoundaryMask_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 168 Q A U} [NeZero s]
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmeta : CouplingIntervalMetadata V s t band a b origin N S)
    (hfit : origin+N ≤ s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (hblank : ∀ k : Fin 168, k.val < 32 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((29*N+2)*tblC V 1+66*V+2*N+70) ∧
      Exec body metadataBoundaryMask (mk v S) m
        (mk v' {S with R := (Function.update S.R 167
          (couplingSourceIntervalMaskSymbols true A s t band a b origin N++S.R 167))}) := by
  let value := fun i => couplingIntervalValue s t band a b origin N (boundaryMaskPlacement i)
  have hbound : ∀ i, value (intervalGuardBankSource i) < 2^V := by
    intro i
    apply couplingIntervalValue_bound hfit haS hbS hst hfitV
    nlinarith [Nat.zero_le (t*t)]
  have hencoded : ∀ i, (embStk boundaryMaskPlacement S).R (intervalGuardBankSource i) =
      binSyms V (value (intervalGuardBankSource i)) := by
    intro i
    apply hmeta.encoded
    simp only [intervalGuardBankSource]
    split_ifs <;> decide
  have hblank' : ∀ r, (embStk boundaryMaskPlacement S).R (intervalGuardReg r) = [] := by
    intro r
    have hr := intervalGuardReg_range r
    have h109 : intervalGuardReg r ≠ 109 := by
      intro he; have hh := congrArg Fin.val he; norm_num at hh; omega
    have h100 : intervalGuardReg r ≠ 100 := by
      intro he; have hh := congrArg Fin.val he; norm_num at hh; omega
    have h99 : intervalGuardReg r ≠ 99 := by
      intro he; have hh := congrArg Fin.val he; norm_num at hh; omega
    simpa [embStk,boundaryMaskPlacement,h109,h100,h99,show (intervalGuardReg r).val < 96 by omega] using
      hblank ⟨(intervalGuardReg r).val,by omega⟩ (by omega)
  obtain ⟨v₁,m,hu₁,hm,he⟩ := binaryCouplingSourceIntervalMask_exec
    (body := fun p : Empty => nomatch p) true value
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    (by simp [value,boundaryMaskPlacement,couplingIntervalValue])
    hfit (NeZero.pos s) hst haS hbS hwide hbound
    (embDn boundaryMaskPlacement v) (embStk boundaryMaskPlacement S) hmeta.width hencoded hblank'
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    boundaryMaskPlacement_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR boundaryMaskPlacement_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
