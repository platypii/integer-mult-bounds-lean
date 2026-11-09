module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! One restoring division step has a linear transient reserve and retains one quotient bit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem divIter_native (rr bw q tx ty tz cy : Fin T) :
    mnNativePushBound 3 (divIter (P := P) (Q := Q) (A := A) (U := U) rr bw q tx ty tz cy) := by
  simp [divIter,bshift,zipPass,zipInit,zipStep,pushBit,bclear,moveR,moveStep,
    bmoveLow,uclear,drainR,popDo,dropTop,whileR,peekR,mnNativePushBound,mnActPush]

theorem divIter_exec_within {rr bw q tx ty tz cy : Fin T}
    (hreg : [rr,bw,q,tx,ty,tz].Nodup) (hcr : cy ≠ rr) (hcb : cy ≠ bw)
    {W ρ y : ℕ} (bit : Bool) (hu : 2*ρ+bit.toNat < 2^W) (hy : y < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (hsym : v.sym = some (bitSymbol bit))
    (hr : S.R rr = binSyms W ρ) (hb : S.R bw = binSyms W y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      let F : Stacks T A := {S with R := (Function.update
        (Function.update S.R rr (binSyms W
          (if y ≤ 2*ρ+bit.toNat then 2*ρ+bit.toNat-y else 2*ρ+bit.toNat)))
        q (bitSymbol (decide (y ≤ 2*ρ+bit.toNat))::S.R q))}
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(12*W+18))
        depth (divIter rr bw q tx ty tz cy) (mk v S) (12*W+18) (mk v' F) ∧
      mnSize (mk v' F) = mnSize (mk v S)+1 := by
  obtain ⟨v',huser,he⟩ := divIter_exec body hreg hcr hcb bit hu hy v S hsym hr hb htx hty htz
  refine ⟨v',huser,mn_native_exec_within he 3 (divIter_native ..) depth _ (Nat.le_refl _),?_⟩
  have hrq : rr ≠ q := by
    have hh := hreg
    regs_ne hh
    assumption
  let words : List (Fin (A+4)) := binSyms W
    (if y ≤ 2*ρ+bit.toNat then 2*ρ+bit.toNat-y else 2*ρ+bit.toNat)
  let bitWord := bitSymbol (decide (y ≤ 2*ρ+bit.toNat))::S.R q
  let D : Stacks T A := {S with R := Function.update S.R rr words}
  have h₁ : mnSize (mk v D)+(S.R rr).length = mnSize (mk v S)+W := by
    simpa only [D,words,mk,update_rt,get_rt,length_binSyms] using
      mn_size_update (mk v S) v (.rt rr) words
  have h₂ : mnSize (mk v' {D with R := Function.update D.R q bitWord})+(D.R q).length =
      mnSize (mk v D)+(S.R q).length+1 := by
    simpa only [bitWord,mk,update_rt,get_rt,List.length_cons,Nat.add_assoc] using
      mn_size_update (mk v D) v' (.rt q) bitWord
  have hq : D.R q = S.R q := by simp [D,hrq.symm]
  rw [hr,length_binSyms] at h₁
  rw [hq] at h₂
  change mnSize (mk v' {D with R := Function.update D.R q bitWord}) = _
  omega

end IntegerMultBounds.MathlibTM2.Host
