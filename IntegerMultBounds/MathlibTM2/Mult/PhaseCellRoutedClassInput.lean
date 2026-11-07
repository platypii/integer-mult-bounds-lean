module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInputReady
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

/-! Move the owned R4 output prefix into the numerical class source. The
external borrowed suffix is untouched, scratch is restored, and readiness
observes only the numerical bank and its retained table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installRoutedClassInput (bank : ComputedClassBank → Fin T)
    (count src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp) (moveR saved (control bank .source) id)

theorem installRoutedClassInput_exec (bank : ComputedClassBank → Fin T)
    (count src saved tmp : Fin T)
    (hreg : [count,src,saved,tmp,control bank .source].Nodup)
    (payload tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = payload++tail) (hcount : (S.R count).length = payload.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (installRoutedClassInput bank count src saved tmp) (mk v S) (6*payload.length+6)
        (mk v' {S with R := (Function.update (Function.update S.R src tail)
          (control bank .source) (payload++S.R (control bank .source)))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v S payload tail hsrc hcount htmp
  let M : Stacks T A := {S with R := Function.update (Function.update S.R src tail) saved payload.reverse}
  have ht : Exec body (transfer count src saved tmp) (mk v S) (4*payload.length+4) (mk v₁ M) := by
    simpa only [M,hsaved,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved (control bank .source)
    (by assumption) id v₁ M
  have hm : M.R saved = payload.reverse := by simp [M]
  have hc : M.R (control bank .source) = S.R (control bank .source) := by
    simp [M,Ne.symm ‹src ≠ control bank .source›,Ne.symm ‹saved ≠ control bank .source›]
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  refine (Exec.seq ht he₂).cast ?_ ?_
  · simp only [hm,List.length_reverse]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hsrc : k = src
    · subst k
      simp [M,movedR,hsaved,Ne.symm ‹src ≠ saved›,‹src ≠ saved›,‹src ≠ control bank .source›]
    by_cases hsave : k = saved
    · subst k
      simp [M,movedR,hsaved,‹saved ≠ control bank .source›,Ne.symm ‹src ≠ saved›]
    by_cases hdst : k = control bank .source
    · subst k
      simp [M,movedR,hsaved,Ne.symm ‹src ≠ control bank .source›,Ne.symm ‹saved ≠ control bank .source›]
    · simp [M,movedR,hsrc,hsave,hdst]

theorem InputReady.install_routed_prefix {bank : ComputedClassBank → Fin T}
    {hinj : Function.Injective bank} {rg : TblR 12 → Fin T}
    {B D s width radius L : ℕ} {st : TblSt 12 A} {S : Stacks T A}
    (h : InputReady bank hinj rg B D s width radius L st S)
    (src : Fin T) (payload tail : List (Fin (A+4)))
    (hsrcBank : ∀ k, src ≠ bank k) (hsrcTable : ∀ r, src ≠ rg r)
    (hsourceTable : ∀ r, rg r ≠ control bank .source) :
    InputReady bank hinj rg B D s width radius L st
      {S with R := (Function.update (Function.update S.R src tail)
        (control bank .source) (payload++S.R (control bank .source)))} := by
  apply h.of_bank_frame
  · intro k hk
    have hne : bank k ≠ control bank .source := by intro he; exact hk (hinj he)
    simp only [Function.update_of_ne hne,Function.update_of_ne (hsrcBank k).symm]
  · intro r
    simp only [Function.update_of_ne (hsourceTable r),Function.update_of_ne (hsrcTable r).symm]
  · intro i; rfl

/-- Closed prefix handoff: actual execution, numerical readiness and a
source-linear stock allowance, all independent of the borrowed suffix. -/
theorem installRoutedClassInput_exec_of_ready (bank : ComputedClassBank → Fin T)
    (hinj : Function.Injective bank) (rg : TblR 12 → Fin T)
    (B D s width radius L : ℕ) (st : TblSt 12 A)
    (count src saved tmp : Fin T)
    (hreg : [count,src,saved,tmp,control bank .source].Nodup)
    (payload tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (h : InputReady bank hinj rg B D s width radius L st S)
    (hsrc : S.R src = payload++tail) (hcount : (S.R count).length = payload.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsrcBank : ∀ k, src ≠ bank k) (hsrcTable : ∀ r, src ≠ rg r)
    (hsourceTable : ∀ r, rg r ≠ control bank .source) :
    let F := {S with R := (Function.update (Function.update S.R src tail)
      (control bank .source) (payload++S.R (control bank .source)))}
    ∃ v', v'.user = v.user ∧ InputReady bank hinj rg B D s width radius L st F ∧
      mnSize (mk v' F) = mnSize (mk v S) ∧
      Exec body (installRoutedClassInput bank count src saved tmp) (mk v S) (6*payload.length+6) (mk v' F) ∧
      ∀ C, mnProgPush (installRoutedClassInput (P := P) (Q := Q) (A := A) (U := U) bank count src saved tmp) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*(6*payload.length+6))
          depth (installRoutedClassInput bank count src saved tmp) (mk v S) (6*payload.length+6) (mk v' F) := by
  dsimp only
  obtain ⟨v',hu,he⟩ := installRoutedClassInput_exec bank count src saved tmp hreg payload tail v S hsrc hcount hsaved htmp
  let M : Stacks T A := {S with R := Function.update S.R src tail}
  have ha := mn_size_update (mk v S) v (.rt src) tail
  have hb := mn_size_update (mk v M) v' (.rt (control bank .source))
    (payload++S.R (control bank .source))
  have hne : control bank .source ≠ src := (hsrcBank (.control .source)).symm
  have hbalanceA : mnSize (mk v M)+(S.R src).length = mnSize (mk v S)+tail.length := by
    simpa only [M,mk,update_rt,get_rt] using ha
  have hbalanceB : mnSize (mk v' {S with R := (Function.update (Function.update S.R src tail)
      (control bank .source) (payload++S.R (control bank .source)))})+(S.R (control bank .source)).length =
      mnSize (mk v M)+(payload++S.R (control bank .source)).length := by
    simpa only [M,mk,update_rt,get_rt,Function.update_of_ne hne] using hb
  have hsize : mnSize (mk v' {S with R := (Function.update (Function.update S.R src tail)
      (control bank .source) (payload++S.R (control bank .source)))}) = mnSize (mk v S) := by
    rw [hsrc,List.length_append] at hbalanceA
    rw [List.length_append] at hbalanceB
    omega
  exact ⟨v',hu,h.install_routed_prefix src payload tail hsrcBank hsrcTable hsourceTable,hsize,he,
    mn_bounded_exec_certify he (le_refl _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
