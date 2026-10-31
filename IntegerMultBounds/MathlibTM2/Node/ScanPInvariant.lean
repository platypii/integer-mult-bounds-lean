module

public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! Counted scans carry semantic invariants, including existential output
certificates, while sharing one body workspace reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The invariant ignores the scan counters; body calls restore both counters. -/
def IterWithinSpec (body : P → Pr P T Q A U) (p : Pr P T Q A U)
    (a t : Fin T) (I : ℕ → Regs T A → Prop) (cost N bound reserve depth : ℕ) : Prop :=
  ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A), I j S.R → mnSize (Host.mk v S) ≤ bound →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ cost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ bound+depth+reserve) depth
        p (Host.mk v S) m (Host.mk v' {S with R := R'}) ∧
      R' a = S.R a ∧ R' t = S.R t ∧ I (j+1) R' ∧
      mnSize (Host.mk v' {S with R := R'}) ≤ bound

private theorem scanP_loop_invariant {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {I : ℕ → Regs T A → Prop} {cost N bound reserve depth : ℕ}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → I j R → I j R')
    (hp : IterWithinSpec body p a t I cost N bound reserve depth) :
    ∀ (xs : List (Fin (A+4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R a = xs → j+xs.length ≤ N → I j S.R → mnSize (Host.mk v S) ≤ bound →
      v.flag = xs.head?.isSome →
      ∃ (vf : HS T Q A U) (R : Regs T A) (n : ℕ), vf.user = v.user ∧
        n ≤ xs.length*(cost+3)+1 ∧ R a = [] ∧ R t = xs.reverse++S.R t ∧
        I (j+xs.length) R ∧ mnSize (Host.mk vf {S with R := R}) ≤ bound ∧
        ExecWithin body (fun d z => mnSize z+d ≤ bound+depth+reserve) depth
          (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (Host.mk v S) n (Host.mk vf {S with R := R}) := by
  intro xs
  induction xs with
  | nil =>
    intro j v S ha _ hI hbound hflag
    exact ⟨v,S.R,1,rfl,by simp,ha,by simp,by simpa using hI,hbound,
      .loop_false (by simpa using hflag) (by omega)⟩
  | cons x xs ih =>
    intro j v S ha hN hI hbound hflag
    let S₀ : Stacks T A := {S with R := Function.update (Function.update S.R a xs) t (x::S.R t)}
    have hpop : (popPush a t : Act T Q A U).run (Host.mk v S) = Host.mk {v with sym := some x} S₀ := by
      simp [popPush,Action.run,ha,update_rt,S₀,hat.symm]
    have hsize := mn_popPush_size hat x xs v S ha
    change mnSize (Host.mk v S₀) = mnSize (Host.mk v S) at hsize
    have hI₀ : I j S₀.R := hframe j S.R S₀.R (by
      intro k hka hkt; simp [S₀,hka,hkt]) hI
    obtain ⟨v₁,R₁,m,hu,hm,he,ha₁,ht₁,hI₁,hnext⟩ := hp j (by simp at hN; omega)
      {v with sym := some x} S₀ hI₀ (by change mnSize (Host.mk v S₀) ≤ bound; rw [hsize]; exact hbound)
    let F₁ : Stacks T A := {S with R := R₁}
    have ha₁' : F₁.R a = xs := by simpa [F₁,S₀,hat] using ha₁
    obtain ⟨vf,R,n,huser,hn,hRa,hRt,hIf,hfinal,hw⟩ := ih (j+1)
      {v₁ with flag := xs.head?.isSome} F₁ ha₁' (by simp at hN; omega) hI₁ hnext rfl
    have hpeek := Exec.act (body := body) (peekR a) (Host.mk v₁ F₁)
    rw [peekR_run,ha₁'] at hpeek
    have hpopw := ExecWithin.act (body := body)
      (Inv := fun d z => mnSize z+d ≤ bound+depth+reserve) (d := depth)
      (popPush a t) (Host.mk v S) (by omega)
      (by rw [hpop]; change mnSize (Host.mk v S₀)+depth ≤ _; omega)
    rw [hpop] at hpopw
    have hpeekw := mn_native_exec_within hpeek 0
      (by simp [mnNativePushBound,peekR,mnActPush]) depth (bound+depth+reserve) (by
        change mnSize (Host.mk v₁ F₁)+depth ≤ _
        change mnSize (Host.mk v₁ F₁) ≤ bound at hnext
        omega)
    refine ⟨vf,R,1+(m+1)+n+1,huser.trans hu,?_,hRa,?_,?_,hfinal,
      .loop_true (by simpa using hflag) (.seq hpopw (.seq he hpeekw)) hw⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
    · rw [hRt]
      have ht₁' : F₁.R t = x::S.R t := by simpa [F₁,S₀] using ht₁
      rw [ht₁']
      simp [List.reverse_cons,List.append_assoc]
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hIf

/-- Execute a fixed counted body, carrying semantic certificates and a shared
workspace reserve. The count register is restored, and its saved bank is blank. -/
theorem scanP_exec_within_invariant {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {I : ℕ → Regs T A → Prop} {cost N bound reserve depth : ℕ}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → I j R → I j R')
    (hp : IterWithinSpec body p a t I cost N bound reserve depth)
    (v : HS T Q A U) (S : Stacks T A) (hI : I 0 S.R) (hcount : (S.R a).length = N)
    (hsaved : S.R t = []) (hbound : mnSize (Host.mk v S) ≤ bound) :
    ∃ (vf : HS T Q A U) (R : Regs T A) (n : ℕ), vf.user = v.user ∧
      n ≤ N*(cost+5)+4 ∧ R a = S.R a ∧ R t = [] ∧ I N R ∧
      mnSize (Host.mk vf {S with R := R}) ≤ bound ∧
      ExecWithin body (fun d z => mnSize z+d ≤ bound+depth+reserve) depth
        (scanP a t p) (Host.mk v S) n (Host.mk vf {S with R := R}) := by
  obtain ⟨v₁,R₁,n,hu,hn,ha,ht,hIf,hfinal,hw⟩ := scanP_loop_invariant hat hframe hp
    (S.R a) 0 {v with flag := (S.R a).head?.isSome} S rfl (by omega) hI hbound rfl
  let F : Stacks T A := {S with R := R₁}
  obtain ⟨vf,hu₂,he⟩ := moveR_exec body t a hat.symm id v₁ F
  have hsize := mn_movedR_size a t hat v₁ vf F
  change mnSize (Host.mk v₁ F) ≤ bound at hfinal
  have hmove := Host.moveR_within t a id he depth (bound+depth+reserve) (by omega)
  have hpeek := Exec.act (body := body) (peekR a) (Host.mk v S)
  rw [peekR_run] at hpeek
  have hpw := mn_native_exec_within hpeek 0 (by simp [mnNativePushBound,peekR,mnActPush]) depth
    (bound+depth+reserve) (by omega)
  have hwhole := ExecWithin.seq hpw (.seq hw hmove)
  let R := movedR R₁ t a id (R₁ t)
  have hRa : R a = S.R a := by simp [R,movedR,ha,ht,hsaved]
  have hRt : R t = [] := by simp [R,movedR,hat.symm]
  have hIR : I N R := by
    apply hframe N R₁ R
    · intro k hka hkt; simp [R,movedR,hka,hkt]
    · simpa only [Nat.zero_add,hcount] using hIf
  refine ⟨vf,R,1+(n+(2*(F.R t).length+2)),hu₂.trans hu,?_,hRa,hRt,hIR,?_,?_⟩
  · have hlen : (F.R t).length = N := by simp [F,ht,hsaved,hcount]
    rw [hlen]
    rw [hcount] at hn
    nlinarith
  · change mnSize (Host.mk vf {F with R := R}) ≤ bound
    rw [hsize]
    exact hfinal
  · simpa only [scanP,F,R] using hwhole

end IntegerMultBounds.MathlibTM2.Node
