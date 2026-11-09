module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScanInvariant
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! Counted scans share a reserve under an invariant containing computed witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- A restoring step preserves an existential boundary invariant and a stock cap. -/
def InvariantBoundedStockSpec (body : P → Pr P T Q A U) (p : Pr P T Q A U)
    (a t : Fin T) (Inv : ℕ → Regs T A → Prop) (left : Regs T A)
    (cost boundary : ℕ → ℕ) (N bound reserve depth : ℕ) : Prop :=
  ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A),
    S.L = left → Inv j S.R → mnSize (mk v S) ≤ boundary j →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ cost j ∧
      ExecWithin body (fun d z => mnSize z+d ≤ bound+depth+reserve) depth
        p (mk v S) m (mk v' {S with R := R'}) ∧
      R' a = S.R a ∧ R' t = S.R t ∧ Inv (j+1) R' ∧
      mnSize (mk v' {S with R := R'}) ≤ boundary (j+1)

private theorem scanInvariant_loop_bounded_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Inv : ℕ → Regs T A → Prop} {cost boundary : ℕ → ℕ} {N bound reserve depth : ℕ}
    {left : Regs T A}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → Inv j R → Inv j R')
    (hboundary : ∀ j ≤ N, boundary j ≤ bound)
    (hp : InvariantBoundedStockSpec body p a t Inv left cost boundary N bound reserve depth) :
    ∀ (xs : List (Fin (A+4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R a = xs → j+xs.length ≤ N → S.L = left → Inv j S.R →
      mnSize (Host.mk v S) ≤ boundary j → v.flag = xs.head?.isSome →
      ∃ (vf : HS T Q A U) (F : Stacks T A) (n : ℕ),
        mnSize (Host.mk vf F) ≤ bound ∧
        ExecWithin body (fun d z => mnSize z+d ≤ bound+depth+reserve) depth
          (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (Host.mk v S) n (Host.mk vf F) := by
  intro xs
  induction xs with
  | nil =>
    intro j v S _ _ _ _ hbound hflag
    exact ⟨v,S,1,hbound.trans (hboundary j (by omega)),.loop_false (by simpa using hflag) (by have hb := hboundary j (by omega); omega)⟩
  | cons x xs ih =>
    intro j v S ha hN hL hR hbound hflag
    let S₀ : Stacks T A := {S with R := Function.update (Function.update S.R a xs) t (x::S.R t)}
    have hpop : (popPush a t : Act T Q A U).run (Host.mk v S) = Host.mk {v with sym := some x} S₀ := by
      simp [popPush,Action.run,ha,update_rt,S₀,hat.symm]
    have hsize := mn_popPush_size hat x xs v S ha
    change mnSize (Host.mk v S₀) = mnSize (Host.mk v S) at hsize
    obtain ⟨v₁,R₁,m,hu,hm,he,ha₁,ht₁,hR₁,hnext⟩ := hp j (by simp at hN; omega)
      {v with sym := some x} S₀ hL (hframe j S.R S₀.R (by intro k hka hkt; simp [S₀,hka,hkt]) hR) (by change mnSize (Host.mk v S₀) ≤ boundary j; rw [hsize]; exact hbound)
    let F₁ : Stacks T A := {S with R := R₁}
    have ha₁' : F₁.R a = xs := by simpa [F₁,S₀,hat] using ha₁
    obtain ⟨vf,F,n,hfinal,hw⟩ := ih (j+1) {v₁ with flag := xs.head?.isSome} F₁ ha₁'
      (by simp at hN; omega) hL hR₁ hnext rfl
    have hpeek := Exec.act (body := body) (peekR a) (Host.mk v₁ F₁)
    rw [peekR_run,ha₁'] at hpeek
    have hpopw := ExecWithin.act (body := body)
      (Inv := fun d z => mnSize z+d ≤ bound+depth+reserve) (d := depth)
      (popPush a t) (Host.mk v S) (by have hb := hboundary j (by simp at hN; omega); omega)
      (by rw [hpop]; change mnSize (Host.mk v S₀)+depth ≤ _; have hb := hboundary j (by simp at hN; omega); omega)
    rw [hpop] at hpopw
    have hpeekw := mn_native_exec_within hpeek 0
      (by simp [mnNativePushBound,peekR,mnActPush]) depth (bound+depth+reserve) (by
        change mnSize (Host.mk v₁ F₁)+depth ≤ _
        change mnSize (Host.mk v₁ F₁) ≤ boundary (j+1) at hnext
        have hb := hboundary (j+1) (by simp at hN; omega)
        omega)
    exact ⟨vf,F,1+(m+1)+n+1,hfinal,
      .loop_true (by simpa using hflag) (.seq hpopw (.seq he hpeekw)) hw⟩

/-- A restoring scan shares one iteration reserve above a boundary bound. -/
theorem scanInvariant_within_bounded_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Inv : ℕ → Regs T A → Prop} {cost boundary : ℕ → ℕ} {N bound reserve depth : ℕ}
    {left : Regs T A}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → Inv j R → Inv j R')
    (hboundary : ∀ j ≤ N, boundary j ≤ bound)
    (hp : InvariantBoundedStockSpec body p a t Inv left cost boundary N bound reserve depth) (j : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : j+(S.R a).length ≤ N) (hL : S.L = left) (hR : Inv j S.R)
    (hbound : mnSize (Host.mk v S) ≤ boundary j)
    {z : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (hex : Exec body (scanP a t p) (Host.mk v S) n z) :
    ExecWithin body (fun d u => mnSize u+d ≤ bound+depth+reserve) depth
      (scanP a t p) (Host.mk v S) n z := by
  obtain ⟨vf,F,m,hmono,hw⟩ := scanInvariant_loop_bounded_stock hat hframe hboundary hp (S.R a) j
    {v with flag := (S.R a).head?.isSome} S rfl hN hL hR hbound rfl
  obtain ⟨v',hu,he⟩ := moveR_exec body t a hat.symm id vf F
  change mnSize (Host.mk vf F) ≤ bound at hmono
  have hsize := mn_movedR_size a t hat vf v' F
  change mnSize (Host.mk v' {F with R := movedR F.R t a id (F.R t)}) = mnSize (Host.mk vf F) at hsize
  have hpeek := Exec.act (body := body) (peekR a) (Host.mk v S)
  rw [peekR_run] at hpeek
  have hpw := mn_native_exec_within hpeek 0 (by simp [mnNativePushBound,peekR,mnActPush]) depth
    (bound+depth+reserve) (by have hb := hboundary j (by omega); omega)
  have hmove := Host.moveR_within t a id he depth (bound+depth+reserve) (by omega)
  have hwhole := ExecWithin.seq hpw (.seq hw hmove)
  obtain ⟨hn,hz⟩ := hwhole.toExec.unique hex
  simpa only [←hn,hz,scanP] using hwhole

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
