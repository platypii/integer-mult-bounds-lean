module

public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! A native symbol scan shares one iteration reserve above its final retained stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def SymStockSpec (p : Pr P T Q A U) (a t : Fin T) (l : List (Fin (A+4)))
    (Ψ : ℕ → Regs T A) (cost : ℕ) : Prop :=
  ∀ j (hj : j < l.length) (v : HS T Q A U) (S : Stacks T A),
    v.sym = some l[j] → (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ cost ∧
      Exec body p (mk v S) m (mk v' {S with R := R'}) ∧
      R' a = S.R a ∧ R' t = S.R t ∧
      (∀ k, k ≠ a → k ≠ t → R' k = Ψ (j+1) k) ∧
      mnSize (mk v S) ≤ mnSize (mk v' {S with R := R'})

theorem SymStockSpec.toSymSpec {p : Pr P T Q A U} {a t : Fin T}
    {l : List (Fin (A+4))} {Ψ : ℕ → Regs T A} {cost : ℕ}
    (hp : SymStockSpec (body := body) p a t l Ψ cost) : SymSpec body p a t l Ψ cost := by
  intro j hj v S hsym hR
  obtain ⟨vf,Rf,m,hu,hm,he,ha,ht,hnext,_⟩ := hp j hj v S hsym hR
  exact ⟨vf,Rf,m,hu,hm,he,ha,ht,hnext⟩

private theorem eachSym_loop_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {l : List (Fin (A+4))} {Ψ : ℕ → Regs T A} {cost c : ℕ}
    (hc : 1 ≤ c) (hnative : mnNativePushBound c p)
    (hp : SymStockSpec (body := body) p a t l Ψ cost) (depth : ℕ) :
    ∀ (n j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      j+n = l.length → S.R a = l.drop j →
      (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) → v.flag = (S.R a).head?.isSome →
      ∃ (vf : HS T Q A U) (F : Stacks T A) (m : ℕ),
        mnSize (mk v S) ≤ mnSize (mk vf F) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vf F)+depth+c*(cost+2)) depth
          (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk vf F) := by
  intro n
  induction n with
  | zero =>
    intro j v S hn ha _ hflag
    have hnil : S.R a = [] := by rw [ha]; exact List.drop_eq_nil_of_le (by omega)
    exact ⟨v,S,1,le_rfl,.loop_false (by simpa [hnil] using hflag) (by omega)⟩
  | succ n ih =>
    intro j v S hn ha hR hflag
    have hj : j < l.length := by omega
    have hcons : S.R a = l[j]::l.drop (j+1) := by rw [ha,List.drop_eq_getElem_cons hj]
    let S₀ : Stacks T A := {S with R := (Function.update (Function.update S.R a (l.drop (j+1))) t (l[j]::S.R t))}
    have hpop : (popPush a t : Act T Q A U).run (mk v S) = mk {v with sym := some l[j]} S₀ := by
      dsimp only [S₀]
      simp only [popPush,Action.run,mk_var,mk_stk,get_rt,hcons,List.head?_cons,
        List.tail_cons,Option.getD_some,update_rt,store_mk]
      rw [Function.update_of_ne hat.symm]
    obtain ⟨v₁,R₁,m,hu,hm,he,ha₁,ht₁,hR₁,hmono⟩ := hp j hj {v with sym := some l[j]} S₀ rfl
      (by intro k hka hkt; simpa [S₀,hka,hkt] using hR k hka hkt)
    let F₁ : Stacks T A := {S with R := R₁}
    have ha₁' : F₁.R a = l.drop (j+1) := by simpa [F₁,S₀,hat] using ha₁
    obtain ⟨vf,F,k,hfinal,hw⟩ := ih (j+1) {v₁ with flag := (F₁.R a).head?.isSome} F₁
      (by omega) ha₁' hR₁ rfl
    have hsize := mn_popPush_size hat l[j] (l.drop (j+1)) v S hcons
    change mnSize (mk v S₀) = mnSize (mk v S) at hsize
    change mnSize (mk v S₀) ≤ mnSize (mk v₁ F₁) at hmono
    change mnSize (mk v₁ F₁) ≤ mnSize (mk vf F) at hfinal
    have hpeek := Exec.act (body := body) (peekR a) (mk v₁ F₁)
    rw [peekR_run] at hpeek
    have hiter := Exec.seq (hpop ▸ Exec.act (body := body) (popPush a t) (mk v S)) (Exec.seq he hpeek)
    have hniter : mnNativePushBound c (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))) :=
      ⟨by simpa [popPush,mnNativePushBound,mnActPush] using hc,hnative,
        by simp [peekR,mnNativePushBound,mnActPush]⟩
    refine ⟨vf,F,1+(m+1)+k+1,by omega,.loop_true (by show v.flag = true; rw [hflag,hcons]; rfl) ?_ hw⟩
    apply mn_native_exec_within hiter c hniter depth
    have hmul := Nat.mul_le_mul_left c (show 1+(m+1) ≤ cost+2 by omega)
    omega

/-- Retained output is charged once, and native scratch is shared across symbols. -/
theorem eachSym_within_final_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Ψ : ℕ → Regs T A} {cost c : ℕ} (hc : 1 ≤ c) (hnative : mnNativePushBound c p)
    (v : HS T Q A U) (S : Stacks T A)
    (hp : SymStockSpec (body := body) p a t (S.R a) Ψ cost)
    (hR : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ 0 k)
    {z : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (hex : Exec body (eachSym a t p) (mk v S) n z) (depth : ℕ) :
    ExecWithin body (fun d u => mnSize u+d ≤ mnSize z+depth+c*(cost+2)) depth
      (eachSym a t p) (mk v S) n z := by
  obtain ⟨vf,F,m,hmono,hw⟩ := eachSym_loop_stock hat hc hnative hp depth (S.R a).length 0
    {v with flag := (S.R a).head?.isSome} S (by simp) (by simp) hR rfl
  change mnSize (mk v S) ≤ mnSize (mk vf F) at hmono
  have hpeek := Exec.act (body := body) (peekR a) (mk v S)
  rw [peekR_run] at hpeek
  have hpw := mn_native_exec_within hpeek 0 (by simp [mnNativePushBound,peekR,mnActPush]) depth
    (mnSize (mk vf F)+depth+c*(cost+2)) (by omega)
  have hwhole := ExecWithin.seq hpw hw
  obtain ⟨hn,hz⟩ := hwhole.toExec.unique hex
  simpa only [←hn,hz,eachSym] using hwhole

/-- Execute the complete scan while retaining its exact frame and runtime contract. -/
theorem eachSym_exec_within_final_stock {a t : Fin T} (hat : a ≠ t)
    {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {cost c : ℕ}
    (hc : 1 ≤ c) (hnative : mnNativePushBound c p) (v : HS T Q A U) (S : Stacks T A)
    (hp : SymStockSpec (body := body) p a t (S.R a) Ψ cost)
    (hR : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ 0 k) (depth : ℕ) :
    ∃ (vf : HS T Q A U) (Rf : Regs T A) (m : ℕ), vf.user = v.user ∧
      m ≤ (S.R a).length*(cost+3)+2 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vf {S with R := Rf})+depth+c*(cost+2))
        depth (eachSym a t p) (mk v S) m (mk vf {S with R := Rf}) ∧
      Rf a = [] ∧ Rf t = (S.R a).reverse++S.R t ∧
      ∀ k, k ≠ a → k ≠ t → Rf k = Ψ (S.R a).length k := by
  obtain ⟨vf,Rf,m,hu,hm,he,ha,ht,hnext⟩ := eachSym_exec body hat v S hp.toSymSpec hR
  exact ⟨vf,Rf,m,hu,hm,eachSym_within_final_stock hat hc hnative v S hp hR he depth,ha,ht,hnext⟩

end IntegerMultBounds.MathlibTM2.Host
