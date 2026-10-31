module

public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Restoring counted scans share one native iteration reserve. Completed
iterations may retain output, but must not shrink total stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- A counted iteration with exact frame and nondecreasing boundary stock. -/
def IterStockSpec (body : P → Pr P T Q A U) (p : Pr P T Q A U) (a t : Fin T) (Ψ : ℕ → Regs T A) (cost N : ℕ) : Prop :=
  ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A), (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ cost ∧
      Exec body p (Host.mk v S) m (Host.mk v' {S with R := R'}) ∧
      R' a = S.R a ∧ R' t = S.R t ∧
      (∀ k, k ≠ a → k ≠ t → R' k = Ψ (j+1) k) ∧
      mnSize (Host.mk v S) ≤ mnSize (Host.mk v' {S with R := R'})

theorem IterStockSpec.toIterSpec {p : Pr P T Q A U} {a t : Fin T} {Ψ : ℕ → Regs T A} {cost N : ℕ}
    (h : IterStockSpec body p a t Ψ cost N) : IterSpec body p a t Ψ (fun _ => cost) N := by
  intro j hj v S hS
  obtain ⟨v',R',m,hu,hm,he,ha,ht,hR,_⟩ := h j hj v S hS
  exact ⟨v',R',m,hu,hm,he,ha,ht,hR⟩

private theorem popPush_size {a t : Fin T} (hat : a ≠ t) (x : Fin (A+4)) (xs : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = x::xs) :
    mnSize (Host.mk v {S with R := Function.update (Function.update S.R a xs) t (x::S.R t)}) =
      mnSize (Host.mk v S) := by
  let F : Stacks T A := {S with R := Function.update S.R a xs}
  have h₁ : mnSize (Host.mk v F)+(S.R a).length = mnSize (Host.mk v S)+xs.length := by
    simpa only [F,Host.mk,update_rt,get_rt] using mn_size_update (Host.mk v S) v (.rt a) xs
  have h₂ : mnSize (Host.mk v {F with R := Function.update F.R t (x::S.R t)})+(F.R t).length =
      mnSize (Host.mk v F)+(x::S.R t).length := by
    simpa only [Host.mk,update_rt,get_rt] using mn_size_update (Host.mk v F) v (.rt t) (x::S.R t)
  have ht : F.R t = S.R t := Function.update_of_ne hat.symm _ _
  rw [ht,List.length_cons] at h₂
  rw [ha,List.length_cons] at h₁
  change mnSize (Host.mk v {F with R := Function.update F.R t (x::S.R t)}) = _
  omega

theorem mn_movedR_size (a t : Fin T) (hat : a ≠ t) (v w : HS T Q A U) (S : Stacks T A) :
    mnSize (Host.mk w {S with R := movedR S.R t a id (S.R t)}) = mnSize (Host.mk v S) := by
  let F : Stacks T A := {S with R := Function.update S.R t []}
  have h₁ : mnSize (Host.mk v F)+(S.R t).length = mnSize (Host.mk v S) := by
    simpa only [F,Host.mk,update_rt,get_rt,List.length_nil,Nat.add_zero] using
      mn_size_update (Host.mk v S) v (.rt t) []
  have h₂ : mnSize (Host.mk w {F with R := Function.update F.R a ((S.R t).reverse++S.R a)})+(F.R a).length =
      mnSize (Host.mk v F)+((S.R t).reverse++S.R a).length := by
    simpa only [Host.mk,update_rt,get_rt] using
      mn_size_update (Host.mk v F) w (.rt a) ((S.R t).reverse++S.R a)
  have ha : F.R a = S.R a := Function.update_of_ne hat _ _
  rw [ha,List.length_append,List.length_reverse] at h₂
  change mnSize (Host.mk w {F with R := Function.update F.R a (((S.R t).map id).reverse++S.R a)}) = _
  simp only [List.map_id]
  omega

private theorem scanP_loop_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Ψ : ℕ → Regs T A} {cost N c : ℕ} (hc : 1 ≤ c) (hnative : mnNativePushBound c p)
    (hp : IterStockSpec body p a t Ψ cost N) (depth : ℕ) :
    ∀ (xs : List (Fin (A+4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R a = xs → j+xs.length ≤ N → (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
      v.flag = xs.head?.isSome →
      ∃ (vf : HS T Q A U) (F : Stacks T A) (n : ℕ),
        mnSize (Host.mk v S) ≤ mnSize (Host.mk vf F) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vf F)+depth+c*(cost+2)) depth
          (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (Host.mk v S) n (Host.mk vf F) := by
  intro xs
  induction xs with
  | nil =>
    intro j v S _ _ _ hflag
    exact ⟨v,S,1,le_rfl,.loop_false (by simpa using hflag) (by omega)⟩
  | cons x xs ih =>
    intro j v S ha hN hR hflag
    let S₀ : Stacks T A := {S with R := Function.update (Function.update S.R a xs) t (x::S.R t)}
    have hpop : (popPush a t : Act T Q A U).run (Host.mk v S) = Host.mk {v with sym := some x} S₀ := by
      simp [popPush,Action.run,ha,update_rt,S₀,hat.symm]
    obtain ⟨v₁,R₁,m,hu,hm,he,ha₁,ht₁,hR₁,hmono⟩ := hp j (by simp at hN; omega)
      {v with sym := some x} S₀ (by intro k hka hkt; simpa [S₀,hka,hkt] using hR k hka hkt)
    let F₁ : Stacks T A := {S with R := R₁}
    have ha₁' : F₁.R a = xs := by simpa [F₁,S₀,hat] using ha₁
    obtain ⟨vf,F,n,hfinal,hw⟩ := ih (j+1) {v₁ with flag := xs.head?.isSome} F₁ ha₁'
      (by simp at hN; omega) hR₁ rfl
    have hsize := popPush_size hat x xs v S ha
    change mnSize (Host.mk v S₀) = mnSize (Host.mk v S) at hsize
    have hmono' : mnSize (Host.mk v S₀) ≤ mnSize (Host.mk v₁ F₁) := hmono
    have hfinal' : mnSize (Host.mk v₁ F₁) ≤ mnSize (Host.mk vf F) := hfinal
    have hpeek := Exec.act (body := body) (peekR a) (Host.mk v₁ F₁)
    rw [peekR_run,ha₁'] at hpeek
    have hiter := Exec.seq (hpop ▸ Exec.act (body := body) (popPush a t) (Host.mk v S)) (Exec.seq he hpeek)
    have hniter : mnNativePushBound c (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))) := by
      exact ⟨by simpa [popPush,mnNativePushBound,mnActPush] using hc,hnative,
        by simp [peekR,mnNativePushBound,mnActPush]⟩
    refine ⟨vf,F,1+(m+1)+n+1,?_,.loop_true (by simpa using hflag) ?_ hw⟩
    · omega
    · apply mn_native_exec_within hiter c hniter depth
      have hm' : 1+(m+1) ≤ cost+2 := by omega
      have hmul := Nat.mul_le_mul_left c hm'
      omega

/-- A restoring counted scan needs one iteration reserve above final stock. -/
theorem scanP_within_final_stock {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Ψ : ℕ → Regs T A} {cost N c : ℕ} (hc : 1 ≤ c) (hnative : mnNativePushBound c p)
    (hp : IterStockSpec body p a t Ψ cost N) (j : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : j+(S.R a).length ≤ N) (hR : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k)
    {z : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (hex : Exec body (scanP a t p) (Host.mk v S) n z) (depth : ℕ) :
    ExecWithin body (fun d u => mnSize u+d ≤ mnSize z+depth+c*(cost+2)) depth
      (scanP a t p) (Host.mk v S) n z := by
  obtain ⟨vf,F,m,hmono,hw⟩ := scanP_loop_stock hat hc hnative hp depth (S.R a) j
    {v with flag := (S.R a).head?.isSome} S rfl hN hR rfl
  obtain ⟨v',hu,he⟩ := moveR_exec body t a hat.symm id vf F
  change mnSize (Host.mk v S) ≤ mnSize (Host.mk vf F) at hmono
  have hsize := mn_movedR_size a t hat vf v' F
  change mnSize (Host.mk v' {F with R := movedR F.R t a id (F.R t)}) = mnSize (Host.mk vf F) at hsize
  have hpeek := Exec.act (body := body) (peekR a) (Host.mk v S)
  rw [peekR_run] at hpeek
  have hpw := mn_native_exec_within hpeek 0 (by simp [mnNativePushBound,peekR,mnActPush]) depth
    (mnSize (Host.mk vf F)+depth+c*(cost+2)) (by omega)
  have hmove := Host.moveR_within t a id he depth (mnSize (Host.mk vf F)+depth+c*(cost+2)) (by omega)
  have hwhole := ExecWithin.seq hpw (.seq hw hmove)
  obtain ⟨hn,hz⟩ := hwhole.toExec.unique hex
  have hzsize : mnSize z = mnSize (Host.mk vf F) := by rw [←hz]; exact hsize
  rw [hzsize]
  simpa only [←hn,hz,scanP] using hwhole

end IntegerMultBounds.MathlibTM2.Node
