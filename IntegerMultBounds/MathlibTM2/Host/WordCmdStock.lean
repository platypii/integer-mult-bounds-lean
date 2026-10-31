module

public import IntegerMultBounds.MathlibTM2.Host.WordCmd
public import IntegerMultBounds.MathlibTM2.StackResources

/-! A word loop retains its boundary stock and one body scratch allowance.
The body is compiled structurally and its actual word execution is reused. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.WordCmd
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage (Cmd WTape)
variable {t T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem native_of_noCalls {K : Type} {Γ : K → Type} {σ P : Type}
    {p : Prog P Γ σ} {c : ℕ} (hn : NoCalls p) (hp : mnProgPush p ≤ c) : mnNativePushBound c p := by
  induction p with
  | act a => exact hp
  | seq p q ihp ihq => exact ⟨ihp hn.1 (max_le_iff.mp hp).1,ihq hn.2 (max_le_iff.mp hp).2⟩
  | cond f p q ihp ihq => exact ⟨ihp hn.1 (max_le_iff.mp hp).1,ihq hn.2 (max_le_iff.mp hp).2⟩
  | loop f p ih => exact ih hn hp
  | call f => exact hn.elim

/-- No controller expansion is needed to certify its largest atomic push. -/
theorem tcompile_native (ι : Fin t → Fin T) (c : Cmd t) :
    mnNativePushBound (mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c))
      (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c) := native_of_noCalls (tcompile_noCalls ι c) le_rfl

/-- Use time as stock only for one bounded compiled word operation. -/
theorem tcompile_runs_within {ι : Fin t → Fin T} (hι : Function.Injective ι) {c : Cmd t}
    {σ : Fin t → WTape} {Post : (Fin t → WTape) → Prop} {budget : ℕ}
    (h : Schoenhage.Runs c σ Post budget) (hQ : cmdStates c ≤ Q)
    (v : HS T Q A U) (S : Stacks T A) (depth : ℕ) :
    ∃ σ', Post σ' ∧ ∃ v' steps, v'.user = v.user ∧ steps ≤ 3*(budget+1) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v (place S ι σ))+depth+
        mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c)*(3*(budget+1)))
        depth (tcompile ι c) (mk v (place S ι σ)) steps (mk v' (place S ι σ')) := by
  obtain ⟨σ',hpost,v',steps,hu,hn,he⟩ := tcompile_runs (body := body) hι h hQ v S
  exact ⟨σ',hpost,v',steps,hu,hn,mn_native_exec_within he _ (tcompile_native ι c) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) _)⟩

/-- A loop over a finite sequence of actual word banks pays body scratch once.
Boundary stock may include retained sources, completed outputs and spectators. -/
theorem tcompile_loop_runs_within {ι : Fin t → Fin T} (hι : Function.Injective ι)
    (i : Fin t) (c : Cmd t) (N budget H : ℕ) (σ : ℕ → Fin t → WTape)
    (hne : ∀ k < N, (σ k i).right ≠ []) (hend : (σ N i).right = [])
    (hstep : ∀ k < N, Schoenhage.Runs c (σ k) (· = σ (k+1)) budget)
    (hQ : cmdStates c ≤ Q) (S : Stacks T A)
    (hstock : ∀ k ≤ N, ∀ v : HS T Q A U, mnSize (mk v (place S ι (σ k))) ≤ H)
    (v : HS T Q A U) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ N*(3*(budget+1)+2)+2 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ H+depth+
        mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c)*(3*(budget+1)))
        depth (tcompile ι (.loop i c)) (mk v (place S ι (σ 0))) steps
          (mk v' (place S ι (σ N))) := by
  let bound := H+depth+mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι c)*(3*(budget+1))
  have hloop : ∀ (K : ℕ) (τ : ℕ → Fin t → WTape),
      (∀ k < K, (τ k i).right ≠ []) → (τ K i).right = [] →
      (∀ k < K, Schoenhage.Runs c (τ k) (· = τ (k+1)) budget) →
      (∀ k ≤ K, ∀ v : HS T Q A U, mnSize (mk v (place S ι (τ k))) ≤ H) →
      ∀ v : HS T Q A U, v.flag = ((place S ι (τ 0)).R (ι i)).head?.isSome →
      ∃ v' steps, v'.user = v.user ∧ steps ≤ K*(3*(budget+1)+2)+1 ∧
        ExecWithin body (fun d z => mnSize z+d ≤ bound) depth
          (.loop (·.flag) (.seq (tcompile ι c) (.act (peekW (ι i)))))
          (mk v (place S ι (τ 0))) steps (mk v' (place S ι (τ K))) := by
    intro K
    induction K with
    | zero =>
      intro τ _ hend _ hs v hf
      have hv : v.flag = false := by rw [hf,place_R_at hι,hend]; rfl
      refine ⟨v,1,rfl,by omega,.loop_false hv ?_⟩
      have hh := hs 0 (by omega) v
      change mnSize (mk v (place S ι (τ 0)))+depth ≤ bound
      dsimp only [bound]
      omega
    | succ K ih =>
      intro τ hne hend hstep hs v hf
      have hv : v.flag = true := by
        rw [hf,place_R_at hι,cells_head_isSome]
        simpa using hne 0 (by omega)
      obtain ⟨τ',hτ',v₁,m,hu₁,hm,ht⟩ := tcompile_runs_within (body := body) hι
        (hstep 0 (by omega)) hQ v S depth
      subst τ'
      have ht' : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth
          (tcompile ι c) (mk v (place S ι (τ 0))) m (mk v₁ (place S ι (τ 1))) := by
        apply ht.mono
        intro d z hz
        have hh := hs 0 (by omega) v
        dsimp only [bound]
        omega
      let v₂ := {v₁ with flag := ((place S ι (τ 1)).R (ι i)).head?.isSome, sym := ((place S ι (τ 1)).R (ι i)).head?}
      have hepeek : Exec body (.act (peekW (ι i))) (mk v₁ (place S ι (τ 1))) 1
          (mk v₂ (place S ι (τ 1))) := by
        simpa only [peekW_run] using Exec.act (body := body) (peekW (ι i)) (mk v₁ (place S ι (τ 1)))
      have htpeek := mn_native_exec_within hepeek 0
        (by simp [peekW,mnNativePushBound,mnActPush]) depth bound (by
          have hh := hs 1 (by omega) v₁
          dsimp only [bound]
          omega)
      obtain ⟨v',n,hu',hn,ht'loop⟩ := ih (fun k => τ (k+1))
        (fun k hk => hne (k+1) (by omega)) hend (fun k hk => hstep (k+1) (by omega))
        (fun k hk => hs (k+1) (by omega)) v₂ rfl
      exact ⟨v',m+1+n+1,hu'.trans hu₁,by rw [Nat.add_mul,Nat.one_mul]; omega,
        .loop_true hv (.seq ht' htpeek) ht'loop⟩
  let v₀ := {v with flag := ((place S ι (σ 0)).R (ι i)).head?.isSome, sym := ((place S ι (σ 0)).R (ι i)).head?}
  obtain ⟨v',n,hu,hn,ht⟩ := hloop N σ hne hend hstep hstock v₀ rfl
  have hepeek : Exec body (.act (peekW (ι i))) (mk v (place S ι (σ 0))) 1
      (mk v₀ (place S ι (σ 0))) := by
    simpa only [peekW_run] using Exec.act (body := body) (peekW (ι i)) (mk v (place S ι (σ 0)))
  have htpeek := mn_native_exec_within hepeek 0
    (by simp [peekW,mnNativePushBound,mnActPush]) depth bound (by
      have hh := hstock 0 (Nat.zero_le _) v
      dsimp only [bound]
      omega)
  exact ⟨v',1+n,hu,by omega,.seq htpeek ht⟩

end IntegerMultBounds.MathlibTM2.Host.WordCmd
