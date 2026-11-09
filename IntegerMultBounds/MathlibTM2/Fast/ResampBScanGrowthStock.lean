module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock

/-! Counted scans charge retained growth per iteration and share one transient reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {rg : R → Fin T} {ι : Fin 64 → Fin T}

theorem rsb_scanIf_loop_within_growth (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {ra rt : R}
    (hat : ra ≠ rt) (c : Fin (A + 4) → Bool) (p q : Pr P T Q A U) (l : List (Fin (A + 4)))
    (Ψ : ℕ → R → List (Fin (A + 4))) (bp : ℕ → ℕ) (reserve growth : ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (if c l[j] then p else q)
      (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j + 1)) ra X rt Y) (bp j) reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+growth) :
    ∀ n j, j + n = l.length → ∀ v S, RsbClean ι S →
      RsbHolds rg S (rsbUpd2 (Ψ j) ra (l.drop j) rt (l.take j).reverse) →
      v.flag = (l.drop j).head?.isSome →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ ∑ i ∈ Finset.range n, (bp (j + i) + 4) + 1 ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(n*growth+reserve))
          depth (.loop (·.flag) (.seq (.act (popPush (rg ra) (rg rt)))
          (.seq (.cond (fun v => c (v.sym.getD blank)) p q) (.act (peekR (rg ra))))))
          (mk v S) m (mk v' S')) ∧
        RsbHolds rg S' (rsbUpd2 (Ψ l.length) ra [] rt l.reverse) ∧ RsbFr rg S S' ∧ mnSize (mk v' S') ≤ mnSize (mk v S)+n*growth := by
  intro n
  induction n with
  | zero =>
    intro j hj v S _ hS hfl
    have hd : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have hjl : j = l.length := by omega
    subst hjl
    refine ⟨v, S, 1, rfl, by simp, (fun depth => .loop_false (by simpa [hd] using hfl) (by omega)), ?_, RsbFr.refl S,by omega⟩
    simpa [List.take_length] using hS
  | succ n ih =>
    intro j hj v S hc hS hfl
    have hg : (n+1)*growth = n*growth+growth := by rw [Nat.add_mul]; simp
    have hjl : j < l.length := by omega
    have hdrop : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have htake : (l.take (j + 1)).reverse = l[j] :: (l.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl]; simp
    have hSa : S.R (rg ra) = l[j] :: l.drop (j + 1) := by
      rw [hS ra, ← hdrop]; simp [Function.update_of_ne hat]
    have hSt : S.R (rg rt) = (l.take j).reverse := by rw [hS rt]; simp
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Stacks T A, S₁ = { S with R := (Function.update (Function.update
        S.R (rg ra) (l.drop (j + 1))) (rg rt) (l[j] :: S.R (rg rt))) } := ⟨_, rfl⟩
    have hrun : (popPush (rg ra) (rg rt) : Act T Q A U).run (mk v S) =
        mk { v with sym := some l[j] } S₁ := by
      rw [hS₁]
      simp [popPush, Action.run, hSa, update_rt, Function.update_of_ne (hrg.ne hat).symm,
        List.getElem?_eq_getElem hjl]
    have hS₁h : RsbHolds rg S₁ (rsbUpd2 (Ψ j) ra (l.drop (j + 1)) rt (l.take (j + 1)).reverse) := by
      intro r
      rw [hS₁]
      dsimp only
      rw [rsb_holds_upd hrg (rsb_holds_upd hrg hS ra _) rt, hSt, htake]
      by_cases h1 : r = rt
      · subst h1; simp
      by_cases h2 : r = ra
      · subst h2; simp [h1]
      simp [h1, h2]
    have hfr₁ : RsbFr rg S S₁ := ⟨by rw [hS₁], by rw [hS₁], by rw [hS₁], fun k hk => by
      rw [hS₁]; dsimp only; rw [rsb_upd_off _ _ _ hk, rsb_upd_off _ _ _ hk]⟩
    have hc₁ : RsbClean ι S₁ := hc.of_fr hdisj hfr₁
    obtain ⟨v₂, S₂, m₂, hu₂, hm₂, hS₂, hfr₂, he₂⟩ :=
      hbody j hjl _ _ { v with sym := some l[j] } S₁ hc₁ hS₁h
    have hpop : mnSize (mk {v with sym := some l[j]} S₁) ≤ mnSize (mk v S) := by
      have hh := mn_pop_one_push (mk v S) (.rt (rg ra)) (fun v o => {v with sym := o})
        (.push (.rt (rg rt)) (fun v => v.sym.getD blank) .done) (by simp [mnActPush])
        (by change S.R (rg ra) ≠ []; rw [hSa]; simp; exact hjl)
      change mnSize ((popPush (rg ra) (rg rt)).run (mk v S)) ≤ mnSize (mk v S) at hh
      rw [hrun] at hh
      exact hh
    have hsize₂ := hstock j hjl _ _ {v with sym := some l[j]} v₂ S₁ S₂ hS₁h hS₂ hfr₂
    have hS₂a : S₂.R (rg ra) = l.drop (j + 1) := by
      rw [hS₂ ra]; simp only [rsbUpd2, Function.update_of_ne hat, Function.update_self]
    obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hS₃, hfr₃, hsize₃⟩ := ih (j + 1) (by omega)
      { v₂ with flag := (S₂.R (rg ra)).head?.isSome } S₂ (hc₁.of_fr hdisj hfr₂) hS₂
      (by rw [hS₂a])
    refine ⟨v₃, S₃, 1 + (m₂ + 1 + 1) + m₃ + 1, by rw [hu₃, ← hu₂], ?time,
      ?trace, hS₃, hfr₁.trans (hfr₂.trans hfr₃), ?stock⟩
    case trace =>
      intro depth
      let Inv : ℕ → Store (HΓ (T := T) A) (HS T Q A U) → Prop := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+((n+1)*growth+reserve)
      have hbody₂ : ExecWithin body Inv depth (if c l[j] then p else q)
          (mk {v with sym := some l[j]} S₁) m₂ (mk v₂ S₂) :=
        (he₂ depth).mono (by intro d z hz; dsimp only [Inv]; omega)
      have hcond : ExecWithin body Inv depth (.cond (fun v => c (v.sym.getD blank)) p q)
          (mk {v with sym := some l[j]} S₁) (m₂+1) (mk v₂ S₂) := by
        by_cases hcj : c l[j] = true
        · rw [ite_eq_left hcj] at hbody₂
          exact .cond_true (by simpa using hcj) hbody₂
        · rw [ite_eq_right hcj] at hbody₂
          exact .cond_false (by simpa using hcj) hbody₂
      have hpeek := mn_native_exec_within (rsb_peekR_exec (body := body) (rg ra) v₂ S₂) 0
        (by simp [peekR,mnNativePushBound,mnActPush]) depth
        (mnSize (mk v S)+depth+((n+1)*growth+reserve)) (by simp only [Nat.zero_mul,Nat.add_zero]; omega)
      refine .loop_true (by show v.flag = true; rw [hfl,hdrop]; rfl)
        (.seq ?_ (.seq hcond hpeek)) ?_
      · have hh : ExecWithin body Inv depth (.act (popPush (rg ra) (rg rt)))
            (mk v S) 1 ((popPush (rg ra) (rg rt)).run (mk v S)) :=
          .act _ _ (by dsimp only [Inv]; omega) (by rw [hrun]; dsimp only [Inv]; omega)
        rw [hrun] at hh
        exact hh
      · exact (he₃ depth).mono (by
          intro d z hz
          have hv : mnSize (mk {v₂ with flag := (S₂.R (rg ra)).head?.isSome} S₂) = mnSize (mk v₂ S₂) := rfl
          rw [hv] at hz
          omega)
    case stock =>
      have hv : mnSize (mk {v₂ with flag := (S₂.R (rg ra)).head?.isSome} S₂) = mnSize (mk v₂ S₂) := rfl
      rw [hv] at hsize₃
      omega
    case time =>
      rw [Finset.sum_range_succ']
      have : ∑ i ∈ Finset.range n, (bp (j + 1 + i) + 4) =
          ∑ i ∈ Finset.range n, (bp (j + (i + 1)) + 4) :=
        Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
      rw [← this]
      simp only [Nat.add_zero]
      omega


theorem rsb_scanIf_runs_within_growth (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {ra rt : R} (hat : ra ≠ rt) (c : Fin (A+4) → Bool) (p q : Pr P T Q A U)
    (l : List (Fin (A+4))) (Ψ : ℕ → R → List (Fin (A+4))) (bp : ℕ → ℕ) (reserve growth : ℕ)
    (hbody : ∀ j (hj : j < l.length) X Y,
      RsbRunsWithin (body := body) (rg := rg) (ι := ι) (if c l[j] then p else q)
        (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j+1)) ra X rt Y) (bp j) reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+growth) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (rsbScanIf (rg ra) (rg rt) c p q) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt [])
      (∑ i ∈ Finset.range l.length, (bp i+4)+2*l.length+4) (l.length*growth+reserve) := by
  intro v S hc hS
  have hSa : S.R (rg ra) = l := by rw [hS ra]; simp [Function.update_of_ne hat]
  obtain ⟨v₁,F,m,hu₁,hm,he₁,hh₁,hf₁,hs₁⟩ := rsb_scanIf_loop_within_growth hrg hdisj hat c p q l Ψ bp reserve growth
    hbody hstock l.length 0 (by simp) {v with flag := (S.R (rg ra)).head?.isSome} S hc
    (by simpa using hS) (by rw [hSa]; simp)
  have hmove := rsb_moveR_runs (body := body) (ι := ι) hrg (a := rt) (b := ra) hat.symm
    (rsbUpd2 (Ψ l.length) ra [] rt l.reverse)
  obtain ⟨v₂,G,n,hu₂,hn,he₂,hh₂,hf₂⟩ := hmove v₁ F (hc.of_fr hdisj hf₁) hh₁
  have hfinal : RsbHolds rg G (rsbUpd2 (Ψ l.length) ra l rt []) := by
    have heq : Function.update (Function.update (rsbUpd2 (Ψ l.length) ra [] rt l.reverse) rt []) ra
        (((rsbUpd2 (Ψ l.length) ra [] rt l.reverse) rt).reverse++
          (rsbUpd2 (Ψ l.length) ra [] rt l.reverse) ra) = rsbUpd2 (Ψ l.length) ra l rt [] := by
      funext r
      by_cases hr : r = ra
      · subst r; simp [Function.update_of_ne hat]
      by_cases ht : r = rt
      · subst r; simp [hr]
      simp [hr,ht]
    rw [heq] at hh₂
    exact hh₂
  refine ⟨v₂,G,1+m+n,hu₂.trans hu₁,?_,hfinal,hf₁.trans hf₂,?_⟩
  · simp only [Nat.zero_add] at hm
    simp only [rsbUpd2,Function.update_self,List.length_reverse] at hn
    omega
  · intro depth
    have hp := mn_native_exec_within (rsb_peekR_exec (body := body) (rg ra) v S) 0
      (by simp [peekR,mnNativePushBound,mnActPush]) depth
      (mnSize (mk v S)+depth+(l.length*growth+reserve)) (by omega)
    have ht := he₁ depth
    have hm := moveR_within _ _ _ he₂ depth (mnSize (mk v S)+depth+(l.length*growth+reserve)) ht.final
    exact .seq (.seq hp ht) hm

/-- Counted repetitions retain one common reserve, independent of their length. -/
theorem rsb_rep_runs_within_growth (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {ra rt : R} (hat : ra ≠ rt) (p : Pr P T Q A U) (l : List (Fin (A+4)))
    (Ψ : ℕ → R → List (Fin (A+4))) (time reserve growth : ℕ)
    (hbody : ∀ j < l.length, ∀ X Y,
      RsbRunsWithin (body := body) (rg := rg) (ι := ι) p
        (rsbUpd2 (Ψ j) ra X rt Y) (rsbUpd2 (Ψ (j+1)) ra X rt Y) time reserve)
    (hstock : ∀ j < l.length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) ra X rt Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) ra X rt Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+growth) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι)
      (rsbRep (rg ra) (rg rt) p) (rsbUpd2 (Ψ 0) ra l rt [])
      (rsbUpd2 (Ψ l.length) ra l rt []) (l.length*(time+6)+4) (l.length*growth+reserve) := by
  refine (rsb_scanIf_runs_within_growth hrg hdisj hat (fun _ => true) p p l Ψ (fun _ => time)
    reserve growth (fun j hj X Y => by simpa using hbody j hj X Y) hstock).mono ?_ (le_refl _)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring_nf
  omega


end IntegerMultBounds.MathlibTM2.Fast
