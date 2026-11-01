module

public import IntegerMultBounds.MathlibTM2.Host.CountedStepStock

/-! Structural counted loops over arbitrary schedules. A stack invariant carries
semantic facts; actual body traces supply the per-entry cost and stock bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U α : Type} {body : P → Pr P T Q A U}

theorem countedLoop_body_exec_within (count : Fin T) (p : Pr P T Q A U)
    (Inv : List α → Stacks T A → Prop) (cost workspace : α → ℕ) (depth : ℕ)
    (hcount : ∀ xs S, Inv xs S → S.R count = List.replicate xs.length tick)
    (hstep : ∀ x xs (v : HS T Q A U) S, Inv (x::xs) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost x ∧ Inv xs F ∧
        ExecWithin body (fun d z => mnSize z+d ≤
          mnSize (mk v {S with R := Function.update S.R count (List.replicate xs.length tick)})+depth+workspace x)
          depth p (mk v {S with R := Function.update S.R count (List.replicate xs.length tick)}) n (mk v' F))
    (xs : List α) (v : HS T Q A U) (S : Stacks T A) (hInv : Inv xs S)
    (hflag : v.flag = xs.head?.isSome) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (xs.map (fun x => cost x+3)).sum+1 ∧ Inv [] F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(xs.map workspace).sum)
        depth (.loop (·.flag) (countedStep count p)) (mk v S) n (mk v' F) := by
  induction xs generalizing v S with
  | nil =>
    refine ⟨v,S,1,rfl,by simp,hInv,?_⟩
    exact .loop_false (by simpa using hflag) (by simp)
  | cons x xs ih =>
    obtain ⟨v₁,M,n₁,hu₁,hn₁,hInv₁,he₁⟩ := hstep x xs v S hInv
    have hc : S.R count = tick::List.replicate xs.length tick := by
      simpa only [List.length_cons,List.replicate_succ] using hcount (x::xs) S hInv
    have he₁' := countedStep_exec_within count p v v₁ S M tick (List.replicate xs.length tick)
      hc (hcount xs M hInv₁) n₁ depth (workspace x) he₁
    let v₂ := {v₁ with flag := (List.replicate xs.length tick).head?.isSome}
    obtain ⟨v₃,F,n₂,hu₂,hn₂,hInv₂,he₂⟩ := ih v₂ M hInv₁
      (by change (List.replicate xs.length tick).head?.isSome = xs.head?.isSome; cases xs <;> simp)
    have hsize := he₁'.final
    change mnSize (mk v₂ M)+depth ≤ mnSize (mk v S)+depth+workspace x at hsize
    refine ⟨v₃,F,(n₁+2)+n₂+1,hu₂.trans hu₁,?_,hInv₂,?_⟩
    · simp only [List.map_cons,List.sum_cons] at hn₂ ⊢
      omega
    · apply ExecWithin.loop_true (by simpa using hflag)
      · apply he₁'.mono
        intro d z hz
        simp only [List.map_cons,List.sum_cons]
        omega
      · apply he₂.mono
        intro d z hz
        simp only [List.map_cons,List.sum_cons]
        omega

end IntegerMultBounds.MathlibTM2.Host
