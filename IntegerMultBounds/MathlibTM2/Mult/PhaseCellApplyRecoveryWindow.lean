module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryWindowFromHeaders
public import IntegerMultBounds.MathlibTM2.Host.WindowStream

/-! Compute and apply either shifted recovery window, restoring counters and scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def applyRecoveryWindow (ambient : Bool) (inside outside : Fin (A+4) → Fin (A+4)) : Pr P 117 Q A U :=
  .seq (recoveryWindowFromHeaders ambient)
    (.seq (windowScan 108 106 109 22 97 23 inside outside) (moveR 22 109 id))

def applyRecoveryWindowCost (ambient : Bool) (W s t B a b : ℕ) : ℕ :=
  recoveryWindowFromHeadersCost ambient W s t B a b+6*s+6

theorem applyRecoveryWindow_exec {W s t B a b : ℕ} (ambient : Bool)
    (inside outside : Fin (A+4) → Fin (A+4))
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hwide : 8*(t+1)^2+2*B+8 < 2^W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (xs tail : List (Fin (A+4)))
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hB : (S.R 100).length = B) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hW : (S.R 115).length = W) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) (hxs : xs.length = s) (hsrc : S.R 109 = xs++tail) :
    ∃ v' n, v'.user = v.user ∧ n ≤ applyRecoveryWindowCost ambient W s t B a b ∧
      Exec body (applyRecoveryWindow ambient inside outside) (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          (windowWord inside outside (recoveryWindowLower ambient s B a)
            (recoveryWindowUpper ambient s B b) xs++tail))}) := by
  let lo := recoveryWindowLower ambient s B a
  let hi := recoveryWindowUpper ambient s B b
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := recoveryWindowFromHeaders_exec (body := body)
    ambient hst has hbs hwide v S hs ht hB ha hb hW h106 h108 hblank
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 108
    (List.replicate lo tick)) 106 (List.replicate hi tick))}
  have hbounds := recoveryWindow_bounds ambient s B a b has
  obtain ⟨v₂,hu₂,he₂⟩ := windowScan_exec body
    (show [(108 : Fin 117),106,109,22,97,23].Nodup by decide) inside outside v₁ S₁ xs tail lo hi
    (by simpa [S₁,hxs] using hs) (by simpa [hxs] using hbounds.1) (by simpa [hxs] using hbounds.2)
    (by simp [S₁]) (by simp [S₁]) (by simpa [S₁] using hsrc)
    (by simpa [S₁] using hblank 23 (by decide))
  let result := windowWord inside outside lo hi xs
  let S₂ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 109 tail) 22 result.reverse)}
  have he₂' : Exec body (windowScan 108 106 109 22 97 23 inside outside)
      (mk v₁ S₁) (4*s+4) (mk v₂ S₂) := by
    apply he₂.cast (by rw [hxs])
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all [result]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 22 109 (by decide) id v₂ S₂
  refine ⟨v₃,n₁+((4*s+4)+(2*s+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · dsimp only [applyRecoveryWindowCost]; omega
  · simp [S₂,result,windowWord_length,hxs]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,movedR,Function.update_apply,List.map_id,List.reverse_reverse]
    split_ifs <;> simp_all [result,lo,hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
