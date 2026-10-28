module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellApplyRecoveryWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardMaskHost

/-! Compose the two computed windows into the exact recovery guard. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def recoveryInteriorSymbols (boundary : Bool) (A s t B a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun k => if haloInteriorAt s t B a b k then
    pairSym A boundary boundary else pairSym A false false)

theorem recoveryWindows_symbols (boundary : Bool) (A s t B a b : ℕ) (hb : b ≤ s) :
    windowWord id (fun _ => pairSym A false false)
      (recoveryWindowLower true s B a) (recoveryWindowUpper true s B b)
      (windowWord id (fun _ => pairSym A true true)
        (recoveryWindowLower false s B a) (recoveryWindowUpper false s B b)
        (recoveryInteriorSymbols boundary A s t B a b)) = recoveryGuardMaskSymbols boundary A s t B a b := by
  unfold recoveryInteriorSymbols
  rw [windowWord_map_range,windowWord_map_range]
  unfold recoveryGuardMaskSymbols
  apply List.map_congr_left
  intro k hk
  have he := recoveryWindows_spec boundary s t B a b k hb (List.mem_range.mp hk)
  have hbase : (if haloInteriorAt s t B a b k then pairSym A boundary boundary else pairSym A false false) =
      pairSym A (boundary && haloInteriorAt s t B a b k) (boundary && haloInteriorAt s t B a b k) := by
    cases boundary <;> cases haloInteriorAt s t B a b k <;> rfl
  rw [hbase]
  dsimp only [id_eq]
  simp only [recoveryGuardMaskAt]
  rw [← he]
  by_cases ha : recoveryWindowLower true s B a ≤ k ∧ k < recoveryWindowUpper true s B b <;>
    by_cases hx : recoveryWindowLower false s B a ≤ k ∧ k < recoveryWindowUpper false s B b <;>
    simp [ha,hx,recoveryGuardMaskAt]

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def recoveryWindowMask : Pr P 117 Q A U :=
  .seq (applyRecoveryWindow false id (fun _ => pairSym A true true))
    (applyRecoveryWindow true id (fun _ => pairSym A false false))

def recoveryWindowMaskCost (W s t B a b : ℕ) : ℕ :=
  applyRecoveryWindowCost false W s t B a b+applyRecoveryWindowCost true W s t B a b

theorem recoveryWindowMask_exec {W s t B a b : ℕ} (boundary : Bool)
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hwide : 8*(t+1)^2+2*B+8 < 2^W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hB : (S.R 100).length = B) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hW : (S.R 115).length = W) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (hsrc : S.R 109 = recoveryInteriorSymbols boundary A s t B a b++tail) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryWindowMaskCost W s t B a b ∧
      Exec body recoveryWindowMask (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (recoveryGuardMaskSymbols boundary A s t B a b++tail)}) := by
  let xs := recoveryInteriorSymbols boundary A s t B a b
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := applyRecoveryWindow_exec (body := body) false id (fun _ => pairSym A true true)
    hst has hbs hwide v S xs tail hs ht hB ha hb hW h106 h108 hblank (by simp [xs,recoveryInteriorSymbols]) hsrc
  let result := windowWord id (fun _ => pairSym A true true)
    (recoveryWindowLower false s B a) (recoveryWindowUpper false s B b) xs
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 109 (result++tail)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := applyRecoveryWindow_exec (body := body) true id (fun _ => pairSym A false false)
    hst has hbs hwide v₁ S₁ result tail (by simpa [S₁] using hs) (by simpa [S₁] using ht)
    (by simpa [S₁] using hB) (by simpa [S₁] using ha) (by simpa [S₁] using hb)
    (by simpa [S₁] using hW) (by simpa [S₁] using h106) (by simpa [S₁] using h108) (by
      intro r hr
      have hr109 : r ≠ (109 : Fin 117) := by intro he; subst r; norm_num at hr
      simpa [S₁,hr109] using hblank r hr)
    (by simp [result,xs,windowWord_length,recoveryInteriorSymbols]) (by simp [S₁])
  have hm := recoveryWindows_symbols boundary A s t B a b hbs
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by dsimp [recoveryWindowMaskCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  simp [S₁,result,xs,hm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
