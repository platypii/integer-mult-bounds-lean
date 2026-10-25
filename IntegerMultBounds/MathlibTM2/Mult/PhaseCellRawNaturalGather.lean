module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders

/-! Gather the exact natural-group RHS from an ambient prefix on the owned
payload tape. The original ambient prefix and arbitrary borrowed suffix survive
below the newly gathered RHS; private copies and controls are released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def rawNaturalGather : Pr P 117 Q A U :=
  .seq generateRuntimeWidth (.seq (unaryProduct 97 94 10 6 7)
    (.seq (copyPrefix 10 110 92 6 7)
      (.seq (naturalGather 110 91 1 2 0 92 3 4 5 6 7 8 9 102 94)
        (clearWords [92, 10, 91, 94]))))

def rawNaturalGatherCost (q s : ℕ) : ℕ :=
  97*s*(2*q+8)+2*(2*q+8)+4*q+59

theorem rawNaturalGather_exec {s : ℕ} [NeZero s] (q t band L : ℕ) (hst : s < t)
    (hgroup : 0 < (naturalLengthGroup s t band L).length) (C : ZMod s → GaussianInt)
    (borrowed : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q) (hs : (S.R 97).length = s) (hL : (S.R 102).length = L)
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C) ++ borrowed)
    (hc : S.R 91 = naturalGatherControls A s t band L (2*q+8))
    (hblank : ∀ k : Fin 117, k.val < 11 → S.R k = [])
    (hfresh : ∀ k ∈ [(92 : Fin 117), 94, 104], S.R k = []) :
    let rhs := cstream A (2*q+8) ((List.range (naturalLengthGroup s t band L).length).flatMap
      (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawNaturalGatherCost q s ∧
      Exec body rawNaturalGather (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 110 (rhs ++ S.R 110)) 91 []) }) := by
  let w := 2*q+8
  let B := (naturalLengthGroup s t band L).length
  let E := cstream A w (chirpLine s C)
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C)))
  have hElength : E.length = s*w := by simp [E]
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 97) (b := 94) (dst := 10) (t₁ := 6) (t₂ := 7) (by decide) v₁ S₁
    (by simpa [S₁] using hblank 6 (by decide)) (by simpa [S₁] using hblank 7 (by decide))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 10 (List.replicate (s*w) tick) }
  have he₂' : Exec body (unaryProduct 97 94 10 6 7) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, hs, hblank 10 (by decide)] using he₂
  have hn₂' : n₂ ≤ s*(4*w+9)+4 := by simpa [S₁, hs] using hn₂
  obtain ⟨v₃, hu₃, he₃⟩ := copyPrefix_exec (body := body)
    (count := 10) (src := 110) (dst := 92) (saved := 6) (tmp := 7) (by decide)
    v₂ S₂ E borrowed (by simpa [S₂, S₁] using hsrc)
    (by simp [S₂, hElength]) (by simpa [S₂, S₁] using hblank 6 (by decide))
    (by simpa [S₂, S₁] using hblank 7 (by decide))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 92 E }
  have he₃' : Exec body (copyPrefix 10 110 92 6 7) (mk v₂ S₂) (10*(s*w)+10) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hElength, hfresh 92 (by simp)] using he₃
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := naturalGather_exec (body := body)
    (dst := 110) (control := 91) (savedControl := 1) (advance := 2) (window := 0) (src := 92)
    (acc := 3) (current := 4) (savedSource := 5) (buf := 6) (tmp := 7) (initialControl := 8)
    (initialSource := 9) (rowCount := 102) (wordR := 94) (by decide) t band L w C hgroup v₃ S₃
    (by simpa [S₃, S₂, S₁] using hc) (by simp [S₃, E])
    (by simpa [S₃, S₂, S₁] using hL) (by simp [S₃, S₂, S₁]) (by
      intro k hk
      have hlo : k.val < 10 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h92 : k ≠ (92 : Fin 117) := by intro he; subst k; norm_num at hlo
      have h10 : k ≠ (10 : Fin 117) := by intro he; subst k; norm_num at hlo
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hlo
      simpa [S₃, S₂, S₁, h92, h10, h94] using hblank k (by omega))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 110 (rhs ++ S₃.R 110) }
  have hn₄' : n₄ ≤ 66*s*w+29 := hn₄.trans (naturalGatherCost_le hst band L w hgroup (by omega))
  have hcontrolLength : (S.R 91).length = (originAdvances w 0 (naturalOrigins s t band L)).sum+B+1 := by
    rw [hc, ← originAdvances_natControls A s t band L w hgroup]
    simp [B]
    omega
  have hsum : (([(92 : Fin 117), 10, 91, 94]).map (fun k => (S₄.R k).length)).sum =
      2*(s*w)+(originAdvances w 0 (naturalOrigins s t band L)).sum+B+1+w := by
    simp [S₄, S₃, S₂, S₁, hElength, hcontrolLength]
    omega
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [(92 : Fin 117), 10, 91, 94] (by decide) v₄ S₄
  refine ⟨v₅, (4*q+5)+(n₂+((10*(s*w)+10)+(n₄+(2*(([(92 : Fin 117), 10, 91, 94]).map
    (fun k => (S₄.R k).length)).sum+9)))), hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · rw [hsum]
    have hvol := naturalOriginAdvances_volume s t band L w
    have hBL : B*L ≤ s := naturalGroup_volume_le hst band L
    have hLpos : 0 < L := ((mem_naturalLengthGroup s t band L _).mp
      (naturalGroupPhase_mem s t band L ⟨0, hgroup⟩)).2.1
    have hBs : B ≤ s := by nlinarith only [hBL, hLpos]
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s (show 1 ≤ w by omega)
    change _ ≤ 97*s*w+2*w+4*q+59
    nlinarith only [hn₂', hn₄', hvol, hBs, hsw]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h92 : k = 92
      · subst k; simp [hfresh 92 (by simp)]
      by_cases h10 : k = 10
      · subst k; simp [hblank 10 (by decide)]
      by_cases h91 : k = 91
      · subst k; simp
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      simp [S₄, S₃, S₂, S₁, h92, h10, h91, h94, Function.update_apply, rhs, B, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
