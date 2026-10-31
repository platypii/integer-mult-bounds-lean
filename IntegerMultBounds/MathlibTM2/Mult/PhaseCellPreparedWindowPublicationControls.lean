module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowPublicationControls

/-! Generate a shared scatter page from retained binary origins. The existing
advance generator and structural gap converter restore all borrowed metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A s L : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def preparedWindowPublicationControls : Pr P 117 Q A U :=
  .seq preparedNaturalAdvanceControls
    (.seq (windowPublicationControls 116 88 91 89 90 103 104 105 92 106 107) (uclear 91))

/-- Only the scatter destination changes. In particular, the origin packet,
count, window width and any existing destination suffix are restored. -/
theorem preparedWindowPublicationControls_exec (V w : ℕ)
    (windows : PublicationWindows s L) (hw1 : 1 ≤ w)
    (hwV : w < 2^V) (hsV : s < 2^V) (hvolume : s*w < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = windows.origins.flatMap (binSyms V)++suffix)
    (hcount : S.R 116 = List.replicate windows.origins.length tick)
    (hwindow : (S.R 103).length = L*w)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,104,105,106,107], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedOriginAdvanceCost V s w windows.origins.length+37*s*w+2*windows.origins.length+29 ∧
      Exec body preparedWindowPublicationControls (mk v S) n
        (mk v' {S with R := (Function.update S.R 92
          (gatherControls A (windows.gaps w)++S.R 92))}) := by
  have hsorted : windows.origins.Pairwise (· ≤ ·) :=
    windows.disjoint.imp (fun h => by omega)
  have hle : ∀ p ∈ windows.origins, p ≤ s := by
    intro p hp
    have := windows.fits p hp
    omega
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hi,ho,hl,hr⟩ :=
    preparedOriginAdvanceControls_exec (body := body) V w s windows.origins
      hwV hsV hvolume hsorted hle v S suffix hV hw hsrc hcount hblank
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  have hcontrol : M.R 91 = gatherControls A (originAdvances w 0 windows.origins++[0]) := by
    simp [hr,hfresh 91 (by simp)]
  have hoff (k : Fin 117) (hk : k ≠ 91) : M.R k = S.R k := by simp [hr,hk]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := windowPublicationControls_exec (body := body)
    116 88 91 89 90 103 104 105 92 106 107 (by decide) windows w hw1 [] v₁ M
    (by rw [hoff 116 (by decide)]; exact hcount)
    (by simpa using hcontrol)
    (by rw [hoff 103 (by decide)]; exact hwindow)
    (by
      intro k hk
      have hk91 : k ≠ 91 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hoff k hk91]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let N : Stacks 117 A := {M with R := (Function.update M.R 92
    (gatherControls A (windows.gaps w)++M.R 92))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 91 v₂ N
  have hlen : (N.R 91).length ≤ s*w+windows.origins.length+1 := by
    have hsum : (originAdvances w 0 windows.origins).sum ≤ s*w := by
      simpa using originAdvances_sum_le w 0 s windows.origins
        (List.pairwise_cons.mpr ⟨by simp,hsorted⟩) (Nat.zero_le _) hle
    simp only [N,Function.update_of_ne (by decide : (91 : Fin 117) ≠ 92),hcontrol,
      length_gatherControls,List.sum_append,List.sum_singleton,List.length_append,
      List.length_singleton,originAdvances_length]
    omega
  refine ⟨v₃,n₁+(n₂+(2*(N.R 91).length+2)),hu₃.trans (hu₂.trans hu₁),by nlinarith only [hn₁,hn₂,hlen],?_⟩
  have hex := Exec.seq he₁ (Exec.seq he₂ he₃)
  have hfinal : {N with R := Function.update N.R 91 []} =
      {S with R := Function.update S.R 92 (gatherControls A (windows.gaps w)++S.R 92)} := by
    ext1
    · exact hi
    · exact ho
    · exact hl
    · funext k
      by_cases h91 : k = 91
      · subst k; simp [hfresh 91 (by simp)]
      by_cases h92 : k = 92
      · subst k; simp [N,hoff 92 (by decide)]
      simp [N,h91,h92,hoff k h91]
  simpa only [preparedWindowPublicationControls,←hfinal] using hex

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
