module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentBandControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectFoldedBand

/-! Generate the clipped controls, collect the band entries and release every control. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def preparedBandCollection : Pr P 151 Q A U := .seq residentBandControls collectColumnEntries

noncomputable def preparedBandCollectionCost {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band n : ℕ) : ℕ :=
  let W := 12*band+1
  residentBandControlsCost n band B.card+
    collectColumnEntriesCost B q V (n-W) (min B.card (n+W+1)-(n-W))

theorem preparedBandCollection_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hband : (S.R 124).length = band) (hrows : (S.R 116).length = B.card)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hfresh : ∀ k ∈ [(94 : Fin 151),106,135,136,137,138,139,140], S.R k = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedBandCollectionCost B q V band n ∧
      Exec body preparedBandCollection (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 0 []) 132
          (cstream A (2*q+8) ((foldedBandRows B (12*band+1) n).reverse.map C)++S.R 132))}) := by
  let W := 12*band+1
  obtain ⟨v₁,hu₁,he₁⟩ := residentBandControls_exec (body := body) n band B.card v S hindex hband hrows (by
    intro k hk
    exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks 151 A := {S with R := (Function.update (Function.update (Function.update S.R 0 [])
    137 (List.replicate (n-W) tick)) 138 (List.replicate (min B.card (n+W+1)-(n-W)) tick))}
  have hoff (k : Fin 151) (hk0 : k ≠ 0) (hk137 : k ≠ 137) (hk138 : k ≠ 138) : S₁.R k = S.R k := by
    simp [S₁,hk0,hk137,hk138]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := collectFoldedBand_exec (body := body) B q V W n hA hs hn C pageTail tail v₁ S₁
    (by simp [S₁]) (by simp [S₁]) (by simpa [S₁] using hwidth)
    (by simpa [S₁] using hpage) (by simpa [S₁] using hq) (by simpa [S₁] using hsource)
    (by simp [S₁])
    (by simpa [S₁] using hfresh 94 (by simp)) (by simpa [S₁] using hfresh 106 (by simp))
    (by simpa [S₁] using hfresh 135 (by simp)) (by simpa [S₁] using hfresh 136 (by simp))
    (by simpa [S₁] using hfresh 139 (by simp)) (by simpa [S₁] using hfresh 140 (by simp)) (by
      intro k hk1 hk7
      rw [hoff k (by omega) (by omega) (by omega)]
      exact hblank k hk1 hk7)
  refine ⟨v₂,residentBandControlsCost n band B.card+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk132 : k = 132 <;> by_cases hk137 : k = 137 <;>
    by_cases hk138 : k = 138 <;> simp [S₁,W,hk0,hk132,hk137,hk138,hfresh 137 (by simp),hfresh 138 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
