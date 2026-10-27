module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyResidentEntry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! Select a folded boundary row and retain its computed column entry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def selectedColumnEntry : Pr P 151 Q A U :=
  .seq selectResidentCoordinate (.seq copyResidentEntry (uclear 139))

def selectedColumnEntryCost (q V n x : ℕ) : ℕ :=
  (n*(12*V+11)+27*V+6*x+36)+(copyResidentEntryCost q x+(2*x+2))

theorem selectedColumnEntry_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h94 : S.R 94 = []) (h106 : S.R 106 = []) (h135 : S.R 135 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    let i := bFoldAt s B n
    ∃ v' m, v'.user = v.user ∧ m ≤ selectedColumnEntryCost q V n i.val ∧
      Exec body selectedColumnEntry (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 0 []) 132
          (csyms A (2*q+8) (C i)++S.R 132))}) ∧
      i ∈ B ∧ bFoldPos s B i = n ∧
      (value q (decodeWord ((csyms A (2*q+8) (C i)++S.R 132).take (2*q+8)))).re =
        publishedCellRead q (2*q+8) (0 : ZMod s) (S.R 110) i := by
  dsimp only
  let i := bFoldAt s B n
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hi,hpos⟩ := selectResidentCoordinate_exec (body := body)
    B V n hA hs hn pageTail v S hindex hwidth hpage h106 h139 hblank
  let S₀ : Stacks 151 A := {S with R := Function.update S.R 0 []}
  let S₁ : Stacks 151 A := {S₀ with R := Function.update S₀.R 139 (List.replicate i.val tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := copyResidentEntry_exec (body := body) q i.val (chirpLine s C)
    (by simpa using i.val_lt) tail v₁ S₁ (by simpa [S₁,S₀] using hq)
    (by simp [S₁]) (by simpa [S₁,S₀] using hsource)
    (by simpa [S₁,S₀] using h94) (by simpa [S₁,S₀] using h135) (by
      intro r hr1 hr7
      have hr0 : r ≠ 0 := by omega
      have hr139 : r ≠ 139 := by omega
      simpa [S₁,S₀,hr0,hr139] using hblank r hr1 hr7)
  have hword : (chirpLine s C)[i.val]'(by simpa using i.val_lt) = C i := by
    simp [chirpLine]
  let output := csyms A (2*q+8) (C i)++S.R 132
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 132 output}
  have he₂' : Exec body copyResidentEntry (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [hword,S₂,S₁,S₀,output] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 139 v₂ S₂
  have hlen : (S₂.R 139).length = i.val := by simp [S₂,S₁]
  have hread : (value q (decodeWord ((csyms A (2*q+8) (C i)++S.R 132).take (2*q+8)))).re =
      publishedCellRead q (2*q+8) (0 : ZMod s) (S.R 110) i := by
    rw [hsource]
    simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
    rw [cstream_word (2*q+8) (chirpLine s C) tail i.val (by simpa using i.val_lt)]
    simp [List.take_append,chirpLine]
  refine ⟨v₃,m₁+(m₂+(2*i.val+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add hm₁ (Nat.add_le_add_right hm₂ _),
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by rw [hlen]) ?_,hi,hpos,hread⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk132 : k = 132 <;> by_cases hk139 : k = 139 <;>
    simp_all [S₂,S₁,S₀,output,i]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
