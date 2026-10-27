module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEntryLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldedBandSchedule

/-! Accumulate a contiguous folded-row interval from a computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def collectColumnEntries : Pr P 151 Q A U :=
  .seq columnEntryLoop (.seq (uclear 137) (uclear 138))

noncomputable def collectColumnEntriesCost {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V start L : ℕ) : ℕ :=
  columnEntryLoopCost B q V start L+((2*(L+start)+2)+(2*L+2))

theorem collectColumnEntries_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V start L : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hfit : start+L ≤ B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = start) (hcount : (S.R 138).length = L)
    (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectColumnEntriesCost B q V start L ∧
      Exec body collectColumnEntries (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138 []) 132
          (cstream A (2*q+8) ((List.range L).reverse.map (fun i => C (bFoldAt s B (start+i))))++S.R 132))
          137 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := columnEntryLoop_exec (body := body)
    B q V start L hA hs hfit C pageTail tail v S hcursor hcount hwidth hpage hq hsource
    h0 h94 h106 h135 h136 h139 h140 hblank
  let output := cstream A (2*q+8)
    ((List.range L).reverse.map (fun i => C (bFoldAt s B (start+i))))++S.R 132
  let S₁ : Stacks 151 A := {S with R := (Function.update (Function.update S.R 132 output)
    137 (List.replicate L tick++S.R 137))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 137 v₁ S₁
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 137 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 138 v₂ S₂
  have hlen137 : (S₁.R 137).length = L+start := by simp [S₁,hcursor]
  have hlen138 : (S₂.R 138).length = L := by simpa [S₂,S₁] using hcount
  refine ⟨v₃,m₁+((2*(L+start)+2)+(2*L+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_right hm₁ _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen137,hlen138]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk132 : k = 132 <;> by_cases hk137 : k = 137 <;> by_cases hk138 : k = 138 <;>
    simp [S₂,S₁,output,hk132,hk137,hk138]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
