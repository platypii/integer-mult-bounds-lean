module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePackedBandTable

/-! Retire the generated packed band table in the shared bank, preserving all borrowed suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageRetireBandTable : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (retirePackedBandTable (P := Empty))

theorem sharedPageRetireBandTable_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (tail : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hW : (S.R 190).length = W) (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = bandTableWords A w B W columns 0++tail)
    (hfresh : ∀ i ∈ ([152,151,131,134,135,136,137,138] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retirePackedBandTableCost B.card W w ∧
      Exec body sharedPageRetireBandTable (mk v S) n
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  let T := embStk sharedPageRecoveryReg S
  have hz : ∀ i ∈ ([152,151,131,134,135,136,137,138] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp [sharedPageRecoveryReg])
  obtain ⟨v₁,n,hu₁,hn,he⟩ := retirePackedBandTable_exec (body := fun p : Empty => nomatch p)
    B W w columns hlen tail (embDn sharedPageRecoveryReg v) T hW hN hw hsource hz
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
