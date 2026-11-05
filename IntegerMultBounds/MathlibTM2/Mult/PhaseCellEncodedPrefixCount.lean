module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Build the encoded prefix length from retained dimensions, retiring the
intermediate row count. The straight-line setup interpreter supplies the proof. -/
def encodedPrefixCountOps (cells rowCount width rows words saved tmp : Fin T) : List (UnarySetup.Op T) :=
  [.mul cells rowCount rows saved tmp, .mul rows width words saved tmp, .clear rows]

def encodedPrefixCountCost (N L W : ℕ) : ℕ :=
  N*(4*L+9)+(N*L)*(4*W+9)+2*(N*L)+11

theorem encodedPrefixCount_exec
    (cells rowCount width rows words saved tmp : Fin T)
    (hreg : [cells,rowCount,width,rows,words,saved,tmp].Nodup)
    (N L W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R cells).length = N) (hL : (S.R rowCount).length = L)
    (hW : (S.R width).length = W)
    (hfresh : ∀ k ∈ [rows,words,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ encodedPrefixCountCost N L W ∧
      Exec body (UnarySetup.program (encodedPrefixCountOps cells rowCount width rows words saved tmp))
        (mk v S) n (mk v' {S with R := Function.update S.R words (List.replicate (N*L*W) tick)}) := by
  have hr := hreg
  regs_ne hr
  have hready : UnarySetup.Ready (encodedPrefixCountOps cells rowCount width rows words saved tmp) S.R := by
    simp only [encodedPrefixCountOps,UnarySetup.Ready,UnarySetup.Op.Ready,UnarySetup.Op.runR]
    refine ⟨⟨by regs_nodup,hfresh saved (by simp),hfresh tmp (by simp)⟩,
      ⟨⟨by regs_nodup,?_,?_⟩,trivial,trivial⟩⟩ <;>
      simp [Ne.symm ‹rows ≠ saved›,Ne.symm ‹rows ≠ tmp›,hfresh saved (by simp),hfresh tmp (by simp)]
  obtain ⟨v',n,hu,hn,he⟩ := UnarySetup.exec (body := body)
    (encodedPrefixCountOps cells rowCount width rows words saved tmp) v S hready
  have hcost : UnarySetup.cost (encodedPrefixCountOps cells rowCount width rows words saved tmp) S.R =
      encodedPrefixCountCost N L W := by
    simp [encodedPrefixCountOps,UnarySetup.cost,UnarySetup.Op.cost,UnarySetup.Op.runR,
      hN,hL,hW,hfresh rows (by simp),‹width ≠ rows›,‹rows ≠ words›,
      encodedPrefixCountCost]
    omega
  have hframe : UnarySetup.runR (encodedPrefixCountOps cells rowCount width rows words saved tmp) S.R =
      Function.update S.R words (List.replicate (N*L*W) tick) := by
    funext k
    by_cases hrows : k = rows
    · subst k
      simp [encodedPrefixCountOps,UnarySetup.runR,UnarySetup.Op.runR,‹rows ≠ words›,hfresh rows (by simp)]
    · simp [encodedPrefixCountOps,UnarySetup.runR,UnarySetup.Op.runR,Function.update_apply,
        hrows,hN,hL,hW,‹width ≠ rows›,Ne.symm ‹rows ≠ words›,hfresh rows (by simp),hfresh words (by simp)]
  rw [hcost] at hn
  rw [hframe] at he
  exact ⟨v',n,hu,hn,he⟩

theorem encodedPrefixCount_native (cells rowCount width rows words saved tmp : Fin T) :
    mnNativePushBound 2 (UnarySetup.program (P := P) (Q := Q) (A := A) (U := U)
      (encodedPrefixCountOps cells rowCount width rows words saved tmp)) := by
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨unaryProduct_native _ _ _ _ _,unaryProduct_native _ _ _ _ _,?_,?_⟩
  · simp [UnarySetup.Op.program,mnNativePushBound,uclear,drainR,popDo,peekR,mnActPush]
  · simp [UnarySetup.program,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
