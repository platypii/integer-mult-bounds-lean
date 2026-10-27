module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryTable
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableLoopReady

/-! The accumulated page may depend on execution witnesses while its source frame stays fixed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix

noncomputable def tableLoopRegs {A s : ℕ} [NeZero s] (w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (base : Regs 154 A) (columns : List (ZMod s → GaussianInt)) : Regs 154 A :=
  Function.update (Function.update base 132 (bandTableWords A w B W columns 0++base 132))
    151 (List.replicate columns.length IntegerMultBounds.MathlibTM2.Node.tick)

def TableLoopInvariant {A s : ℕ} [NeZero s] (q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (Sh : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ) (base : Regs 154 A) (n : ℕ) (R : Regs 154 A) : Prop :=
  ∃ columns : List (ZMod s → GaussianInt), columns.length = n ∧
    ColumnFamilyAccurate A q w B Sh ε columns ∧ ColumnFamilyFormat w columns ∧
    ∀ k : Fin 154, k ≠ 152 → k ≠ 153 → R k = tableLoopRegs w B W base columns k

theorem TableLoopInvariant.of_frame {A s : ℕ} [NeZero s] {q w W n : ℕ} {B : Finset (ZMod s)}
    {Sh : Matrix (ZMod s) (ZMod s) ℝ} {ε : ℝ} {base R R' : Regs 154 A}
    (hframe : ∀ k : Fin 154, k ≠ 152 → k ≠ 153 → R' k = R k)
    (h : TableLoopInvariant q w B W Sh ε base n R) :
    TableLoopInvariant q w B W Sh ε base n R' := by
  obtain ⟨columns,hlen,hcolumns,hformat,hr⟩ := h
  exact ⟨columns,hlen,hcolumns,hformat,fun k hk152 hk153 => (hframe k hk152 hk153).trans (hr k hk152 hk153)⟩

theorem TableLoopInvariant.ready {A P N q l s t u band V width w W n : ℕ} [NeZero s]
    {B : Finset (ZMod s)} {Sh : Matrix (ZMod s) (ZMod s) ℝ} {ε : ℝ}
    {input : List (Fin (A+4))} {S S' : Stacks 154 A}
    (hready : ScalarPlacement.LengthKeyReady P N q l s t u band V width input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (hL : S'.L = S.L) (h : TableLoopInvariant q w B W Sh ε S.R n S'.R) :
    ScalarPlacement.LengthKeyReady P N q l s t u band V width input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  apply ScalarPlacement.tableLoopReady_of_frame hready hL
  intro k hk hk132
  obtain ⟨columns,hlen,hcolumns,hformat,hr⟩ := h
  rw [hr k (by omega) (by omega)]
  simp [tableLoopRegs,hk132,show k ≠ 151 by omega]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
