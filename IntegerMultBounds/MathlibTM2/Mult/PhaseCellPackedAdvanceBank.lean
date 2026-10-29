module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBank

/-! Load the scanner's halo origin and word width from binary metadata.
Initialization scans fixed-width words rather than a unary ambient offset. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Node

def packedAdvanceSource (i : Fin 4) : Fin 117 :=
  if i = 1 then 95 else if i = 2 then 94 else 106

def packedAdvanceValues (a w : ℕ) (i : Fin 117) : ℕ :=
  if i = 95 then a else if i = 94 then w else 0

@[simp] theorem packedAdvanceOrigin (a w : ℕ) :
    packedAdvanceValues a w (packedAdvanceSource 1) = a := by
  simp [packedAdvanceValues,packedAdvanceSource]

@[simp] theorem packedAdvanceWordWidth (a w : ℕ) :
    packedAdvanceValues a w (packedAdvanceSource 2) = w := by
  simp [packedAdvanceValues,packedAdvanceSource]

theorem packedAdvanceBank_cost (V : ℕ) :
    chirpBankLoadCost advanceReg packedAdvanceSource V V (fun _ => V) = 40*V+41 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments]
  ring

theorem packedAdvanceBank_holds {A : ℕ} (V a w : ℕ)
    (S : Stacks 117 A) (hblank : ∀ r, S.R (advanceReg r) = []) :
    tblHolds advanceReg
      {S with R := chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) S.R}
      (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun i => packedAdvanceValues a w (packedAdvanceSource i),[]⟩) := by
  exact chirpBankLoad_holds advanceReg advanceReg_injective packedAdvanceSource V V
    (packedAdvanceValues a w) S hblank

/-- All origin packets, counts and output suffixes lie above the small bank. -/
theorem packedAdvanceBank_frame {A : ℕ} (V a w : ℕ)
    (R : Fin 117 → List (Fin (A+4))) (k : Fin 117) (hk : 19 ≤ k.val) :
    chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) R k = R k := by
  apply chirpBankLoad_off
  intro r he
  have hh := advanceReg_range r
  rw [← he] at hh
  omega

theorem packedAdvanceBank_bounded (V a w : ℕ) (ha : a < 2^V) (hw : w < 2^V) :
    ∀ i, packedAdvanceValues a w (packedAdvanceSource i) < 2^V := by
  intro i
  simp only [packedAdvanceValues]
  split_ifs <;> first | exact ha | exact hw | positivity

theorem packedAdvanceBank_exec {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}
    (V a w : ℕ) (ha : a < 2^V) (hw : w < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V)
    (hsrc : ∀ i, S.R (packedAdvanceSource i) =
      binSyms V (packedAdvanceValues a w (packedAdvanceSource i)))
    (hblank : ∀ r, S.R (advanceReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpBankLoad advanceReg packedAdvanceSource 115 115) (mk v S)
        (40*V+41)
        (mk v' {S with R := (chirpBankLoadR advanceReg packedAdvanceSource V V
          (packedAdvanceValues a w) S.R)}) ∧
      tblHolds advanceReg
        {S with R := chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) S.R}
        (tblRho V (List.replicate V tick) (List.replicate V tick)
          ⟨fun i => packedAdvanceValues a w (packedAdvanceSource i),[]⟩) ∧
      ∀ k : Fin 117, 19 ≤ k.val →
        chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) S.R k = S.R k := by
  have hoff (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
    intro r he
    have hh := advanceReg_range r
    rw [he] at hh
    omega
  have hfits : ∀ i, packedAdvanceValues a w (packedAdvanceSource i) < 2^V := by
    exact packedAdvanceBank_bounded V a w ha hw
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) advanceReg advanceReg_injective packedAdvanceSource 115 115
    (hoff 115 (by decide)) (hoff 115 (by decide))
    (fun i => hoff (packedAdvanceSource i) (by
      simp only [packedAdvanceSource]; split_ifs <;> decide)) V V (fun _ => V)
    (packedAdvanceValues a w) hfits (fun _ => le_rfl) v S hV hV hsrc hblank
  exact ⟨v',hu,he.cast (packedAdvanceBank_cost V) rfl,packedAdvanceBank_holds V a w S hblank,
    fun k hk => packedAdvanceBank_frame V a w S.R k hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
