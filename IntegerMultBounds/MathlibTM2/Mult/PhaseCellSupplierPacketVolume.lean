module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierReadyCosts
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth

/-! Actual installation bounds the ordinary descriptor volume, independently
of the packet bank's concrete register layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan.Ready
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s : ℕ} [NeZero s] {U : Type}

theorem packetVolume_le {input : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : input.Ready r S) (v : HS T Q A U) : (∑ i, (r.words i).length) ≤ r.inputStock := by
  obtain ⟨v',n,F,hu,hn,hwords,hframe,hleft,hin,hout,he⟩ :=
    input.exec (body := fun f : Empty => nomatch f) r v S h 0
  have hg := mn_fill_bank_size input.work input.injective v v' S F r.words h.blank hwords
    (by intro k hk; exact hframe k (by intro i heq; exact hk i heq.symm)) hin hout hleft
  have hf := he.final
  rw [hg,h.stock_eq] at hf
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan.Ready
