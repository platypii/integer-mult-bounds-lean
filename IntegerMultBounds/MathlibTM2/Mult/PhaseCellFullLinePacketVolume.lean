module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputPlan
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth

/-! The actual ordinary input installer bounds the serialized full-line bank.
Its one borrowed width seed is paid once, without expanding 303 registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan.Ready
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A s p u l target t : ℕ} [NeZero s] {U : Type}

theorem packetVolume_le {input : FullLineInputPlan T} {Fs : List (ZMod s → GaussianInt)} {S : Stacks T A}
    (h : input.Ready p u l target t Fs S) (hst : s < t) (v : HS T Q A U) :
    (∑ i, ((fullLineGridRecord (A := A) p u l target t Fs).words i).length) ≤
      inverseCallerWordWidth p u l target s t+setupStock p u l target s t Fs.length := by
  obtain ⟨v',n,F,_,_,hwords,hframe,hI,hO,hL,he⟩ := input.generate_exec
    (body := fun f : Empty => nomatch f) p u l target t hst Fs v S h 0
  have hstock := mn_replace_bank_size input.work input.injective v v' S F
    (fullLineGridRecord (A := A) p u l target t Fs).words hwords
    (by intro k hk; exact hframe k (by intro i heq; exact hk i heq.symm)) hI hO hL
  have hseed : (∑ i, (S.R (input.work i)).length) = inverseCallerWordWidth p u l target s t := by
    rw [Finset.sum_eq_single (familyInverseScalarReg .wr)]
    · rw [h.width,List.length_replicate]
    · intro i _ hi
      rw [h.blank i hi]
      rfl
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  rw [hseed] at hstock
  have hf := he.final
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.FullLineInputPlan.Ready
