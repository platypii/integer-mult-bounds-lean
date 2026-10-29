module

public import IntegerMultBounds.MathlibTM2.Host.CountSelectors
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryMask

/-! Generate the fold's boundary count from its retained local membership mask. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedBoundaryFlags_count {s origin N : ℕ} [NeZero s] (B : Finset (ZMod s))
    (hB : ∀ i ∈ B, origin ≤ i.val ∧ i.val < origin+N) :
    ((packedBoundaryRhsFlags origin N B).filter id).length = B.card := by
  have hh := congrArg List.length (packedBoundary_order (a := origin) (N := N) B hB)
  have hlen : (bOrder s B).length = B.card := by
    rw [← List.toFinset_card_of_nodup (bOrder_nodup s B),bOrder_toFinset]
  simpa only [packedBoundaryRhsFlags,← List.countP_eq_length_filter,List.countP_map,
    Function.comp_def,id_eq,hlen] using hh

theorem packedBoundaryMask_count {A s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N) :
    ((couplingSourceIntervalMaskSymbols true A s t band a b origin N).filter pairRe).length =
      (haloBoundary s t band a b).card := by
  have hh := packedBoundaryRhsMask_flags hst hA band a b hb hfit
  have hc := congrArg (fun xs : List Bool => (xs.filter id).length) hh
  rw [packedBoundaryFlags_count _ hB] at hc
  simpa only [← List.countP_eq_length_filter,List.countP_map,Function.comp_def,id_eq] using hc

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedBoundaryCount : Pr P 168 Q A U := countSelectors 167 0 116 pairRe

theorem packedBoundaryCount_exec {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (h0 : S.R 0 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 7*N+4 ∧
      Exec body packedBoundaryCount (mk v S) m
        (mk v' {S with R := Function.update S.R 116 (List.replicate (haloBoundary s t band a b).card tick)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := countSelectors_exec (body := body)
    (src := 167) (saved := 0) (dst := 116) (by decide) pairRe v S h0
  rw [hmask,packedBoundaryMask_count hst hA band a b hb hfit hB,h116,List.append_nil] at he
  refine ⟨v',m,hu,?_,he⟩
  simpa only [hmask,couplingSourceIntervalMaskSymbols_length] using hm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
