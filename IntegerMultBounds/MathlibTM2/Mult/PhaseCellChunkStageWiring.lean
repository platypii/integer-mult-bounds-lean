module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBank
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

/-- Prefix masters are read in reverse power order; suffix masters in forward
power order. The two exponent fields share a single borrowed master. -/
def wiredChunkStages {T c : ℕ} (K W : ℕ) (one exponent : Fin T)
    (prefixes suffixes : Fin c → Fin T) : List (ChunkInterchangeStage T) :=
  List.ofFn fun i => {
    dims := ![prefixes i.rev,one,suffixes i,exponent,exponent]
    outerCount := K^(c-1-i.val)
    blockWidth := W*K^i.val }

theorem replicaChunkSwaps_ofFn (K W c : ℕ) :
    replicaChunkSwaps K W c = List.ofFn (fun i : Fin c => (K^(c-1-i.val),W*K^i.val)) := by
  induction c generalizing W with
  | zero => simp [replicaChunkSwaps]
  | succ c ih =>
    rw [replicaChunkSwaps,ih,List.ofFn_succ]
    congr 1
    · simp
    · apply congrArg List.ofFn
      funext i
      apply Prod.ext
      · apply congrArg (fun j => K^j)
        simp only [Fin.val_succ]
        omega
      · simp only [Fin.val_succ,pow_succ]
        ring

theorem wiredChunkStages_shape {T c : ℕ} (K W : ℕ) (one exponent : Fin T)
    (prefixes suffixes : Fin c → Fin T) :
    ((wiredChunkStages K W one exponent prefixes suffixes).map fun r => (r.outerCount,r.blockWidth)) =
      replicaChunkSwaps K W c := by
  rw [replicaChunkSwaps_ofFn]
  simp only [wiredChunkStages,List.map_ofFn,Function.comp_def]

/-- Master lengths produced by the two power chains discharge all five scalar
fields of every wired stage. -/
theorem wiredChunkStages_values {T A c : ℕ} (d W : ℕ) (one exponent : Fin T)
    (prefixes suffixes : Fin c → Fin T) (R : Regs T A)
    (hone : (R one).length = 1) (hexponent : (R exponent).length = d)
    (hp : ∀ i, (R (prefixes i)).length = (2^d)^i.val)
    (hb : ∀ i, (R (suffixes i)).length = W*(2^d)^i.val) :
    ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, (R (r.dims k)).length = swapValues r.outerCount 1 r.blockWidth d d k := by
  intro r hr k
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  fin_cases k <;> simp [swapValues,hp,hb,hone,hexponent,Fin.rev]
  congr 1
  omega

/-- Wire the actual generated banks into all stage dimensions. Only the original
one/width/exponent master lengths are premises; no generated power is supplied. -/
theorem wiredChunkStages_bank_values {T A c : ℕ} (d W : ℕ) (one width exponent : Fin T)
    (ps bs : List (Fin T)) (hp : (one::ps).Nodup) (hb : (width::bs).Nodup)
    (hsep : ∀ p ∈ one::ps, ∀ b ∈ width::bs, p ≠ b)
    (prefixes suffixes : Fin c → Fin T)
    (hprefixes : List.ofFn prefixes = one::ps) (hsuffixes : List.ofFn suffixes = width::bs)
    (hexOff : exponent ∉ ps++bs) (R : Regs T A)
    (hone : (R one).length = 1) (hwidth : (R width).length = W) (hexponent : (R exponent).length = d) :
    ∀ r ∈ wiredChunkStages (2^d) W one exponent prefixes suffixes,
      ∀ k, (chunkDimensionBankR (2^d) W ps bs R (r.dims k)).length =
        swapValues r.outerCount 1 r.blockWidth d d k := by
  obtain ⟨hpowers,hwidths⟩ := chunkDimensionBank_lengths (2^d) W one width ps bs hp hb hsep R hone hwidth
  have hlengths : (one::ps).length = c ∧ (width::bs).length = c := by
    constructor
    · rw [←hprefixes,List.length_ofFn]
    · rw [←hsuffixes,List.length_ofFn]
  apply wiredChunkStages_values
  · rw [chunkDimensionBankR_off (2^d) W ps bs R one (by
      simp only [List.mem_append,not_or]
      exact ⟨(List.nodup_cons.mp hp).1,by intro hi; exact hsep one (by simp) one (by simp [hi]) rfl⟩)]
    exact hone
  · rw [chunkDimensionBankR_off _ _ _ _ _ _ hexOff]
    exact hexponent
  · intro i
    have hh := hpowers i.val (by rw [hlengths.1]; exact i.isLt)
    simpa only [←hprefixes,List.getElem_ofFn] using hh
  · intro i
    have hh := hwidths i.val (by rw [hlengths.2]; exact i.isLt)
    simpa only [←hsuffixes,List.getElem_ofFn] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
