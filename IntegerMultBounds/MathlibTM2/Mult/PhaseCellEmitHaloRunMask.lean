module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEmitRunPackets
public import IntegerMultBounds.NLogN.PhaseCellHaloRunMask

/-! Instantiate the fixed run consumer with the exact halo interval mask.
The binary run packets and flags are explicit preconditions; their producer is separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem emitHaloRunMask_exec {s t : ℕ} [NeZero s] (hst : s < t)
    (W band a b : ℕ) (hb : b ≤ s) (hsW : s < 2^W) (off on : Fin (A+4))
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hW : (S.R 115).length = W)
    (hflags : S.R 116 = (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b)).map
      (fun r => bitSymbol r.1))
    (hsrc : S.R 109 = (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b)).flatMap
      (fun r => binSyms W r.2)++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,22,23,25,26,27], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 10*s+(19*W+22)*(2*(t-s+1)+1)+6 ∧
      Exec body (emitRunPackets off on) (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          ((List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off)++tail))}) := by
  let xs := IntervalRunMask.runs 0 s (haloRunIntervals s t band a b)
  have hsum : (xs.map Prod.snd).sum = s := by
    simpa [xs] using IntervalRunMask.sum_runs (haloRunIntervals_ordered s t band a b)
  have hlength : xs.length ≤ 2*(t-s+1)+1 := by
    dsimp only [xs]
    rw [IntervalRunMask.length_runs]
    have := haloRunIntervals_length_le s t band a b
    omega
  have hfit : ∀ r ∈ xs, r.2 < 2^W := by
    intro r hr
    have hle : r.2 ≤ (xs.map Prod.snd).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)
    omega
  have hout : xs.flatMap (fun r => List.replicate r.2 (if r.1 then on else off)) =
      (List.range s).map (fun k => if haloInteriorAt s t band a b k then on else off) := by
    have hm := congrArg (List.map (fun flag : Bool => if flag then on else off))
      (haloRunMask_eq hst band a b hb)
    rw [← IntervalRunMask.flatten_runs] at hm
    simpa [xs,List.map_flatMap,List.map_replicate,List.map_map,Function.comp_def] using hm
  obtain ⟨v',n,hu,hn,he⟩ := emitRunPackets_exec (body := body) W xs off on hfit v S tail hW hflags hsrc hfresh
  refine ⟨v',n,hu,?_,?_⟩
  · rw [hsum] at hn
    exact hn.trans (by gcongr)
  · simpa only [hout] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
