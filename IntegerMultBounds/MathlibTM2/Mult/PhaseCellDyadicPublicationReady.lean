module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationTranspose

/-! Retained dyadic publication headers and fresh workspace, independent of
the source archive. A restoring handoff changes only that source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
variable {T Q K : ℕ}

structure PublicationWorkspaceReady (e : Fin tapeCount → Fin T)
    (exponent packet pad tmp saved : Fin tapeCount) (a b L W V : ℕ) (S : Stacks T (prime+K)) : Prop where
  exponent : (S.R (e exponent)).length = a+b
  packet : (S.R (e packet)).length = L*W
  pad : S.R (e pad) = []
  tmp : S.R (e tmp) = []
  saved : S.R (e saved) = []
  zero : S.R (e (base (callerGenerator 106))) = []
  width : (S.R (e (base (callerGenerator 115)))).length = V
  blank : ∀ r, S.R (e (base (callerGenerator (originReg r)))) = []
  stages : S.R (e (base (callerGenerator 116))) = []
  left : ∀ i, S.L (e i) = []
  fresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 →
    S.R (e (base (callerWorker i))) = []
  count : S.R (e (extra 4)) = []
  codec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R (e i) = []

structure PublicationReady (e : Fin tapeCount → Fin T)
    (exponent packet pad tmp saved : Fin tapeCount) (a b L W V : ℕ) (S : Stacks T (prime+K)) : Prop
    extends PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V S where
  a : S.R (e (base (callerGenerator 97))) = binSyms V a
  b : S.R (e (base (callerGenerator 98))) = binSyms V b
  seed : S.R (e (base (callerGenerator 102))) = binSyms V (L*W)

private theorem padding_source_off {exponent packet pad tmp saved : Fin tapeCount}
    (hr : [exponent,packet,extra 1,pad,tmp,saved].Nodup) :
    ∀ r ∈ [exponent,packet,pad,tmp,saved], r ≠ extra 1 := by
  regs_ne hr
  intro r hmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  all_goals first | assumption | (apply Ne.symm; assumption)

theorem PublicationReady.of_frame {e : Fin tapeCount → Fin T}
    {exponent packet pad tmp saved : Fin tapeCount} {a b L W V : ℕ} {S F : Stacks T (prime+K)}
    (h : PublicationReady e exponent packet pad tmp saved a b L W V S)
    (hreg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (hR : ∀ i, i ≠ extra 1 → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    PublicationReady e exponent packet pad tmp saved a b L W V F := by
  have hp (r : Fin tapeCount) (hr : r ∈ [exponent,packet,pad,tmp,saved]) := hR r (padding_source_off hreg r hr)
  have hb (i : Fin kernelT) := hR (base i) (base_extra i 1)
  refine {
    exponent := ?_
    packet := ?_
    pad := ?_
    tmp := ?_
    saved := ?_
    a := ?_
    b := ?_
    seed := ?_
    zero := ?_
    width := ?_
    blank := ?_
    stages := ?_
    left := ?_
    fresh := ?_
    count := ?_
    codec := ?_ }
  · rw [hp exponent (by simp)]; exact h.exponent
  · rw [hp packet (by simp)]; exact h.packet
  · rw [hp pad (by simp)]; exact h.pad
  · rw [hp tmp (by simp)]; exact h.tmp
  · rw [hp saved (by simp)]; exact h.saved
  · simpa only [hb] using h.zero
  · simpa only [hb] using h.width
  · simpa only [hb] using h.blank
  · simpa only [hb] using h.stages
  · simpa only [hL] using h.left
  · simpa only [hb] using h.fresh
  · rw [hR (extra 4) (by simp [extra,Fin.ext_iff])]; exact h.count
  · intro i hi
    have hne : i ≠ extra 1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact base_extra _ 1
      all_goals simp [planeReg,extra,Fin.ext_iff]
    rw [hR i hne]
    exact h.codec i hi

  · simpa only [hb] using h.a
  · simpa only [hb] using h.b
  · simpa only [hb] using h.seed

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
