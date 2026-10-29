module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyedPackedHaloPublish

/-! The reusable state between generated packed halo keys. Numerical parameters,
geometry, the source and word width are retained across publications. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

structure PackedHaloReady {A : ℕ} (precision stage q l s t u band a b V w : ℕ)
    (input E outputTail : List (Fin (A+4))) (S : Stacks 168 A) : Prop where
  native : embStk packedCellCoreReg S = releasedCellBank [] input (S.R 93) S.inp S.out
  masters : ∀ r ∈ groupHeaderCopies, r.1 ≠ 128 →
    (S.R (packedHeaderReg r.1)).length = groupHeaderValue precision stage q l s t u band 0 r.1
  metadata : CouplingIntervalMetadata V s t band a b a (b-a) S
  keyWidth : (S.R 125).length = V
  unaryLengthBound : (S.R 128).length ≤ s
  binaryLengthBound : (S.R 157).length ≤ V
  wordWidth : (S.R 130).length = w
  output : S.R 132 = E++outputTail
  length : E.length = (b-a)*w
  fresh : ∀ k ∈ [(129 : Fin 168),131,133,134,135,136,140,153,166], S.R k = []

/-- A publication restores readiness using only its native-bank and high-frame
contracts. The queue and selected length are deliberately outside this invariant. -/
theorem PackedHaloReady.of_publication {A precision stage q l s t u band a b V w : ℕ}
    {input E E' outputTail : List (Fin (A+4))} {S F : Stacks 168 A}
    (h : PackedHaloReady precision stage q l s t u band a b V w input E outputTail S)
    (hproj : embStk packedCellCoreReg F = releasedCellBank [] input (S.R 93) S.inp S.out)
    (hframe : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 128 → k ≠ 157 → k ≠ 132 →
      F.L k = S.L k ∧ F.R k = S.R k)
    (houtput : F.R 132 = E'++outputTail) (hlen : E'.length = (b-a)*w)
    (h128 : (F.R 128).length ≤ s) (h157 : (F.R 157).length ≤ V) :
    PackedHaloReady precision stage q l s t u band a b V w input E' outputTail F := by
  have hpass (k : Fin 168) (hk : 117 ≤ k.val) (h126 : k ≠ 126) (h128 : k ≠ 128)
      (h157 : k ≠ 157) (h132 : k ≠ 132) := (hframe k hk h126 h128 h157 h132).2
  constructor
  · have h93 : F.R 93 = S.R 93 := by
      simpa [embStk,packedCellCoreReg,releasedCellBank] using congrArg (fun B : Stacks 117 A => B.R 93) hproj
    have hi : F.inp = S.inp := congrArg (fun B : Stacks 117 A => B.inp) hproj
    have ho : F.out = S.out := congrArg (fun B : Stacks 117 A => B.out) hproj
    simpa only [h93,hi,ho] using hproj
  · intro r hr hn
    have hs : 117 ≤ (packedHeaderReg r.1).val ∧ packedHeaderReg r.1 ≠ 126 ∧
        packedHeaderReg r.1 ≠ 128 ∧ packedHeaderReg r.1 ≠ 157 ∧ packedHeaderReg r.1 ≠ 132 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact False.elim (hn rfl) | decide
    rw [hpass _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2]
    exact h.masters r hr hn
  · constructor
    · rw [hpass 163 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h.metadata.width
    · intro k hk
      have hs : 117 ≤ k.val ∧ k ≠ 126 ∧ k ≠ 128 ∧ k ≠ 157 ∧ k ≠ 132 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hpass k hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2]
      exact h.metadata.encoded k hk
  · rw [hpass 125 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.keyWidth
  · exact h128
  · exact h157
  · rw [hpass 130 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.wordWidth
  · exact houtput
  · exact hlen
  · intro k hk
    have hs : 117 ≤ k.val ∧ k ≠ 126 ∧ k ≠ 128 ∧ k ≠ 157 ∧ k ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hpass k hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2]
    exact h.fresh k hk

/-- The loop owns its count on 127 independently of the reusable solver state. -/
theorem PackedHaloReady.update_count {A precision stage q l s t u band a b V w : ℕ}
    {input E outputTail : List (Fin (A+4))} {S : Stacks 168 A}
    (h : PackedHaloReady precision stage q l s t u band a b V w input E outputTail S)
    (count : List (Fin (A+4))) :
    PackedHaloReady precision stage q l s t u band a b V w input E outputTail
      {S with R := Function.update S.R 127 count} := by
  constructor
  · have hp : embStk packedCellCoreReg {S with R := Function.update S.R 127 count} =
        embStk packedCellCoreReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have hn : packedCellCoreReg k ≠ 127 := by
        intro he
        have hv := congrArg (fun i : Fin 168 => i.val) he
        change k.val = 127 at hv
        have hh := k.isLt
        omega
      simp [embStk,hn]
    simpa only [hp,Function.update_of_ne (by decide : (93 : Fin 168) ≠ 127)] using h.native
  · intro r hr hn
    have hoff : packedHeaderReg r.1 ≠ 127 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hoff] using h.masters r hr hn
  · constructor
    · simpa using h.metadata.width
    · intro k hk
      have hn : k ≠ 127 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa only [Function.update_of_ne hn] using h.metadata.encoded k hk
  · simpa using h.keyWidth
  · simpa using h.unaryLengthBound
  · simpa using h.binaryLengthBound
  · simpa using h.wordWidth
  · simpa using h.output
  · exact h.length
  · intro k hk
    have hn : k ≠ 127 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hn] using h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
