module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScatterData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule

/-! Convert ascending boundary origin advances into the actual scatter controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

theorem boundaryPublicationGaps (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) :
    publicationGaps w (originAdvances w 0 (boundaryScatterOrigins s B)) = boundaryScatterGaps s B w := by
  rw [originAdvances_symbols]
  simpa only [Nat.zero_mul,boundaryScatterGaps] using
    (windowGaps_publicationGaps w ((boundaryScatterOrigins s B).map (·*w))).symm

theorem boundaryOriginAdvances_volume (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) :
    (originAdvances w 0 (boundaryScatterOrigins s B)).sum ≤ s*w := by
  have ho : (0::boundaryScatterOrigins s B).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp,(boundaryScatterOrigins_disjoint s B).imp (fun h => by omega)⟩
  simpa using originAdvances_sum_le w 0 s (boundaryScatterOrigins s B) ho (Nat.zero_le _)
    (fun p hp => (boundaryScatterOrigins_fit s B p hp).trans' (Nat.le_succ _))

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryPublicationControls : Pr P 224 Q A U :=
  publicationControls 116 184 206 217 201 160 223 208 220 211 215

theorem boundaryPublicationControls_nonempty_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (w : ℕ) (hwpos : 1 ≤ w) (hB : 0 < B.card)
    (borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hc : S.R 116 = List.replicate B.card tick)
    (hs : S.R 206 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*s*w+21 ∧
      Exec body boundaryPublicationControls (mk v S) n
        (mk v' {S with R := (Function.update S.R 220
          (gatherControls A (boundaryScatterGaps s B w)++S.R 220))}) := by
  have hh := packedBoundaryPublicationControls_nonempty_exec (body := body) s B 0 s w
    (fun i _ => ⟨Nat.zero_le _,by simpa using i.val_lt⟩) hwpos hB borrowed v S hc
    (by simpa [packedBoundaryOrigins,boundaryScatterOrigins] using hs) hw hz
  simpa [packedBoundaryPublicationControls,boundaryPublicationControls,
    packedBoundaryGaps,packedBoundaryOrigins,boundaryScatterGaps,boundaryScatterOrigins] using hh

/-- The same converter also handles an empty boundary without reading a packet. -/
def conditionalBoundaryPublicationControls : Pr P 224 Q A U :=
  .seq (.act (peekR 116)) (.cond (·.flag) boundaryPublicationControls (.act .done))

theorem conditionalBoundaryPublicationControls_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (w : ℕ) (hwpos : 1 ≤ w) (borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hc : S.R 116 = List.replicate B.card tick)
    (hs : S.R 206 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*s*w+23 ∧
      Exec body conditionalBoundaryPublicationControls (mk v S) n
        (mk v' {S with R := (Function.update S.R 220
          (gatherControls A (boundaryScatterGaps s B w)++S.R 220))}) := by
  have hh := conditionalPackedBoundaryPublicationControls_exec (body := body) s B 0 s w
    (fun i _ => ⟨Nat.zero_le _,by simpa using i.val_lt⟩) hwpos borrowed v S hc
    (by simpa [packedBoundaryOrigins,boundaryScatterOrigins] using hs) hw hz
  simpa [conditionalPackedBoundaryPublicationControls,conditionalBoundaryPublicationControls,
    packedBoundaryPublicationControls,boundaryPublicationControls,
    packedBoundaryGaps,packedBoundaryOrigins,boundaryScatterGaps,boundaryScatterOrigins] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
