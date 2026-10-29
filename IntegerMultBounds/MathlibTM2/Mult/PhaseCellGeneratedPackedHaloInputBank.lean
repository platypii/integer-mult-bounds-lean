module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupInput
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generated binary halo controls establish the exact packed batch ABI.
Origin packets and count are produced by execution, not supplied by the caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Generated packets have the batch's working width and retain its FFT exponent suffix. -/
theorem naturalGroupInputBank_packed_halo_controls {A s : ℕ} [NeZero s]
    (P N q l t u band a b L : ℕ) (hab : a ≤ b) (hb : b ≤ s) (hL : 0 < L)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let V := weightWorkspaceWidth P q (2*q+8) t u
    let offsets := haloPackedOffsets s t band a b L
    let B := naturalGroupInputBank P N q l s t u band L [] borrowed outTail inp out
    {B with R := (Function.update (Function.update B.R
      109 (haloOriginPackets A V s t band a b L++B.R 109))
      116 (List.replicate (haloLengthGroup s t band a b L).length tick))} =
      batchInputBank P N q l s t u band L offsets.length
        (fun n => (packedCellOrigin (s := s) a offsets n).val) [] borrowed outTail inp out := by
  dsimp only
  have hpackets := packedCellOrigin_packets (A := A) (s := s)
    (weightWorkspaceWidth P q (2*q+8) t u)
    (haloPackedOffsets s t band a b L) (show a+(b-a) ≤ s by omega) hL
    (haloPackedOffsets_fit s t band a b L)
  rw [← haloOriginPackets_eq_packed] at hpackets
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h109 : k = 109
  · subst k
    simpa [naturalGroupInputBank,batchInputBank] using congrArg (fun xs => xs++List.replicate l tick) hpackets.symm
  by_cases h116 : k = 116
  · subst k; simp [naturalGroupInputBank,batchInputBank]
  · simp [h109,h116,naturalGroupInputBank,batchInputBank,Function.update_apply,
      show k.val ≠ 109 from fun he => h109 (Fin.ext he),
      show k.val ≠ 116 from fun he => h116 (Fin.ext he)]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

theorem metadataHaloClass_inputBank_exec {V s t band a b origin K L precision stage q l u : ℕ} [NeZero s]
    (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth precision q (2*q+8) t u)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmeta : CouplingIntervalMetadata V s t band a b origin K S) (h157 : S.R 157 = binSyms V L)
    (hbank : embStk packedCellCoreReg S = naturalGroupInputBank precision stage q l s t u band L [] borrowed outTail inp out) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ binaryHaloClassCost V s t band a b L ∧
      Exec body metadataHaloClass (mk v S) m (mk v' F) ∧
      F = {S with R := (Function.update (Function.update S.R 109
        (haloOriginPackets A V s t band a b L++S.R 109))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick))} ∧
      embStk packedCellCoreReg F = batchInputBank precision stage q l s t u band L
        (haloPackedOffsets s t band a b L).length
        (fun n => (packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n).val)
        [] borrowed outTail inp out := by
  have hR (i : Fin 117) := congrArg (fun B : Stacks 117 A => B.R i) hbank
  have hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [] := by
    intro k hk
    let i : Fin 117 := ⟨k.val,by omega⟩
    have hh := hR i
    change S.R k = _ at hh
    apply hh.trans
    apply batchInputBank_low
    dsimp [i]; omega
  have h104 : S.R 104 = [] := by simpa [embStk,packedCellCoreReg,naturalGroupInputBank,batchInputBank] using hR 104
  have h106 : S.R 106 = [] := by simpa [embStk,packedCellCoreReg,naturalGroupInputBank,batchInputBank] using hR 106
  have h116 : S.R 116 = [] := by simpa [embStk,packedCellCoreReg,naturalGroupInputBank,batchInputBank] using hR 116
  obtain ⟨v',m,hu,hm,he⟩ := metadataHaloClass_exec (body := body) (NeZero.pos s) hst hband hab hb
    hL hLs hA hwide v S hmeta h157 hblank h104 h106 h116
  refine ⟨v',_,m,hu,hm,he,rfl,?_⟩
  change embStk packedCellCoreReg {S with R := (Function.update (Function.update S.R
    (packedCellCoreReg 109) (haloOriginPackets A V s t band a b L++(embStk packedCellCoreReg S).R 109))
    (packedCellCoreReg 116) (List.replicate (haloLengthGroup s t band a b L).length tick))} = _
  let S₁ : Stacks 168 A := {S with R := (Function.update S.R (packedCellCoreReg 109)
    (haloOriginPackets A V s t band a b L++(embStk packedCellCoreReg S).R 109))}
  change embStk packedCellCoreReg {S₁ with R := (Function.update S₁.R (packedCellCoreReg 116)
    (List.replicate (haloLengthGroup s t band a b L).length tick))} = _
  rw [embStk_updateR packedCellCoreReg_injective]
  dsimp only [S₁]
  rw [embStk_updateR packedCellCoreReg_injective,hbank,hVeq]
  exact naturalGroupInputBank_packed_halo_controls precision stage q l t u band a b L hab hb hL borrowed outTail inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
