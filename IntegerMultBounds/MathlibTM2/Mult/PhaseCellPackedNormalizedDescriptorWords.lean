module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyDescriptorInput

/-! Ordinary descriptor words for the normalized packed caller. The numerical
bank is supplied separately; this module constructs the complete outer frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {A T : ℕ}

/-- Extend the numerical bank with its core length, scalar width and ordinary
parameter queue. All remaining outer registers start blank. -/
def packedNormalizedInputBank (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) : Stacks 325 A :=
  let H := extendStacks (by decide : 280 ≤ 325) (complexBatchInputBank M B L)
  {H with R := Function.update (Function.update H.R (packedNormalizedScalarReg .wr) wl) 324 parameters}

def packedNormalizedDescriptorWords (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) : Fin 325 → List (Fin (A+4)) :=
  (packedNormalizedInputBank M B L wl parameters).R

/-- The ordinary packet uses a unary scalar width and the parameter queue
already consumed by the normalization program. -/
def ordinaryPackedNormalizedDescriptorWords (M : Stacks 276 A) (B L : ℕ)
    (p u l target s t a b : ℕ) : Fin 325 → List (Fin (A+4)) :=
  packedNormalizedDescriptorWords M B L (List.replicate B Node.tick)
    ((inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2))

/-- The complete ordinary descriptor for a batch of complex fields. Counts,
packet width, source serialization and owned core length come from the batch
itself; the native factory bank remains the input to this construction. -/
def packedNormalizedPacketWords (S : Stacks 242 A)
    (B V p u l target s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) : Fin 325 → List (Fin (A+4)) :=
  ordinaryPackedNormalizedDescriptorWords
    (packedKeyDescriptorInput (packedKeyPublicationInput S V radius) p W Fs.length ((b-a)*W)
      (cstream A W (Fs.map (packedInterval a (b-a))).flatten))
    B (coreLength s coreWidth k) p u l target s t a b

theorem packedNormalizedInputBank_view (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) :
    embStk (Fin.castLE (by decide : 280 ≤ 325)) (packedNormalizedInputBank M B L wl parameters) =
      complexBatchInputBank M B L := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk, packedNormalizedInputBank, extendStacks, i.isLt]
  · funext i
    have hheader : Fin.castLE (by decide : 280 ≤ 325) i ≠ (324 : Fin 325) := by
      intro h
      have hv := congrArg Fin.val h
      have := i.isLt
      change i.val = 324 at hv
      omega
    have hwidth : Fin.castLE (by decide : 280 ≤ 325) i ≠ packedNormalizedScalarReg .wr := by
      intro h
      have hv := congrArg Fin.val h
      have := i.isLt
      have := packedNormalizedScalarReg_bounds (.wr : TblR 25)
      change i.val = (packedNormalizedScalarReg .wr).val at hv
      omega
    simp [embStk, packedNormalizedInputBank, hheader, hwidth, extendStacks, i.isLt]

theorem packedNormalizedInputBank_width (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) :
    (packedNormalizedInputBank M B L wl parameters).R (packedNormalizedScalarReg .wr) = wl := by
  simp [packedNormalizedInputBank, packedNormalizedScalarReg_header]

theorem packedNormalizedInputBank_scalar (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) (r : TblR 25) (hr : r ≠ .wr) :
    (packedNormalizedInputBank M B L wl parameters).R (packedNormalizedScalarReg r) = [] := by
  have hne := packedNormalizedScalarReg_injective.ne hr
  have hhigh := (packedNormalizedScalarReg_bounds r).1
  simp [packedNormalizedInputBank, packedNormalizedScalarReg_header, hne,
    extendStacks, show ¬ (packedNormalizedScalarReg r).val < 280 by omega]

theorem packedNormalizedInputBank_parameters (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) :
    (packedNormalizedInputBank M B L wl parameters).R 324 = parameters := by
  simp [packedNormalizedInputBank]

theorem packedNormalizedInputBank_ports (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) (i : Fin 4) :
    (packedNormalizedInputBank M B L wl parameters).R (packedNormalizedPort i) = [] := by
  have hheader : packedNormalizedPort i ≠ (324 : Fin 325) := by
    intro h
    have hv := congrArg Fin.val h
    have := i.isLt
    change 320+i.val = 324 at hv
    omega
  have hwidth := (packedNormalizedScalarReg_port (.wr : TblR 25) i).symm
  have hhigh := packedNormalizedPort_high i
  simp [packedNormalizedInputBank, hheader, hwidth, extendStacks,
    show ¬ (packedNormalizedPort i).val < 280 by omega]

/-- Loading these ordinary words supplies exactly the constructed input bank,
including its left-stack frame and unchanged host tapes. No solver readiness
or execution is assumed in this descriptor identity. -/
theorem descriptorReadyBank_packedNormalized
    (work : Fin 325 → Fin T) (M : Stacks 276 A) (S : Stacks T A) (B L : ℕ)
    (wl parameters : List (Fin (A+4)))
    (hinp : M.inp = S.inp) (hout : M.out = S.out)
    (hleft : ∀ i, M.L i = []) (hworkLeft : ∀ i, S.L (work i) = []) :
    descriptorReadyBank work (packedNormalizedDescriptorWords M B L wl parameters) S =
      packedNormalizedInputBank M B L wl parameters := by
  refine Stacks.ext hinp.symm hout.symm ?_ rfl
  funext i
  simp [descriptorReadyBank, embStk, packedNormalizedInputBank, extendStacks,
    complexBatchInputBank, hleft, hworkLeft]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
