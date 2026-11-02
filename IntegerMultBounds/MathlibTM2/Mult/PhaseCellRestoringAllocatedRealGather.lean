module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealGatherExposureData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringAllocatedGather

/-! Actual ambient exposure followed by routing from caller metadata into a
fresh private bank. Both phases preserve the original ambient lines and tail. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

structure AllocatedRealGatherData (bank : ComputedClassBank → Fin T)
    (V s width radius L w a D : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    extends RealGatherExposureData V s width radius L w Fs borrowed S where
  src : Fin 7 → Fin T
  hstates : FixedStreamedBank.stateCount ≤ Q
  hpacket : 0 < L*w
  hbits : a+Nat.clog 2 (coreGatherIndices s width radius L).length < D
  hfit : (L*w)*2^(a+Nat.clog 2 (coreGatherIndices s width radius L).length) < 2^D
  hrouteWide : s+width+2*radius < 2^D
  hrouteLfit : L < 2^D
  hrouteV : 0 < D
  hreplicaPower : Fs.length = 2^a
  hrouteSrc : e 108 = control (extendedBank bank) .source
  houtput : S.R (control (extendedBank bank) .source) = []
  hmetadataOff : ∀ i, src i ≠ bank (.control .source)
  hmetaS : S.R (Fin.castAdd PackedTranspose.tapeCount (src 0)) = binSyms D s
  hmetaWidth : S.R (Fin.castAdd PackedTranspose.tapeCount (src 1)) = binSyms D width
  hmetaRadius : S.R (Fin.castAdd PackedTranspose.tapeCount (src 2)) = binSyms D radius
  hmetaL : S.R (Fin.castAdd PackedTranspose.tapeCount (src 3)) = binSyms D L
  hmetaV : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 4))).length = D
  hmetaWord : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 5))).length = w
  hmetaReplicas : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 6))).length = 2^a
  hrouteBlank : ∀ i, S.R (Fin.natAdd T i) = []
  hrouteLeft : ∀ i, S.L (Fin.natAdd T i) = []
  hsourceLeft : S.L (control (extendedBank bank) .source) = []

namespace AllocatedRealGatherData
variable {bank : ComputedClassBank → Fin T} {V s width radius L w a D : ℕ}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks (T+PackedTranspose.tapeCount) (prime+K)}
noncomputable section

def program {P U : Type} (g : AllocatedRealGatherData (Q := Q) bank V s width radius L w a D Fs borrowed S) :
    Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U :=
  .seq g.toRealGatherExposureData.program (restoringAllocatedGather bank g.src g.hstates)

def timeCost (g : AllocatedRealGatherData (Q := Q) bank V s width radius L w a D Fs borrowed S) : ℕ :=
  g.toRealGatherExposureData.timeCost+((6*gatherMetadataVolume g.src S+49)+
    (geometryGatherTimeCost g.hstates D s a width radius L w+(2*gatherMetadataVolume g.src S+17)))

def stockAllowance (g : AllocatedRealGatherData (Q := Q) bank V s width radius L w a D Fs borrowed S) : ℕ :=
  g.toRealGatherExposureData.stockAllowance+
    (2*(6*gatherMetadataVolume g.src S+49)+geometryGatherStockAllowance g.hstates D s a width radius L w)

theorem exec {P U : Type}
    (g : AllocatedRealGatherData (Q := Q) bank V s width radius L w a D Fs borrowed S)
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ g.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+g.stockAllowance)
        depth g.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (control (extendedBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := g.toRealGatherExposureData.exec body v depth
  rw [g.hrouteSrc,g.houtput,List.append_nil] at he₁
  let F : Stacks (T+PackedTranspose.tapeCount) (prime+K) := {S with R :=
    (Function.update S.R (control (extendedBank bank) .source)
      (cstream (prime+K) w (coreGatherPayload width radius L Fs.reverse)))}
  have hmeta (i : Fin 7) : F.R (Fin.castAdd PackedTranspose.tapeCount (g.src i)) =
      S.R (Fin.castAdd PackedTranspose.tapeCount (g.src i)) := by
    apply Function.update_of_ne
    intro he
    apply g.hmetadataOff i
    simp only [control,extendedBank] at he
    exact Fin.ext (congrArg (fun j : Fin (T+PackedTranspose.tapeCount) => j.val) he)
  have hblank (i) : F.R (Fin.natAdd T i) = [] := by
    rw [show F.R (Fin.natAdd T i) = S.R (Fin.natAdd T i) from
      Function.update_of_ne (prefix_ne_routing (bank (.control .source)) i).symm _ _]
    exact g.hrouteBlank i
  have hvolume : gatherMetadataVolume g.src F = gatherMetadataVolume g.src S := by
    unfold gatherMetadataVolume gatherHeaderCopies
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact congrArg List.length (hmeta r.1)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := restoringAllocatedGather_exec_within body bank g.src g.hstates
    D s a width radius L w g.hwidth g.hrouteWide g.hrouteLfit g.hA g.hrouteV g.hpacket g.hbits g.hfit
    Fs.reverse (by simpa only [List.length_reverse] using g.hreplicaPower) v₁ F
    ((hmeta 0).trans g.hmetaS) ((hmeta 1).trans g.hmetaWidth)
    ((hmeta 2).trans g.hmetaRadius) ((hmeta 3).trans g.hmetaL)
    (by rw [hmeta 4]; exact g.hmetaV) (by rw [hmeta 5]; exact g.hmetaWord)
    (by rw [hmeta 6]; exact g.hmetaReplicas) hblank g.hrouteLeft g.hsourceLeft
    (Function.update_self _ _ _) depth
  rw [hvolume] at hn₂ he₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [program,stockAllowance,F,Function.update_idem] using mn_seq_within_add he₁ he₂

end
end AllocatedRealGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
