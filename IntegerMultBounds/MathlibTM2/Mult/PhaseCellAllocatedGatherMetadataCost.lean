module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringAllocatedRealGather

/-! The eight copied routing headers have a bill determined by seven caller
words; the unary width master is used at two destinations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K V s width radius L w a D : ℕ} {bank : ComputedClassBank → Fin T}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks (T+PackedTranspose.tapeCount) (prime+K)}

namespace AllocatedRealGatherData

theorem metadataVolume_eq
    (g : AllocatedRealGatherData (Q := Q) bank V s width radius L w a D Fs borrowed S) :
    gatherMetadataVolume g.src S = 6*D+w+Fs.length := by
  simp only [gatherMetadataVolume,gatherHeaderCopies,gatherHeaderAssignments,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil]
  simp only [g.hmetaS,g.hmetaWidth,g.hmetaRadius,g.hmetaL,g.hmetaV,g.hmetaWord,
    g.hmetaReplicas,length_binSyms,g.hreplicaPower]
  omega

end AllocatedRealGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
