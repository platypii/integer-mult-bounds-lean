module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherData

/-! Exact metadata volumes for both private banks in the restoring caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K V s width radius L w : ℕ} {bank : ComputedClassBank → Fin T}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K)}

namespace RestoringGatherData

theorem exposureMetadataVolume_eq
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S) :
    exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S) = 5*V+w+s*w+Fs.length := by
  simp only [exposureMetadataVolume,exposureHeaderCopies,exposureHeaderAssignments,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil]
  simp only [g.hs,g.hw,g.hr,g.hL,g.hV,g.hword,g.hcount,g.hreplicas,length_binSyms]
  omega

theorem routingMetadataVolume_eq
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S) :
    gatherMetadataVolume (fun i => Fin.castAdd 175 (g.routeSrc i)) S = 6*g.D+w+Fs.length := by
  have hs := g.hRs
  have hw := g.hRw
  have hr := g.hRr
  have hL := g.hRL
  have hV := g.hRV
  have hword := g.hRword
  have hrep := g.hRrep
  simp only [classCallerRegister,exposureIntoRouting] at hs hw hr hL hV hword hrep
  simp only [gatherMetadataVolume,gatherHeaderCopies,gatherHeaderAssignments,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil]
  simp only [hs,hw,hr,hL,hV,hword,hrep,length_binSyms,g.hpower]
  omega

end RestoringGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
