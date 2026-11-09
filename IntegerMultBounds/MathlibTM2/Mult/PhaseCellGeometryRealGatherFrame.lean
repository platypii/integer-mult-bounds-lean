module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryRealGatherData

/-! Transport ordinary exposure and routing data through an unrelated setup.
Only the declared input ports matter; the physical program is unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {V s width radius L w a D : ℕ}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S F : Stacks T (prime+K)}

namespace RealGatherExposureData

def readPort (g : RealGatherExposureData V s width radius L w Fs borrowed S) (r : Fin T) : Prop :=
  (∃ i, g.e i = r) ∨ r ∈ [g.count,g.source,g.archive,g.saved,g.tmp,g.replicas,g.savedReplicas]

def of_frame (g : RealGatherExposureData V s width radius L w Fs borrowed S)
    (hread : ∀ r, g.readPort r → F.R r = S.R r) :
    RealGatherExposureData V s width radius L w Fs borrowed F := by
  have he (i) := hread (g.e i) (Or.inl ⟨i,rfl⟩)
  have hp (r) (hr : r ∈ [g.count,g.source,g.archive,g.saved,g.tmp,g.replicas,g.savedReplicas]) :=
    hread r (Or.inr hr)
  exact { g with
    h163 := by simpa only [he] using g.h163
    h115 := by simpa only [he] using g.h115
    h103 := by simpa only [he] using g.h103
    h105 := by simpa only [he] using g.h105
    hs := by simpa only [he] using g.hs
    hw := by simpa only [he] using g.hw
    hr := by simpa only [he] using g.hr
    hL := by simpa only [he] using g.hL
    hz := by simpa only [he] using g.hz
    hblank := by simpa only [he] using g.hblank
    h104 := by simpa only [he] using g.h104
    h106 := by simpa only [he] using g.h106
    h116 := by simpa only [he] using g.h116
    hsource := by simpa only [hp g.source (by simp)] using g.hsource
    harchive := by simpa only [hp g.archive (by simp)] using g.harchive
    hreplicas := by simpa only [hp g.replicas (by simp)] using g.hreplicas
    hsavedReplicas := by simpa only [hp g.savedReplicas (by simp)] using g.hsavedReplicas
    hlocal := by simpa only [he] using g.hlocal
    hcount := by simpa only [hp g.count (by simp)] using g.hcount
    hsaved := by simpa only [hp g.saved (by simp)] using g.hsaved
    htmp := by simpa only [hp g.tmp (by simp)] using g.htmp
    hword := by simpa only [he] using g.hword
    hcontrol := by simpa only [he] using g.hcontrol
    horigin := by simpa only [he] using g.horigin
    hclean := by simpa only [he] using g.hclean
    hfresh := by simpa only [he] using g.hfresh }

end RealGatherExposureData

namespace GeometryRealGatherData

def readPort (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S) (r : Fin T) : Prop :=
  g.toRealGatherExposureData.readPort r ∨ ∃ i, g.route i = r

def of_frame (g : GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed S)
    (hread : ∀ r, g.readPort r → F.R r = S.R r) (hleft : F.L = S.L) :
    GeometryRealGatherData (Q := Q) V s width radius L w a D Fs borrowed F :=
  { g with
    toRealGatherExposureData := g.toRealGatherExposureData.of_frame (fun r hr => hread r (Or.inl hr))
    houtput := (hread _ (Or.inr ⟨_,rfl⟩)).trans g.houtput
    hready := g.hready.of_frame (fun i _ => hread _ (Or.inr ⟨i,rfl⟩)) (fun i => congrFun hleft (g.route i)) }

end GeometryRealGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
