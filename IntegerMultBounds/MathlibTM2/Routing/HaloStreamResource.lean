module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedVolume

/-! Charge the executed halo stream by real coefficient bytes plus metadata
per coarse page. The latter retains its 1/L amortization over the tensor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloStreamResource
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume
open IntegerMultBounds.MathlibTM2.Fast.TableVM RegularHaloCountCode

def metadataUnit (V : ℕ) := 33*tblC V V+201*V+238
def haloUnit (V : ℕ) := metadataUnit V+76*V+228

def sourceBytes (p : Parameters) := p.N*p.L*p.B*p.w

theorem metadata_cost_le (N V : ℕ) (hN : 0 < N) : RegularHaloMetadata.prepareCost N V ≤ N*metadataUnit V := by
  have hmod := Nat.mod_le N 2
  have h1 : 10*paddedCount N+13 ≤ 33*N := by unfold paddedCount; omega
  have h2 : 4*paddedCount N+193 ≤ 201*N := by unfold paddedCount; omega
  have h3 : 6*paddedCount N+226 ≤ 238*N := by unfold paddedCount; omega
  have h1' := Nat.mul_le_mul_right (tblC V V) h1
  have h2' := Nat.mul_le_mul_right V h2
  dsimp only [RegularHaloMetadata.prepareCost,metadataUnit]
  nlinarith only [h1',h2',h3]

theorem halo_cost_le (p : Parameters) : haloCost p ≤ 160*sourceBytes p+p.N*haloUnit p.V := by
  have hmeta := metadata_cost_le p.N p.V p.N_pos
  have hL : p.L ≤ p.N*p.L := Nat.le_mul_of_pos_left p.L p.N_pos
  have h2 : 2*(p.H*p.B) ≤ p.N*p.L*p.B := by
    calc
      _ = (2*p.H)*p.B := by ring
      _ ≤ (p.N*p.L)*p.B := Nat.mul_le_mul_right p.B (p.gap.trans hL)
  have hh : p.H*p.B ≤ p.N*p.L*p.B := by omega
  have hw : 8*p.w+9 ≤ 17*p.w := by have hp := p.w_pos; omega
  have h1 := Nat.mul_le_mul (show p.N*p.L*p.B+p.H*p.B ≤ 2*(p.N*p.L*p.B) by omega) hw
  have h3 := Nat.mul_le_mul_right p.w (show 30*(p.N*p.L*p.B)+28*(p.H*p.B) ≤ 58*(p.N*p.L*p.B) by omega)
  have h4 := Nat.mul_le_mul_left 34 (Nat.mul_le_mul_right p.w
    (show p.N*(p.L*p.B)+2*(p.H*p.B) ≤ 2*(p.N*p.L*p.B) by nlinarith only [h2]))
  have h5 : p.N*(76*p.V+149)+79 ≤ p.N*(76*p.V+228) := by have hn := p.N_pos; nlinarith only [hn]
  dsimp only [haloCost,GeneratedPeriodicHalo.cost,sourceBytes,haloUnit]
  nlinarith only [hmeta,h1,h3,h4,h5]

variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem halo_cost_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) :
    (xs axis retained s).prod*haloCost s.params ≤
      320*volume axis ∅*s.params.w+((2*volume axis ∅)/L)*haloUnit s.params.V := by
  have hlocal : localLength axis retained s.i = s.params.L := by
    simp [localLength,hr.fresh,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hPL : s.params.L = L := by simpa only [hr.axis_eq,HaloAxisTensorInvariant.axisOf] using hL s.i
  have hN : (axis s.i).N = s.params.N := by simp only [hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hfactor := halo_factorization axis retained s.left s.i s.right hn hall
  rw [hlocal,hN,hr.spectator] at hfactor
  have hbytes : (xs axis retained s).prod*sourceBytes s.params = volume axis retained*s.params.w := by
    dsimp only [xs,sourceBytes]
    rw [←hfactor]
    ring
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis retained L H hL hH hLpos hlarge
  have hpages := page_count_le axis retained s.left s.i s.right hn hall
  rw [hN,hlocal,hPL] at hpages
  have hquot : volume axis retained/L ≤ (2*volume axis ∅)/L := Nat.div_le_div_right hv.le
  have hpage : (xs axis retained s).prod*s.params.N ≤ (2*volume axis ∅)/L := hpages.trans hquot
  calc
    _ ≤ (xs axis retained s).prod*(160*sourceBytes s.params+s.params.N*haloUnit s.params.V) :=
      Nat.mul_le_mul_left _ (halo_cost_le s.params)
    _ = 160*(volume axis retained*s.params.w)+((xs axis retained s).prod*s.params.N)*haloUnit s.params.V := by
      rw [←hbytes]; ring
    _ ≤ 160*((2*volume axis ∅)*s.params.w)+((2*volume axis ∅)/L)*haloUnit s.params.V :=
      Nat.add_le_add (Nat.mul_le_mul_left 160 (Nat.mul_le_mul_right _ hv.le)) (Nat.mul_le_mul_right _ hpage)
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Routing.HaloStreamResource
