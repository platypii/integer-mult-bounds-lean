module

public import IntegerMultBounds.MathlibTM2.Routing.HaloScheduleResource

/-! Polynomial setup room for the manuscript's dyadic p^8 core and 4096*p^3
halo. Encoded-width and coarse-count bounds remain obligations of actual axis
sizing; the estimates here introduce no execution or budget suppliers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloManuscriptSizing
open HaloStageResource HaloStreamResource IntegerMultBounds.MathlibTM2.Fast.TableVM

def core (p : ℕ) := 2^Nat.clog 2 (p^8)
def halo (p : ℕ) := 4096*p^3

theorem core_bounds (p : ℕ) (hp : 0 < p) : p^8 ≤ core p ∧ core p < 2*p^8 :=
  GeneratedFiberPadding.dyadic_capacity_bounds _ (pow_pos hp _)

theorem units_le (q V K D : ℕ) (hq : 0 < q) (hV : V ≤ q) (hK : K ≤ q) (hD : D ≤ q) :
    timeUnit K K V D ≤ 100000*q^2 ∧ stockUnit V D ≤ 100000*q^2 := by
  have hq2 : q ≤ q^2 := by nlinarith
  have hV2 : V*V ≤ q*q := Nat.mul_le_mul hV hV
  have hDV : D*V ≤ q*q := Nat.mul_le_mul hD hV
  have hV' := hV.trans hq2
  have hK' := hK.trans hq2
  have hD' := hD.trans hq2
  have hone : 1 ≤ q^2 := by nlinarith
  dsimp only [timeUnit,stockUnit,haloUnit,metadataUnit,tblC]
  constructor <;> nlinarith only [hV2,hDV,hV',hK',hD',hone]

theorem setup_room (p V K D : ℕ) (hp : 32 ≤ p)
    (hV : V ≤ p^2) (hK : K ≤ p^2) (hD : D ≤ p^2) :
    timeUnit K K V D ≤ core p ∧ stockUnit V D ≤ core p := by
  have hp0 : 0 < p := by omega
  have h := units_le (p^2) V K D (pow_pos hp0 _) hV hK hD
  have hcut : 100000 ≤ p^4 := by
    have hh := Nat.pow_le_pow_left hp 4
    norm_num at hh
    omega
  have hpoly : 100000*(p^2)^2 ≤ p^8 := by
    calc
      _ ≤ p^4*(p^2)^2 := Nat.mul_le_mul_right _ hcut
      _ = _ := by ring
  exact ⟨h.1.trans (hpoly.trans (core_bounds p hp0).1),
    h.2.trans (hpoly.trans (core_bounds p hp0).1)⟩

theorem halo_room (p d : ℕ) (hp : 32 ≤ p) (hd : d ≤ p) : 64*d*halo p ≤ core p := by
  have hp0 : 0 < p := by omega
  have hcut : 262144 ≤ p^4 := by
    have hh := Nat.pow_le_pow_left hp 4
    norm_num at hh
    omega
  calc
    _ ≤ 64*p*halo p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hd)
    _ = 262144*p^4 := by dsimp only [halo]; ring
    _ ≤ p^4*p^4 := Nat.mul_le_mul_right _ hcut
    _ = p^8 := by ring
    _ ≤ core p := (core_bounds p hp0).1

/-- Retained halos require only a logarithmic local routing exponent. -/
theorem routingExponent_le (p : ℕ) (hp : 32 ≤ p) :
    Nat.clog 2 (core p+2*halo p) ≤ 9*(Nat.log 2 p+1) := by
  have hpow : p ≤ 2^(Nat.log 2 p+1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le
  have hk : Nat.clog 2 (p^8) ≤ 8*(Nat.log 2 p+1) := by
    apply Nat.clog_le_of_le_pow
    calc
      p^8 ≤ (2^(Nat.log 2 p+1))^8 := Nat.pow_le_pow_left hpow 8
      _ = 2^(8*(Nat.log 2 p+1)) := by rw [←pow_mul]; congr 1; omega
  have hgap : 2*halo p ≤ core p := by
    have hh := halo_room p 1 hp (by omega)
    omega
  have hr : Nat.clog 2 (core p+2*halo p) ≤ Nat.clog 2 (p^8)+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    change core p+2*halo p ≤ core p*2
    omega
  omega

/-- Both moves use least dyadic padding, hence share the return exponent.
The coarse dimension is never padded. -/
theorem padding_room (p : ℕ) (hp : 32 ≤ p) :
    let L := core p
    let H := halo p
    let k := Nat.clog 2 L
    let r := Nat.clog 2 (L+2*H)
    2^k ≤ 2*L ∧ 2^r ≤ 2*(L+2*H) ∧ k ≤ r ∧ r ≤ p^2 := by
  have hp0 : 0 < p := by omega
  have hL : 0 < core p := Nat.two_pow_pos _
  have hgap : 2*halo p ≤ core p := by
    have hh := halo_room p 1 hp (by omega)
    omega
  have hk : Nat.clog 2 (p^8) ≤ 8*p := by
    apply Nat.clog_le_of_le_pow
    calc
      p^8 ≤ (2^p)^8 := Nat.pow_le_pow_left (HaloSetupResource.self_le_two_pow p) 8
      _ = 2^(8*p) := by rw [←pow_mul]; congr 1; omega
  have hr : Nat.clog 2 (core p+2*halo p) ≤ Nat.clog 2 (p^8)+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    change core p+2*halo p ≤ core p*2
    omega
  have hkr : Nat.clog 2 (core p) ≤ Nat.clog 2 (core p+2*halo p) := Nat.clog_mono_right 2 (by omega)
  have hquad : 8*p+1 ≤ p^2 := by nlinarith
  exact ⟨(GeneratedFiberPadding.dyadic_capacity_bounds _ hL).2.le,
    (GeneratedFiberPadding.dyadic_capacity_bounds _ (by omega)).2.le,hkr,hr.trans (by omega)⟩

/-- The actual schedule budgets with polynomial setup room discharged.
Only ordinary dimension, encoding-width and least-padding facts remain. -/
theorem stage_budgets {ι : Type} [DecidableEq ι] [Fintype ι]
    (axis : ι → RetainedHaloTensor.Axis) (axes : List ι) (hn : axes.Nodup)
    (hall : ∀ i, i ∈ axes) (stages : List (HaloAxisSchedule.Stage ι)) (p w V : ℕ)
    (hp : 32 ≤ p) (hd : Fintype.card ι ≤ p) (hV : V ≤ p^2)
    (hD : 2*axes.length ≤ p^2)
    (hL : ∀ i, (axis i).L = core p) (hH : ∀ i, (axis i).H = halo p)
    (horder : ∀ s ∈ stages, s.left++s.i::s.right = axes)
    (hparams : ∀ s ∈ stages, s.params.w = w ∧ s.params.V = V)
    (hready : ∀ done s todo, stages = done++s::todo →
      HaloAxisSchedule.Ready axis (HaloAxisSchedule.after ∅ done) s)
    (hsizing : ∀ s ∈ stages, s.params.L ≤ s.params.N ∧
      s.params.k = Nat.clog 2 s.params.L ∧
      s.params.r = Nat.clog 2 (s.params.L+2*s.params.H)) :
    ∀ done s todo, stages = done++s::todo →
      HaloAxisSchedule.time axis (HaloAxisSchedule.after ∅ done) s ≤
        (RetainedHaloTensor.volume axis ∅*w)*(992*Nat.clog 2 (core p+2*halo p)+6654) ∧
      HaloAxisSchedule.reserve axis (HaloAxisSchedule.after ∅ done) s ≤
        17320*(RetainedHaloTensor.volume axis ∅*w) := by
  have hp0 : 0 < p := by omega
  have hpad := padding_room p hp
  have hroom := setup_room p V (Nat.clog 2 (core p+2*halo p)) (2*axes.length) hp hV hpad.2.2.2 hD
  apply HaloScheduleResource.stage_budgets axis axes hn hall stages w V (core p) (halo p)
    (Nat.clog 2 (core p+2*halo p)) hL hH (Nat.two_pow_pos _) (halo_room p _ hp hd)
    horder hparams hready _ hroom.1 hroom.2
  intro s hs
  obtain ⟨done,todo,heq⟩ := List.mem_iff_append.mp hs
  have hr := hready done s todo heq
  have hLs : s.params.L = core p := by
    simpa only [hr.axis_eq,HaloAxisTensorInvariant.axisOf] using hL s.i
  have hHs : s.params.H = halo p := by
    simpa only [hr.axis_eq,HaloAxisTensorInvariant.axisOf] using hH s.i
  rcases hsizing s hs with ⟨hcoarse,hk,hrpad⟩
  refine ⟨hcoarse,?_,?_,?_,?_⟩
  · simpa only [hk,hLs] using hpad.1
  · simpa only [hrpad,hLs,hHs] using hpad.2.1
  · simpa only [hk,hLs] using hpad.2.2.1
  · simp only [hrpad,hLs,hHs,le_refl]

end IntegerMultBounds.MathlibTM2.Routing.HaloManuscriptSizing
