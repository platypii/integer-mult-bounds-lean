module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRun
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.AssemblyWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearWithin

/-! The actual nine-phase core reuses one volume reserve. Boundary heads are
independent of views and payloads; only fixed phase coefficients enter the maximum. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRunWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open Stage2Wrapper (top low)
open FlatCoordinateSchedule (bits)
open RevMachine
open Assembly (tW bank wOf nOf rOf switch_le shear_le)
noncomputable section
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- A finite maximum of fixed machine coefficients, independent of input shape. -/
def coefficients (k cutoff : ℕ) : Fin 6 → ℕ :=
  ![FamilyStepWithin.coefficient k cutoff,
    M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff,
    ShearWithin.coefficient ShearSem.ops₁,ShearWithin.coefficient ShearSem.ops₂,
    ShearWithin.coefficient ShearSem.ops₃,10001*72]

def coefficient (k cutoff : ℕ) : ℕ := Finset.univ.sup (coefficients k cutoff)

theorem coefficient_le (k cutoff : ℕ) (i : Fin 6) : coefficients k cutoff i ≤ coefficient k cutoff :=
  Finset.le_sup (Finset.mem_univ i)

local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem core_phase (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (K : ℕ) (hK : 2 ≤ K) (v : Descriptor) (hp : v.Positive) (he : 2 ≤ v.width)
    (hrows : rev97m.roleCount^RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (hpay : ∀ z, p ≤ z → f z = blank)
    (node : Tapes 1 prime) (hfree : Family.NodeFree node) (st : Tapes 2 prime)
    (hdesc : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (lo upper : ℤ)
    (hmargin : ∀ X j, lo+(coefficient k cutoff*volume prime v : ℕ) ≤
      (bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v X).head j ∧
      (bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v X).head j+
        (coefficient k cutoff*volume prime v : ℕ) ≤ upper) :
    ∃ c, Core.PhaseWithin (CoreRun.program capacity)
      (bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v)) v v
      (Stage2Wrapper.Moves prime v Prod.swap) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  let w := wOf K v
  let n := nOf K v
  let r := rOf K v
  have hw : 0 < w := Stage2Width.atomWidth_pos K _
  have hr : r ≤ v.width := Assembly.rOf_le K v
  have hn : 1 ≤ n := Assembly.nOf_pos hK he
  have htw : (top prime r v).width = n*w := Assembly.top_width K v
  have htop := Assembly.top_positive (r := r) Networks.Shared50ModularControl.prime_prime.pos hp
  have hlow := Assembly.low_positive (r := r) Networks.Shared50ModularControl.prime_prime.pos hp
  have hvt : volume prime (top prime r v) = volume prime v := Assembly.top_volume hr
  have hvl : volume prime (low prime r v) = volume prime v := Assembly.low_volume hr
  have margins (i : Fin 6) (u : Descriptor) : ∀ X j,
      lo+(coefficients k cutoff i*volume prime v : ℕ) ≤
        (bank capacity f p node (Place.memo v.width) (fun _ => st) w u X).head j ∧
      (bank capacity f p node (Place.memo v.width) (fun _ => st) w u X).head j+
        (coefficients k cutoff i*volume prime v : ℕ) ≤ upper := by
    intro X j
    rw [AssemblyWithin.bank_head_eq capacity f p node (Place.memo v.width) st w u v X X]
    have hm := hmargin X j
    change lo+_ ≤ (bank capacity f p node (Place.memo v.width) (fun _ => st) w v X).head j ∧
      (bank capacity f p node (Place.memo v.width) (fun _ => st) w v X).head j+_ ≤ upper at hm
    have hb := Nat.mul_le_mul_right (volume prime v) (coefficient_le k cutoff i)
    omega
  let L : ℝ := ((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau+(bits w).length+1
  have hpower : 0 ≤ ((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlength : (0 : ℝ) ≤ (bits w).length := Nat.cast_nonneg _
  obtain ⟨C,hC,hF⟩ := AssemblyWithin.fam_phase capacity cutoff hcut
  have hfamily := hF w L (by dsimp only [L]; linarith only [hpower,hlength]) (by dsimp only [L]; linarith only [hpower])
    (by dsimp only [L]; linarith only [hlength])
    (top prime r v) n htop hw htw hn hrows f p hpay node hfree (Place.memo v.width) st hdesc hpc lo upper
    (by rw [hvt]; exact margins 0 (top prime r v))
  have hleaf := AssemblyWithin.leaf_phase capacity cutoff hcut f p node (Place.memo v.width) st w
    (low prime r v) hlow lo upper (by rw [hvl]; exact margins 1 (low prime r v))
  have h₁ := (Switch.toTop_phase (f := f) (p := p) (node := node) (E := v.width) (st := st)
    (switch_le capacity) v hw).within_heads (D := 10001*72*volume prime v)
      (by have h := Switch.toTop_cost (w := w) hp (Stage2Width.atomWidth_le_self hK he); omega) lo upper (margins 5 v)
  have h₇ := (Switch.toLow_phase (f := f) (p := p) (node := node) (c := Prepare.rest w 529) (st := st)
    (switch_le capacity) v hr).within_heads (Switch.toLow_cost hp hr) lo upper (margins 5 (top prime r v))
  have h₉ := (Switch.back_phase (f := f) (p := p) (node := node) (c := Prepare.rest w 529) (st := st)
    (switch_le capacity) v hr).within_heads (D := 10001*72*volume prime v)
      (by have h := Switch.back_cost hp hr; omega) lo upper (margins 5 (low prime r v))
  have h₂ := ShearWithin.shear_phase (s := fun h d => d-h) (f := f) (p := p) (node := node) (E := v.width) (st := st)
    (switch_le capacity) (shear_le capacity) htop hw htw hn ShearSem.ops₁ ShearRun.fits₁ ShearSem.lin₁
    (ShearRun.hs₁ w n) lo upper (by rw [hvt]; exact margins 2 (top prime r v))
  have h₄ := ShearWithin.shear_phase (s := fun h d => d+h) (f := f) (p := p) (node := node) (E := v.width) (st := st)
    (switch_le capacity) (shear_le capacity) htop hw htw hn ShearSem.ops₂ ShearRun.fits₂ ShearSem.lin₂
    (ShearRun.hs₂ w n) lo upper (by rw [hvt]; exact margins 3 (top prime r v))
  have h₆ := ShearWithin.shear_phase (s := fun h d => h-d) (f := f) (p := p) (node := node) (E := v.width) (st := st)
    (switch_le capacity) (shear_le capacity) htop hw htw hn ShearSem.ops₃ ShearRun.fits₃ ShearSem.lin₃
    (ShearRun.hs₃ w n) lo upper (by rw [hvt]; exact margins 4 (top prime r v))
  exact ⟨_,Core.core_hoare_within hr htw h₁ h₂ hfamily h₄ hfamily h₆ h₇ hleaf h₉⟩

/-- The original exact transpose and certified runtime share this prefix bound. -/
theorem core_run (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) {K : ℕ} (hK : 2 ≤ K)
    (hs1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau) (hτ₁ : M8.Machine.BudgetBound.tau ≤ 1)
    (hhalf : 1 / 2 ≤ M8.Machine.BudgetBound.tau)
    (h2 : 1 / 2 ≤ Stage2Width.tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau)
    (hlin : 1 - (K : ℝ)⁻¹ ≤ Stage2Width.tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau) :
    ∃ C' : ℝ, ∀ v : Descriptor, v.Positive → 2 ≤ v.width →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K v) ∣ v.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ st : Tapes 2 prime,
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ (x : Fin (volume prime v) → ZMod 2) (lo upper : ℤ),
      (∀ j, lo+(coefficient k cutoff*volume prime v : ℕ) ≤
        (bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v (FamilyRoot.ext x)).head j ∧
        (bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v (FamilyRoot.ext x)).head j+
          (coefficient k cutoff*volume prime v : ℕ) ≤ upper) → ∃ c : ℕ,
        (c : ℝ) ≤ C' * volume prime v * (v.width : ℝ) ^ Stage2Width.tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau ∧
        HoareWithin (CoreRun.program capacity)
          (· = bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v (FamilyRoot.ext x))
          (· = bank capacity f p node (Place.memo v.width) (fun _ => st) (wOf K v) v
            (FamilyRoot.ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C,hC⟩ := CoreRun.core_run capacity (Spec.familySpec capacity) hK hs1 hτ₁ hhalf h2 hlin
  refine ⟨C,?_⟩
  intro v hp he hrows f p hpay node hfree st hdesc hpc x lo upper hm
  obtain ⟨c,hc,ht⟩ := hC v hp he hrows f p hpay node hfree st hdesc hpc x
  obtain ⟨m,hphase⟩ := core_phase capacity cutoff hcut K hK v hp he hrows f p hpay node hfree st hdesc hpc
    lo upper (by
      intro X j
      rw [AssemblyWithin.bank_head_eq capacity f p node (Place.memo v.width) st (wOf K v) v v X (FamilyRoot.ext x)]
      exact hm j)
  refine ⟨c,hc,?_⟩
  apply HoareWithin.of_time_invariant ht
  intro z hz
  exact (hphase (FamilyRoot.ext x)).invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreRunWithin
