module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearRun
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.BankHeads
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegmentSpace
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CounterCostBounds
public import IntegerMultBounds.Machine.SharedBankFamilyWithin
public import IntegerMultBounds.Machine.RawHeadMargin
public import IntegerMultBounds.Machine.HoareHeadChange


/-!
# The atomwise shears on the core's bank

A shear of the top view `u` of `n` atoms of `w` digits runs in three pieces (`program`): a
straight-line routine sets the segment's counters, `n` atoms and the loop count `n - 1`, from the
width header and the atom width (`setList`); the segment's chain runs on the role data
(`NodeSegment.place`); the counters are erased (`cleanList`). `shear_phase`: on the core's bank the
shear moves the array by the atomwise shear `d ← s h d` of `Stage2Wrapper`, within
`C (n + 1) V`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearWithin

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedBankFamily (padProgram)
open FlatCoordinateSchedule (bits)
open Stage2Wrapper (Moves shear)
open RevMachine
open RevMachine.AtomRoleSegment (SOp chain chainData chainConst bankSize tapesOf)
open CommonBank (count)
open Core (Phase)
open Place (memo Slot sel)
open Straight (Instr State words execs Pres costs)
open Switch (B placed)

local instance (w : ℕ) : NeZero (prime ^ w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

local instance (w : ℕ) : NeZero (modulus w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

open ShearRun

def coefficient (l : List (SOp 1)) : ℕ := AtomRoleSegment.chainSpace io l+200004

variable {f : ℤ → Fin (prime+4)} {p : ℤ} {node : Tapes 1 prime} {E : ℕ} {st : Tapes 2 prime}

theorem shear_phase {N : ℕ} (hN₁ : count tR + 22 ≤ N) (hN₂ : count tR + (T' + 2) ≤ N)
    {u : Descriptor} {w n : ℕ} (hp : u.Positive) (hw : 0 < w) (hwn : u.width = n * w) (hn : 1 ≤ n)
    (l : List (SOp 1)) (hl : ∀ s ∈ l, tapesOf io s ≤ T')
    {g : ZMod (modulus w) → ZMod (modulus w) → ZMod (modulus w)} (hlin : ShearSem.Lin (f := n) (b := w) l g)
    {s : Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n}
    (hs : ∀ h d, ShearSem.lift g n h d = s (Stage2Wrapper.dec (prime ^ w) n h) (Stage2Wrapper.dec (prime ^ w) n d)) (lo upper : ℤ)
    (hmargin : ∀ X j, lo+(coefficient l*volume prime u : ℕ) ≤
      (B f p node E (Prepare.rest w 529) st N u X).head j ∧
      (B f p node E (Prepare.rest w 529) st N u X).head j+
        (coefficient l*volume prime u : ℕ) ≤ upper) :
    Core.PhaseWithin (program hN₁ hN₂ l hl) (B f p node E (Prepare.rest w 529) st N) u u
      (Moves prime u (shear (prime ^ w) n s)) (cost l u w n) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  intro X
  have hf : 0 < n := hn
  have hw' : u.width = (1*n)*w := by rw [one_mul]; exact hwn
  let data := data₀ u X
  let initial := CommonBank.bank (RecursiveRoleSerialization.roles data) (Routines.hdr u) f p node
    (memo E) (Prepare.rest w 529) st
  let prepared := CommonBank.bank (RecursiveRoleSerialization.roles data) (Routines.hdr u) f p node
    (memo E) (segC w n) st
  let returned := CommonBank.bank (RecursiveRoleSerialization.roles (chainData hf io u hw' l data))
    (Routines.hdr u) f p node (memo E) (segC w n) st
  have hch := AtomRoleSegment.chain_hoare hw T' hf io u hw' hp (Routines.hdr u) (Routines.hdr_headers u) l hl data
  have hseg := NodeSegment.seg_runs (fs := f) (p := p) (node := node) (scalar := memo E) (st := st) T'_ge
    (Routines.hdr u) (segCounters w n)
    (hch.consequence (fun _ h => h) (fun _ h => h) (AtomRoleSegment.chainCost_le hw hf io u hw' hp l))
  have h₁ := SharedBankFamily.pad_realizes hN₁ (Nat.le_add_right _ _) _ _ _
    (set_runs (f := f) (p := p) (node := node) (E := E) (st := st) (RecursiveRoleSerialization.roles data) u hw hwn hn)
  have h₃ := SharedBankFamily.pad_realizes hN₁ (Nat.le_add_right _ _) _ _ _
    (clean_runs (f := f) (p := p) (node := node) (E := E) (st := st) (RecursiveRoleSerialization.roles
      (chainData hf io u hw' l data)) (Routines.hdr u) w n)
  have hV := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le u hp
  have hbound := ShearRun.boundary_costs hp hw hwn hn
  have hreserve : costs prime setList (setIn u.width w)+
      (AtomRoleSegment.chainSpace io l+4)*volume prime u+costs prime cleanList (cleanIn n) ≤
      coefficient l*volume prime u := by
    dsimp only [coefficient]
    rw [Nat.add_mul]
    nlinarith only [hbound]
  have hin : ∀ j, lo+(coefficient l*volume prime u : ℕ) ≤ (raw initial N).head j ∧
      (raw initial N).head j+(coefficient l*volume prime u : ℕ) ≤ upper := by
    simpa only [B,Leaf.leafBank,rolesAt_data₀,initial,data] using hmargin X
  have hw₁ := HoareWithin.of_time_heads h₁ lo upper (by
    rintro z rfl j
    have hm := hin j
    change lo+_ ≤ (raw initial N).head j ∧ (raw initial N).head j+_ ≤ upper
    omega)
  have hprepared : ∀ j, lo+((AtomRoleSegment.chainSpace io l+4)*volume prime u : ℕ) ≤
      (raw prepared N).head j ∧ (raw prepared N).head j+
        ((AtomRoleSegment.chainSpace io l+4)*volume prime u : ℕ) ≤ upper := by
    intro j
    have ht := h₁.head_change j
    change (raw initial N).head j-_ ≤ (raw prepared N).head j ∧
      (raw prepared N).head j ≤ (raw initial N).head j+_ at ht
    have hm := hin j
    omega
  have hraw := SharedBankStageInput.raw_margin_of_padding prepared (by omega : count tR < N) hprepared
  have hzero := hraw (count tR+1) (Fin.last (count tR))
  simp only [raw,Fin.val_last,lt_self_iff_false,↓reduceDIte] at hzero
  have hlo : lo ≤ 0 := by omega
  have hupper : 0 ≤ upper := by omega
  have hnV : n ≤ volume prime u :=
    (show n ≤ u.width from by rw [hwn]; exact Nat.le_mul_of_pos_right _ hw).trans (Switch.width_le hp)
  have hbits := RevBudget.bits_len (n-1)
  have hspace : NodeSegment.segmentSpace io l n (volume prime u) ≤
      (AtomRoleSegment.chainSpace io l+4)*volume prime u := by
    unfold NodeSegment.segmentSpace
    rw [Nat.add_mul]
    omega
  have hlocal : ∀ z, RunInvariant (chainP l hl).program
      (· = raw prepared (count tR+(T'+2))) z → ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper := by
    intro z hz j
    have hh := NodeSegment.segment_heads T'_ge io l hl hw hf u hw' hp (Routines.hdr u)
      (Routines.hdr_headers u) f p node (memo E) (segC w n) st (segCounters w n) data hz j
    have hm := hraw (count tR+(T'+2)) j
    change (raw prepared (count tR+(T'+2))).head j-_ ≤ z.head j ∧
      z.head j ≤ (raw prepared (count tR+(T'+2))).head j+_ at hh
    omega
  have hw₂ : HoareWithin (padProgram (chainP l hl).program hN₂)
      (· = raw prepared N) (· = raw returned N) (chainConst io l*n*volume prime u)
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
    rintro z rfl
    obtain ⟨m,hm,d,hr,hh,hout⟩ := SharedBankFamily.pad_within_heads (chainP l hl).program hN₂
      (Nat.le_add_right _ _) _ _ _ hseg lo upper hlo hupper hlocal
    exact ⟨m,hm,d,hr,hh,hout⟩
  have hheads : (raw returned N).head = (raw prepared N).head :=
    SharedBankStageInput.raw_head_congr (CommonBank.bank_head_congr _ _ _ _ f p node (memo E) (segC w n) st rfl) N
  have hw₃ := HoareWithin.of_time_heads h₃ lo upper (by
    rintro z rfl j
    change lo+_ ≤ (raw returned N).head j ∧ (raw returned N).head j+_ ≤ upper
    rw [hheads]
    have ht := h₁.head_change j
    change (raw initial N).head j-_ ≤ (raw prepared N).head j ∧
      (raw prepared N).head j ≤ (raw initial N).head j+_ at ht
    have hm := hin j
    omega)
  have hsafe := (hw₁.seq hw₂).seq hw₃
  apply HoareWithin.of_time_invariant ((ShearRun.shear_phase hN₁ hN₂ hp hw hwn hn l hl hlin hs) X)
  intro z hz
  apply hsafe.invariant
  obtain ⟨v,hv,m,hr⟩ := hz
  refine ⟨v,?_,m,hr⟩
  rw [hv,B,Leaf.leafBank,rolesAt_data₀]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearWithin
