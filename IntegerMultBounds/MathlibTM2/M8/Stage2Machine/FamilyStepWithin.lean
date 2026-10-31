module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStep
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRootWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreWithin
public import IntegerMultBounds.Machine.HoareHeadChange


/-!
# One run of the reversed family on the core's bank

The core's bank at a view `u` holds the bit array on the `io` role, the headers of `u`, the
family's resting counters `rest w 529` and the caller's stacks (`bankAt`). One family step
pushes the halt code on the PC stack and runs the family's machine (`program`): by the data
semantics of the family (`FamilySpec`) the frame of the pushed bank returns to the halt block
with the reversed interchange of the array and the stack popped, and halts (`family_step`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStepWithin

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open RecursiveInterchangeLayout (Descriptor volume index)
open SharedPlacementAlphabet (setTape)
open RevMachine
open RevMachine.Family (Frame NodeFree)
open RevMachine.RevHalf (pcs Ok)
open FamilyRoot (ext rolesOf machine entry padded bound FamilySpec impl)
open Core (Phase)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k)

open FamilyStep

def coefficient (k cutoff : ℕ) : ℕ := FamilyRootWithin.coefficient k cutoff+k

theorem family_step (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ (u : Descriptor) (n : ℕ), u.Positive → 0 < b₀ → u.width = n * b₀ → 1 ≤ n →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) n ∣ u.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), NodeFree node → ∀ (scalar : Tapes 1 prime) (st : Tapes 2 prime),
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ lo upper : ℤ,
      (∀ X j, lo+(coefficient k cutoff*volume prime u : ℕ) ≤
        (bankAt capacity f p node scalar st b₀ u X).head j ∧
        (bankAt capacity f p node scalar st b₀ u X).head j+
          (coefficient k cutoff*volume prime u : ℕ) ≤ upper) →
      Core.PhaseWithin (program capacity) (bankAt capacity f p node scalar st b₀) u u (RevT prime b₀ n u)
        (k + 1 + ⌊bound C L n * volume prime u⌋₊) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C, hC, hroot⟩ := FamilyRootWithin.root_hoare capacity cutoff hcut
  refine ⟨C, hC, fun b₀ L hL hℓ hτ u n hpos hb hw hn hrows f p hpay node hfree scalar st hdesc hpc lo upper hmargin X => ?_⟩
  set code := Graph.rootCode (pcs rev97m) capacity
  have hcode : Family.Coded (pushedStack capacity st)
      (FiniteReturnStack.address capacity (Graph.encoding (pcs rev97m) .halt)) (st.tape 1) (st.head 1) := by
    refine ⟨by simp [pushedStack, setTape]; rfl, by simp [pushedStack, setTape], fun j _ => hpc _ (by omega)⟩
  let σ : Frame (pcs rev97m) capacity :=
    { v := u, n := n, b := b₀, hpos := hpos, hb := hb, hw := hw, f := f, p := p, node := node,
      scalar := scalar, st := pushedStack capacity st, hfree := hfree, ret := .halt,
      g := st.tape 1, q := st.head 1, hcode := hcode }
  have hok : Ok rev97m b₀ σ :=
    { b := rfl
      rows := hrows
      pay := hpay
      desc := by
        intro z hz
        have : (pushedStack capacity st).head 0 = st.head 0 ∧ (pushedStack capacity st).tape 0 = st.tape 0 := by
          simp [pushedStack, setTape]
        rw [this.2]; rw [this.1] at hz; exact hdesc z hz
      pc := by
        intro z hz
        simp only [σ, pushedStack, setTape, Function.update_self] at hz ⊢
        unfold FiniteReturnStack.wordPart
        rw [dite_eq_right_iff.mpr (fun h => absurd h (by omega))]
        exact hpc z (by omega) }
  have h₁ := FiniteReturnStackAt.push_hoare (a := prime) (pcRaw capacity) code (bankAt capacity f p node scalar st b₀ u X)
  have hV := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le u hpos
  have hreserve : k+FamilyRootWithin.coefficient k cutoff*volume prime u ≤ coefficient k cutoff*volume prime u := by
    unfold coefficient
    rw [Nat.add_mul]
    have h := Nat.mul_le_mul_left k hV
    omega
  have hw₁ := HoareWithin.of_time_heads h₁ lo upper (by
    rintro z rfl j
    have hm := hmargin X j
    omega)
  have hprepared : ∀ j, lo+(FamilyRootWithin.coefficient k cutoff*volume prime u : ℕ) ≤
      (padded capacity (σ.at (rolesOf (v := u) (fun i => X i)) (Prepare.rest b₀ 529))).head j ∧
      (padded capacity (σ.at (rolesOf (v := u) (fun i => X i)) (Prepare.rest b₀ 529))).head j+
        (FamilyRootWithin.coefficient k cutoff*volume prime u : ℕ) ≤ upper := by
    intro j
    have ht := h₁.head_change j
    rw [push_bank] at ht
    change (bankAt capacity f p node scalar st b₀ u X).head j-(k : ℕ) ≤
      (padded capacity (σ.at (rolesOf (v := u) (fun i => X i)) (Prepare.rest b₀ 529))).head j ∧
      (padded capacity (σ.at (rolesOf (v := u) (fun i => X i)) (Prepare.rest b₀ 529))).head j ≤
        (bankAt capacity f p node scalar st b₀ u X).head j+(k : ℕ) at ht
    have hm := hmargin X j
    omega
  have h₂ := hroot b₀ L hL hℓ hτ σ hok hn rfl (fun i => X i) lo upper hprepared
  refine (hw₁.seq (h₂.consequence (fun z hz => ?_) (fun z hz => ?_) le_rfl (fun _ h => h))).consequence
    (fun _ h => h) (fun _ h => h) le_rfl (fun _ h => h)
  · rw [hz, push_bank]; rfl
  · obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨FamilyRoot.ext y, revT_of_ext hw (fun _ => rfl) hy, ?_⟩
    unfold bankAt
    rw [rolesAt_ext]
    change padded capacity (CommonBank.bank (rolesOf y) (Routines.hdr u) f p node scalar (Prepare.rest b₀ 529)
      (Family.popped (pushedStack capacity st) (st.tape 1) (st.head 1))) = _
    simp [Family.popped, pushedStack]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStepWithin
