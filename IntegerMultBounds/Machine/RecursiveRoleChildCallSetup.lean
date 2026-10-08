import IntegerMultBounds.Machine.RecursiveChildSetupRoleBank
import IntegerMultBounds.Machine.RecursiveCrossPrepare
import IntegerMultBounds.Machine.RecursiveChildReturnRoleBank

/-! Recursive call entry after the parent row split. Supplied headers already
describe one role array: save those headers and the return PC, then construct
the cross-group child with divisor one. No second row division occurs. -/
namespace IntegerMultBounds.Machine.RecursiveRoleChildCallSetup
noncomputable section
open RecursiveInterchangeLayout (Descriptor child volume)
open RecursiveChildCallSetup (bank fields words descriptorStack pcStack savedStacks)
open Networks
open Shared50ModularControl (prime)
variable {q k t u : ℕ}

def program (hq : 2 ≤ q) {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  seq (RecursiveFrameControl.callProgram (a := q) descriptorStack fields pcStack code)
    (extend (RecursiveCrossPrepare.program hq i j) 2)

def constant (m k : ℕ) := RecursiveCrossPrepare.constant m+k+74

/-- The child's rows equal the already-split role parent's rows. -/
theorem child_rows (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m) :
    (child q 1 b v i j).rows = v.rows := by simp [child]

/-- Physical role-header/PC saving and same-row child construction. The
runtime volume is that of the role, not the unsplit network's parent array. -/
theorem prepares (hq : 2 ≤ q) (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child q 1 b v i j) ch ∧
      HoareTime (program hq i j code) (fun w => w = bank hs st)
        (fun w => w = bank ch (savedStacks hs st code)) (constant m k*volume q v) := by
  obtain ⟨ch,hch,hcross⟩ := RecursiveCrossPrepare.prepares hq b v i j hw hp hs hv
  have hsave := RecursiveChildCallSetup.save_hoare hs st code
  have hprepare := hoare_extend_eq hcross (savedStacks hs st code)
  have hjoin := hsave.seq hprepare
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hlen (z : Fin 6) : (hs z).length ≤ 2*volume q v := by
    have hl := RecursiveAffinePrepare.header_log hq v hp hs hv z
    have hl' := Nat.log2_le_self (volume q v)
    omega
  have hcost := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words hs)
    (2*volume q v) (by
      intro op hop
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hlen z)
  refine ⟨ch,hch,hjoin.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold constant
  nlinarith

/-- The permanent bank is exactly the one used by physical header return.
All role arrays, shared scratch, and auxiliary tapes are literal spectators. -/
def placedProgram {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  Placement.placed (program Shared50ModularControl.prime_prime.two_le i j code)
    (CleanSubbank.placement RecursiveChildSetupRoleBank.ports
      (RecursiveChildSetupRoleBank.commonPorts (t := t) (u := u)) RecursiveChildSetupRoleBank.commonPorts_injective)

theorem placed_prepares (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (roles : Tapes t prime) (aux : Tapes u prime)
    (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child prime 1 b v i j) ch ∧
      HoareTime (placedProgram (t := t) (u := u) i j code)
        (fun w => w = CleanSubbank.bank (RecursiveShiftRoleBank.common roles hs (aux.append st)))
        (fun w => w = CleanSubbank.bank
          (RecursiveShiftRoleBank.common roles ch (aux.append (savedStacks hs st code))))
        (constant m k*volume prime v) := by
  obtain ⟨ch,hch,h⟩ := prepares Shared50ModularControl.prime_prime.two_le b v i j hw hp hs hv st code
  exact ⟨ch,hch,RecursiveChildSetupRoleBank.placed_hoare _ roles hs ch aux st _ h⟩

/-- The matching role-parent return is also linear without requiring either
layout to be an original unsplit root-path node. -/
theorem restore_cost_le (hq : 2 ≤ q) (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs ch : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (hc : RecursiveDimensionBank.Headers (child q 1 b v i j) ch) :
    RecursiveChildCallReturn.cost hs ch ≤ 127*volume q v := by
  have hq' : 0 < q := by omega
  have hchild : (child q 1 b v i j).Positive := by
    rcases hp with ⟨hA,hR,hB,hC,hE⟩
    dsimp [Descriptor.Positive,child]
    rw [Nat.div_one]
    exact ⟨hA,hR,Nat.mul_pos hB (pow_pos hq' _),
      Nat.mul_pos (Nat.mul_pos (pow_pos hq' _) hC) (pow_pos hq' _),Nat.mul_pos (pow_pos hq' _) hE⟩
  have hvol : volume q (child q 1 b v i j) = volume q v := RecursiveAffineViews.cross_volume q b v i j hw
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hold (z : Fin 6) : (hs z).length ≤ 2*volume q v := by
    have h := RecursiveAffinePrepare.header_log hq v hp hs hv z
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hnew (z : Fin 6) : (ch z).length ≤ 2*volume q v := by
    have h := RecursiveAffinePrepare.header_log hq _ hchild ch hc z
    rw [hvol] at h
    have hl := Nat.log2_le_self (volume q v)
    omega
  have hpop := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words hs)
    (2*volume q v) (by
      intro op hop
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hold z)
  have hclear := BinaryDescriptorCleanupList.cost_le (BinaryDescriptorFrameRestore.slots fields) (words ch)
    (2*volume q v) (by
      intro z hz
      obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hnew i)
  have hlen : (BinaryDescriptorFrameRestore.slots fields).length = 6 := by
    simp [BinaryDescriptorFrameRestore.slots,fields]
  rw [hlen] at hclear
  unfold RecursiveChildCallReturn.cost
  omega

theorem placed_restores (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs ch : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs)
    (hc : RecursiveDimensionBank.Headers (child prime 1 b v i j) ch)
    (roles : Tapes t prime) (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k)
    (hd : RecursiveStackAllocation.Available 0 st) :
    HoareTime (RecursiveChildReturnRoleBank.restoreProgram (t := t) (u := u))
      (fun w => w = RecursiveChildReturnRoleBank.bank roles ch aux (savedStacks hs st code))
      (fun w => w = RecursiveChildReturnRoleBank.bank roles hs aux (RecursiveChildCallReturn.pending st code))
      (127*volume prime v) :=
  (RecursiveChildReturnRoleBank.restores roles hs ch aux st code hd).consequence
    (fun _ h => h) (fun _ h => h)
    (restore_cost_le Shared50ModularControl.prime_prime.two_le b v i j hw hp hs ch hv hc)


end
end IntegerMultBounds.Machine.RecursiveRoleChildCallSetup
