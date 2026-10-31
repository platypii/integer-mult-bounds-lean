module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
public import IntegerMultBounds.Machine.RunInvariant
public import IntegerMultBounds.Machine.RecursiveInterchangeVolume

/-! Concrete preparation has linear-volume time and head bounds. The actual
test block supplies state-sensitive controller readiness from runtime counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl RecursiveInterchangeLayout RecursiveInterchangeVolume
  FlatCoordinateSchedule CommonBank Routines SharedBankStageInput
noncomputable section

theorem prepCost_linear (v : Descriptor) (hv : v.Positive) (b m n : ℕ)
    (hb : 0 < b) (hn : 1 ≤ n) (hw : v.width = n*b) :
    prepCost b m n ≤ (4000+BinaryDescriptorDivMod.linearConstant (bits m))*volume prime v := by
  have hbwidth : b ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_left _ hn
  have hnwidth : n ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_right _ hb
  have hbits := GrowingCounterData.canonical_width (bits b) (bits_canonical b)
  rw [bits_value] at hbits
  have hblen : (bits b).length ≤ v.width+1 := by have h := Nat.log2_le_self b; omega
  have hCb : BinaryDescriptorDivMod.linearConstant (bits b) ≤ 3818*(v.width+1) := by
    unfold BinaryDescriptorDivMod.linearConstant
    nlinarith only [hblen]
  have hfirst := Nat.mul_le_mul_right (v.width+1) hCb
  have hwsq : v.width+1 ≤ (v.width+1)^2 := by nlinarith only [Nat.zero_le v.width]
  have hsecond := Nat.mul_le_mul_left (BinaryDescriptorDivMod.linearConstant (bits m))
    ((Nat.add_le_add_right hnwidth 1).trans hwsq)
  have hcost : prepCost b m n ≤
      (4000+BinaryDescriptorDivMod.linearConstant (bits m))*(v.width+1)^2 := by
    unfold prepCost
    rw [← hw]
    nlinarith only [hfirst,hsecond,hbwidth,Nat.zero_le v.width]
  have hpow : v.width+1 ≤ prime^v.width := Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt
  have hsquare : (v.width+1)^2 ≤ volume prime v := by
    calc
      _ ≤ (prime^v.width)^2 := Nat.pow_le_pow_left hpow 2
      _ = prime^(2*v.width) := by rw [← pow_mul]; congr 1; omega
      _ ≤ nonrowVolume prime v := original_chunks_lower prime v hv
      _ ≤ volume prime v := by
        rw [volume_factor]
        exact Nat.le_mul_of_pos_left _ hv.2.1
  exact hcost.trans (Nat.mul_le_mul_left _ hsquare)

/-- The run invariant of the actual preparation block has fixed head intervals
linear in its active descriptor volume, on every private and common tape. -/
theorem prepare_heads {T : ℕ} (v : Descriptor) (hv : v.Positive) (b m n : ℕ)
    (hb : 0 < b) (hm : 0 < m) (hn : 1 ≤ n) (hw : v.width = n*b)
    (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    {c : Config (prepare (T := T)).tapes (prepare (T := T)).states prime}
    (hc : RunInvariant (prepare (T := T)).program
      (· = raw (bank roles (hdr v) f p node scalar (Prepare.rest b m) st) (prepare (T := T)).tapes) c) :
    ∀ i,
      (raw (bank roles (hdr v) f p node scalar (Prepare.rest b m) st) (prepare (T := T)).tapes).head i-
          ((4000+BinaryDescriptorDivMod.linearConstant (bits m))*volume prime v : ℕ) ≤ c.head i ∧
      c.head i ≤ (raw (bank roles (hdr v) f p node scalar (Prepare.rest b m) st) (prepare (T := T)).tapes).head i+
          ((4000+BinaryDescriptorDivMod.linearConstant (bits m))*volume prime v : ℕ) := by
  have h := prepare_runs (roles := roles) (f := f) (p := p) (node := node) (scalar := scalar) (st := st) hb hm hw
  have h' := h.consequence (fun _ h => h) (fun _ h => h) (prepCost_linear v hv b m n hb hn hw)
  exact hc.heads_eq h'

/-- The real test block returns its unchanged bank and the finite exit state
selected by the actual leaf and atom counters. -/
theorem test_reachable_post {T b m n r : ℕ} (hm : 0 < m)
    (roles : Tapes T prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    {c : Config (test (T := T)).tapes (test (T := T)).states prime}
    (hc : RunInvariant (test (T := T)).program
      (· = raw (bank roles hs f p node scalar (leafC b m n r) st) (test (T := T)).tapes) c)
    (hh : Machine.step (test (T := T)).program c = none) :
    c.tapes = raw (bank roles hs f p node scalar (leafC b m n r) st) (test (T := T)).tapes ∧
      Guard.exit c.state = (if r ≠ 0 then .leaf else if m ≤ n then .node else .done) := by
  apply RunInvariant.post_config (post := fun z =>
    z.tapes = raw (bank roles hs f p node scalar (leafC b m n r) st) (test (T := T)).tapes ∧
      Guard.exit z.state = (if r ≠ 0 then .leaf else if m ≤ n then .node else .done)) ?_ hc hh
  intro v hv
  subst v
  obtain ⟨st',hexit,hrun,hhalt⟩ := test_runs (roles := roles) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (b := b) (n := n) (r := r) hm hs
  exact ⟨1,_,hrun,hhalt,rfl,hexit⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
