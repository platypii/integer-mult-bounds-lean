module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
public import IntegerMultBounds.Machine.RunInvariant
public import IntegerMultBounds.Machine.RecursiveInterchangeVolume

/-! Concrete preparation has linear-volume time and head bounds. Finish restores the counters, and the actual
test block supplies state-sensitive controller readiness from runtime counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl RecursiveInterchangeLayout RecursiveInterchangeVolume
  FlatCoordinateSchedule CommonBank Routines SharedBankStageInput
noncomputable section

theorem width_square_le_volume (v : Descriptor) (hv : v.Positive) :
    (v.width+1)^2 ≤ volume prime v := by
  have hpow : v.width+1 ≤ prime^v.width := Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt
  calc
    _ ≤ (prime^v.width)^2 := Nat.pow_le_pow_left hpow 2
    _ = prime^(2*v.width) := by rw [← pow_mul]; congr 1; omega
    _ ≤ nonrowVolume prime v := original_chunks_lower prime v hv
    _ ≤ volume prime v := by
      rw [volume_factor]
      exact Nat.le_mul_of_pos_left _ hv.2.1

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
  exact hcost.trans (Nat.mul_le_mul_left _ (width_square_le_volume v hv))

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

theorem finishCost_length (m n : ℕ) : finishCost m n ≤ 4*n+18 := by
  have h := GrowingCounterData.canonical_width (bits n) (bits_canonical n)
  have h' := GrowingCounterData.canonical_width (bits (n/m)) (bits_canonical (n/m))
  rw [bits_value] at h h'
  have hn := Nat.log2_le_self n
  have hd := Nat.log2_le_self (n/m)
  have hm := Nat.div_le_self n m
  have hz : (bits 0).length = 0 := rfl
  unfold finishCost
  rw [hz]
  omega

/-- Counter retirement restores the ordinary preparation bank. Its execution
uses linear active-volume head intervals on all tapes. -/
theorem finish_heads {T : ℕ} (v : Descriptor) (hv : v.Positive) (b m n : ℕ)
    (hb : 0 < b) (hw : v.width = n*b)
    (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    {c : Config (Prepare.finish (t := T)).tapes (Prepare.finish (t := T)).states prime}
    (hc : RunInvariant (Prepare.finish (t := T)).program
      (· = raw (bank roles (hdr v) f p node scalar (leafC b m n 0) st) (Prepare.finish (t := T)).tapes) c) :
    ∀ i,
      (raw (bank roles (hdr v) f p node scalar (leafC b m n 0) st) (Prepare.finish (t := T)).tapes).head i-
          (22*volume prime v : ℕ) ≤ c.head i ∧
      c.head i ≤ (raw (bank roles (hdr v) f p node scalar (leafC b m n 0) st) (Prepare.finish (t := T)).tapes).head i+
          (22*volume prime v : ℕ) := by
  have hnwidth : n ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_right _ hb
  have hnv : n ≤ volume prime v := hnwidth.trans
    ((show v.width ≤ (v.width+1)^2 by nlinarith).trans (width_square_le_volume v hv))
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  have hcost : finishCost m n ≤ 22*volume prime v := by have h := finishCost_length m n; omega
  have h := Prepare.finish_runs (roles := roles) (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := leafC b m n 0) (by rfl) (by rfl) (by rfl)
  have h' := h.consequence (fun _ h => h) (fun _ h => h) hcost
  exact hc.heads_eq h'

theorem finish_reachable_post {T b m n : ℕ}
    (roles : Tapes T prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    {c : Config (Prepare.finish (t := T)).tapes (Prepare.finish (t := T)).states prime}
    (hc : RunInvariant (Prepare.finish (t := T)).program
      (· = raw (bank roles hs f p node scalar (leafC b m n 0) st) (Prepare.finish (t := T)).tapes) c)
    (hh : Machine.step (Prepare.finish (t := T)).program c = none) :
    c.tapes = raw (bank roles hs f p node scalar (Prepare.rest b m) st) (Prepare.finish (t := T)).tapes := by
  apply RunInvariant.post (k := finishCost m n)
    (post := fun x => x = raw (bank roles hs f p node scalar (Prepare.rest b m) st) (Prepare.finish (t := T)).tapes) ?_ hc hh
  have h := Prepare.finish_runs (roles := roles) (hs := hs) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := leafC b m n 0) (by rfl) (by rfl) (by rfl)
  simpa only [finish_counters,finishCost,GraphContract.Runs] using h

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
