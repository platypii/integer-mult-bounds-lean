module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyRun
public import IntegerMultBounds.MathlibTM2.M6.BitPortImage
public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Physical passes for the PR589 port-frame correction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Stack Host Cover.Fallback
open Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open M8.Machine.Segments IntegerMultBounds.Swap.Modular in
/-- The two port basis changes use fixed tape programs. Each maps both
eight-digit fields, preserves the spectator and costs at most a constant
times the payload volume, uniformly in the width. -/
theorem frameBasis_runs (l : Fin 636) (inverse : Bool) :
    ∃ stages : List (FlatCoordinateSchedule.Op 16), ∀ (w W : ℕ) (_hW : 0 < W)
      (x : Fin ((prime^w)^16*W) → ZMod 2),
      let bank := fun (y : Fin ((prime^w)^16*W) → ZMod 2) => SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
          (fun i => SparseRoleCircuit.encode (y i))) (FlatCoordinateCleanSchedule.tapeCount stages)
      let M := reduce (prime^w) (frameBasis l inverse)
      ∃ y, HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = bank x)
        (fun z => z = bank y) (FlatCoordinateCleanSchedule.constant stages * ((prime^w)^16*W)) ∧
        ∀ s j, y (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (M8.Exchange.transform M M s)) j) =
          x (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨pass,action⟩ := frameBasis_pass l inverse
  let B := frameBasis l inverse
  let ops := M8.Exchange.transformOps B B
  refine ⟨description ops pass.good,?_⟩
  intro w W hW x bank M
  obtain ⟨y,exec,reads⟩ := copySegment_runs ops pass.good hW x (pass.legal w)
  exact ⟨y,exec,fun s j => (action w s) ▸ reads s j⟩

/-- Packed action of the two digit transpositions, one per field. -/
def portSwapDigits {R : Type*} (x : Fin 16 → R) : Fin 16 → R :=
  x ∘ Equiv.swap 0 7 ∘ Equiv.swap 8 15

open Matrix in
theorem portSwapDigits_embed {R : Type*} [CommRing R] (s : IntegerMultBounds.Swap.Shear.State (Fin 8) R) :
    portSwapDigits (AffineFieldCoordinates.embed s) =
      AffineFieldCoordinates.embed (M8.Exchange.transform (portPivotSwap R) (portPivotSwap R) s) := by
  have swap (x : Fin 8 → R) : portPivotSwap R *ᵥ x = x ∘ Equiv.swap 0 (Fin.last 7) := by
    funext i
    simp [portPivotSwap,mulVec,dotProduct,ite_mul]
  rw [M8.Exchange.transform,swap,swap]
  funext i
  fin_cases i <;> rfl

local notation "N" => rowSwapBlock.tapes+35

/-- Swap digits zero and seven on both fields in the shared column bank.
Both calls restore their private workspace and the saved pivot stream. -/
theorem portPivotSwap_exec [M8.Machine.Net] {P U : Type} {w W : ℕ} (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U)
    (S : Stacks (N+1) prime) (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin ((prime^(w+1))^16*W) → ZMod 2)
    (addr : (Fin 16 → ZMod (prime^(w+1))) → Fin 16 → ZMod (prime^(w+1))) :
    let ready := ColumnRecordReady columnBank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ k : Fin N, 35 ≤ k.val →
      D.L (columnPorts k) = [] ∧ D.R (columnPorts k) = []
    let cost := fun i j => 1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W H J
    ready addr S → clean S → ∃ z F n, z.user = v.user ∧ n ≤ cost 0 7 + cost 8 15 ∧
      Exec body (.seq (columnSwapProgram 16 0 7) (columnSwapProgram 16 8 15)) (mk v S) n (mk z F) ∧
      ready (portSwapDigits ∘ addr) F ∧ clean F ∧
      F.L (Fin.last N) = S.L (Fin.last N) ∧ F.R (Fin.last N) = S.R (Fin.last N) := by
  intro ready clean cost before free
  obtain ⟨u,D,m,hu,hm',first,next,freeD,hl,hr⟩ := columnSwapRecord_exec (0 : Fin 16) 7
    (by decide) H J hm hw hW body v S record dest q original addr before free
  obtain ⟨z,F,n,hz,hn,last,out,freeF,hl',hr'⟩ := columnSwapRecord_exec (8 : Fin 16) 15
    (by decide) H J hm hw hW body u D record dest q original _ next freeD
  exact ⟨z,F,m+n,hz.trans hu,Nat.add_le_add hm' hn,Exec.seq first last,out,freeF,hl'.trans hl,hr'.trans hr⟩

/-- Both swaps, including header setup and workspace cleanup, fit the
stage's volume and atom-width rate with canonical binary headers. -/
theorem portPivotSwap_cost [M8.Machine.Net] (U : Type) :
    ∃ base swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let cost := fun i j => 1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W (Nat.size M) (Nat.size W)
      cost 0 7 + cost 8 15 ≤ (base+swaps*swapVolumeRate w)*(M^16*W) := by
  have one (i j : ℕ) : ∃ a b : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      1+completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j w W (Nat.size M) (Nat.size W) ≤
        (a+b*swapVolumeRate w)*(M^16*W) := by
    let cost := completeSwapTime (P := Empty) (U := U) Empty.elim 16 i j
    obtain ⟨a,setup⟩ := completeSwapTime_setup_le (P := Empty) (U := U) Empty.elim 16 i j
    have ctr : ∃ c : ℕ, ∀ w H J, cost w 0 H J = cost w 0 H 0 + c*J :=
      ⟨_,fun w H J => completeSwapTime_eq_setup_add_counter _ 16 i j w 0 H J⟩
    have vol : ∃ b : ℕ, ∀ w W H J, cost w W H J ≤ cost w 0 H J +
        b*swapVolumeRate w*((prime^(w+1))^16*W) :=
      ⟨_,fun w W H J => completeSwapTime_le_setup_add_volume _ 16 i j w W H J⟩
    obtain ⟨c,counter⟩ := ctr
    obtain ⟨b,bound⟩ := vol
    let k := 2*(Nat.size prime+1)^2
    refine ⟨1+a*k+c,b,?_⟩
    intro w W hW M
    let H := Nat.size M
    let J := Nat.size W
    have positive : 0 < M^16 := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
    have size : M^16 ≤ M^16*W := Nat.le_mul_of_pos_right _ hW
    have bits : 0 < (H+1)^2 := pow_pos (by omega) _
    have field := prefixSetup_volume_le w 15
    change (w+1+M^15)*(H+1)^2 ≤ k*M^16 at field
    have digits : 0 < M^15 := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
    rw [Nat.add_mul] at field
    have overhead := (Nat.add_le_add (Nat.le_mul_of_pos_right (w+1) bits)
      (Nat.le_mul_of_pos_left ((H+1)^2) digits)).trans (field.trans (Nat.mul_le_mul_left k size))
    have header := (setup w H).trans (Nat.mul_le_mul_left a overhead)
    have len : J ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
    have count := Nat.mul_le_mul_left c (len.trans (Nat.le_mul_of_pos_left W positive))
    have run := bound w W H J
    rw [counter] at run
    change cost w W H J ≤ cost w 0 H 0 + c*J + b*swapVolumeRate w*(M^16*W) at run
    change cost w 0 H 0 ≤ _ at header
    change 1+cost w W H J ≤ _
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    have := Nat.mul_pos positive hW
    omega
  obtain ⟨a,b,first⟩ := one 0 7
  obtain ⟨c,d,last⟩ := one 8 15
  refine ⟨a+c,b+d,?_⟩
  intro w W hW M cost
  exact (Nat.add_le_add (first w W hW) (last w W hW)).trans_eq (by ring)

end IntegerMultBounds.MathlibTM2.M6.BitNode
