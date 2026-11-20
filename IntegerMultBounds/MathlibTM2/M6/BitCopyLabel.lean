module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyRun
public import IntegerMultBounds.MathlibTM2.M6.BitRouteRun

/-! Physical cover-label reads of the pointwise COPY window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.RevMachine (ext ext_apply)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Keep the sixteen active fields ahead of the cover label and trailing
spectators. The routing program can use width zero in its payload descriptor. -/
noncomputable def copyLabelLayout (w B K : ℕ) : Descriptor :=
  ⟨(prime^w)^16,1,B*prime^(64*(w*64)),0,1,K⟩

private theorem copyLabel_index {w B K : ℕ} (z : LabelEntry.Cell (copyLabelLayout w B K) B) (before : ℕ) :
    RecursiveInterchangeLayout.index prime (copyLabelLayout w B K) z.a z.row before z.h z.mid z.d z.after =
      z.a.val*(B*prime^(64*(w*64))*K)+(before*K+z.after.val) := by
  have row : z.row.val = 0 := Nat.lt_one_iff.mp z.row.isLt
  have mid : z.mid.val = 0 := Nat.lt_one_iff.mp z.mid.isLt
  have h : z.h.val = 0 := Nat.lt_one_iff.mp (by simpa [copyLabelLayout,ActualAffineScaling.modulus] using z.h.isLt)
  have d : z.d.val = 0 := Nat.lt_one_iff.mp (by simpa [copyLabelLayout,ActualAffineScaling.modulus] using z.d.isLt)
  simp only [RecursiveInterchangeLayout.index,copyLabelLayout,row,mid,h,d,pow_zero,Nat.mul_one,Nat.add_zero]
  exact pack _ _ _ _ _
where
  pack (a V b K k : ℕ) : (a*V+b)*K+k = a*(V*K)+(b*K+k) := by ring

/-- The cover read on this layout is the literal address used by COPY, with
the whole matrix label packed into the spectator index. -/
theorem copyLabel_read {w B K : ℕ} (x : Fin (volume prime (copyLabelLayout w B K)) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let count := prime^(64*(w*64))
    let spectator := (z.b.val*count+(LabelAddress.address g).val)*K+z.after.val
    chartRead x g z = ext x (z.a.val*(B*count*K)+spectator) := by
  intro count spectator
  exact congrArg (ext x) (copyLabel_index z _)

/-- A fanout addition on physical positions induces the same addition on
each cover-label slice when the local move changes the leading field. -/
theorem copyLabel_add {w B K : ℕ}
    (f : Fin ((prime^w)^16) → Fin ((prime^w)^16))
    (src dst out : Fin (volume prime (copyLabelLayout w B K)) → ZMod 2)
    (add : ∀ (a : Fin ((prime^w)^16)) (j : ℕ), j < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      ext out (a.val*W+j) = ext dst (a.val*W+j) + ext src ((f a).val*W+j))
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    chartRead out g z = chartRead dst g z + chartRead src g {z with a := f z.a} := by
  rw [copyLabel_read out,copyLabel_read dst,copyLabel_read src]
  apply add
  apply LabelShift.pack_lt _ z.after.isLt
  apply LabelShift.pack_lt z.b.isLt
  have size : (prime^w)^(64*64) = prime^(64*(w*64)) := by
    rw [← pow_mul]
    congr 1
    omega
  exact size ▸ (LabelAddress.address g).isLt

theorem copyLabel_volume (w B K : ℕ) :
    volume prime (copyLabelLayout w B K) = (prime^w)^16*(B*prime^(64*(w*64))*K) := by
  simp only [volume,copyLabelLayout,pow_zero,Nat.mul_one,Nat.mul_assoc]

/-- Read the exact pointwise target output of the physical COPY window.
The selected modular word changes the active coordinate of the source cell
while its cover label and spectator position stay fixed. -/
theorem copyLabel_window_read {w B K : ℕ} (p : ℕ × ℕ)
    (src dst : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let move := AffineFieldProgram.run (selectedWord w p)
    let output := fun i => dst i + src (copyAddress.symm (move (copyAddress i).1,(copyAddress i).2))
    let view := fun (x : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) i =>
      x (Fin.cast (copyLabel_volume w B K) i)
    chartRead (view output) g z = chartRead (view dst) g z +
      chartRead (view src) g {z with a := copyActive (move (copyActive.symm z.a))} := by
  intro move output view
  apply copyLabel_add (fun a => copyActive (move (copyActive.symm a)))
  intro a j hj W
  let k : Fin W := ⟨j,hj⟩
  have read (x : Fin ((prime^w)^16*W) → ZMod 2) (b : Fin ((prime^w)^16)) :
      ext (view x) (b.val*W+j) = x (finProdFinEquiv (b,k)) := by
    let i := finProdFinEquiv (b,k)
    have eq : i.val = b.val*W+j := by
      change j+W*b.val = _
      rw [Nat.mul_comm,Nat.add_comm]
    rw [← eq,M8.RevMachine.ext_cast,ext_apply]
  rw [read,read,read]
  have unpack : copyAddress (finProdFinEquiv (a,k)) = (copyActive.symm a,k) := by
    apply copyAddress.symm.injective
    rw [Equiv.symm_apply_apply]
    change finProdFinEquiv (a,k) = finProdFinEquiv (copyActive (copyActive.symm a),k)
    rw [Equiv.apply_symm_apply]
  simp only [output,unpack]
  rfl


open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine.ArbitraryWidthOriginalRun in
/-- The same width-uniform machine that executes the COPY window realizes its
cover-label addition at every actual target, with the child run charged once. -/
theorem copyLabel_window_runs [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) :
    let io := ownerTape n r d
    let src := io ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    ∃ (A D : List (FlatCoordinateSchedule.Op 16)) (states : ℕ) (machine : Program _ states prime),
      ∀ (w B K : ℕ), 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let N := (prime^w)^16*W
      let prepare := copyPrepared (t := 142081+2) (w := w) (W := W) A D
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let view := fun (x : Fin N → ZMod 2) i => x (Fin.cast (copyLabel_volume w B K) i)
      let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
      ∀ (data : Fin 142081 → Fin N → ZMod 2) (bs : List Bool), Counter.value bs = N →
      let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) bs
      ∃ out, HoareTime machine (fun z => z = prepare (bank data) (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W))
        (fun z => z = prepare (bank out) (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W))
        (copyWindowWork (FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D)
          life.targets.length N bs.length + cost (copyChild w W) hs) ∧
        ∀ (j : Fin 661), j.val ∈ life.targets → ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B),
          chartRead (view (out (io j))) g z = chartRead (view (data (io j))) g z +
            chartRead (view (data src)) g {z with a := copyActive (move (copyActive.symm z.a))} := by
  intro io src
  obtain ⟨C,rev,fwd,states,machine,run⟩ := copyWindow_hoare n r d life scheduled
  refine ⟨_,_,states,machine,?_⟩
  intro w B K hw hB hK W N prepare hs view move data bs count bank
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨exec,_,_⟩ := (run w hw).2.2 hW data bs count
  refine ⟨_,exec,?_⟩
  intro j member g z
  have target := List.mem_map_of_mem (f := ownerTape n r d)
    (List.mem_map_of_mem (f := fun k : {k // k ∈ life.targets} =>
      (⟨k.val,((Copy.target_bounds life scheduled _ k.property).2.trans (by decide : 222 < 661))⟩ : Fin 661))
      (List.mem_attach life.targets ⟨j.val,member⟩))
  have off : io j ≠ Fin.last 142080 := Fin.castSucc_ne_last _
  change io j ∈ _ at target
  simp only [Function.update_of_ne off,ite_eq_left target]
  exact copyLabel_window_read (life.sourceFrame,0) (data src) (data (io j)) g z

end IntegerMultBounds.MathlibTM2.M6.BitNode
