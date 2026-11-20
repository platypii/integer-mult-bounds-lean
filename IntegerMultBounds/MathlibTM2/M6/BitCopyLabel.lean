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


private theorem payload_append {k t u : ℕ} (v : Tapes t prime) (workspace : Tapes u prime)
    (slots : Fin k → Fin (t+u)) (leading : ∀ i, (slots i).val = i.val) (fits : k ≤ t) :
    SharedBank.payload (v.append workspace) slots = SharedBank.payload v (fun i => Fin.castLE fits i) := by
  have same (i) : slots i = Fin.castAdd u (Fin.castLE fits i) := Fin.ext (leading i)
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [same,Tapes.append]

open M8.Machine in
/-- Projecting the leading owner slots of the complete COPY machine discards
all of its private workspaces, for either its initial or its final bank. -/
theorem copyLabel_payload [Net] {t w W : ℕ} (A D : List (FlatCoordinateSchedule.Op 16))
    (owners : Tapes t prime) (controls : Tapes 2 prime) (headers : Tapes 6 prime) (arithmetic : Tapes 15 prime)
    (slots : Fin t → Fin _) (leading : ∀ i, (slots i).val = i.val) :
    SharedBank.payload (copyPrepared (w := w) (W := W) A D (owners.append controls) headers arithmetic) slots = owners := by
  unfold copyPrepared ArbitraryWidthOriginalRun.input ArbitraryWidthHighPreparedRun.input
    ArbitraryWidthHighCommonPrepare.input ArbitraryWidthHighBranchPrepare.input ArbitraryWidthHighExecutionInitialize.input
  rw [payload_append _ _ slots leading (by omega)]
  have peel {k u : ℕ} (v : Tapes k prime) (extra : Tapes u prime) (h : t ≤ k+u) (small : t ≤ k) :
      SharedBank.payload (v.append extra) (fun i => Fin.castLE h i) =
        SharedBank.payload v (fun i => Fin.castLE small i) := payload_append v extra (fun i => Fin.castLE h i) (fun _ => rfl) small
  repeat rw [peel _ _ _ (by omega)]
  cases owners
  rfl

/-- The route block exposes the identical leading owner bank through its
24 public control tapes and its variable private tape count. -/
theorem copyRoute_payload {t : ℕ} (block : M8.RevMachine.Graph.Block (t+24) prime)
    (leading : M8.RevMachine.Blocks.Leading block) (owners : Tapes t prime) (v : Descriptor)
    (d : Fin 22 → Option (List Bool)) :
    SharedBank.payload (SharedBankStageInput.raw (LabelCall.bank owners v d) block.tapes)
        (fun i => block.slots (Fin.castAdd 24 i)) = owners := by
  have all := SharedBankRawCompose.payload_raw (LabelCall.bank owners v d) block.slots leading
  change SharedBank.payload (SharedBank.payload (SharedBankStageInput.raw (LabelCall.bank owners v d) block.tapes) block.slots) (Fin.castAdd 24) = owners
  rw [all]
  cases owners
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [LabelCall.bank,Tapes.append]

open M8.RevMachine in
/-- Compose both chart routes around a COPY body at their owner tapes. The route
controls and the private tapes of all three machines remain in the postcondition. -/
theorem copyRoute_window_return [M8.Machine.Net] {t w W states : ℕ}
    (route : Graph.Block (t+24) prime) (leading : Blocks.Leading route)
    (v : Descriptor) (d : Fin 22 → Option (List Bool)) (before entered : Tapes t prime)
    (A D : List (FlatCoordinateSchedule.Op 16)) (controls : Tapes 2 prime)
    (headers : Tapes 6 prime) (arithmetic : Tapes 15 prime) (body : Program _ states prime)
    (added out : Tapes t prime) (finalHeaders : Tapes 6 prime) (finalArithmetic : Tapes 15 prime)
    (leave : Graph.Block (t+24) prime) (leaveLeading : Blocks.Leading leave) {r b l : ℕ}
    (entry : GraphContract.Runs route (LabelCall.bank before v d) (LabelCall.bank entered v d) r)
    (run : HoareTime body
      (fun z => z = copyPrepared (w := w) (W := W) A D (entered.append controls) headers arithmetic)
      (fun z => z = copyPrepared (w := w) (W := W) A D (added.append controls) finalHeaders finalArithmetic) b)
    (exitRun : GraphContract.Runs leave (LabelCall.bank added v d) (LabelCall.bank out v d) l) :
    let rs := fun i => route.slots (Fin.castAdd 24 i)
    let cs := fun i : Fin t => Fin.castLE (by omega : t ≤ _) i
    let pair := SharedBankPair.program route.program body rs cs
    let common := SharedBankFrames.commonSlots t route.tapes _
    let ls := fun i => leave.slots (Fin.castAdd 24 i)
    let setup := SharedBankPair.input (SharedBankStageInput.raw (LabelCall.bank before v d) route.tapes)
        (copyPrepared (w := w) (W := W) A D (entered.append controls) headers arithmetic) rs cs
    let finish := SharedBankPair.output (SharedBankStageInput.raw (LabelCall.bank entered v d) route.tapes)
        (copyPrepared (w := w) (W := W) A D (added.append controls) finalHeaders finalArithmetic) rs cs
    HoareTime (SharedBankPair.program pair leave.program common ls)
      (fun z => z = SharedBankPair.input setup (SharedBankStageInput.raw (LabelCall.bank added v d) leave.tapes) common ls)
      (fun z => z = SharedBankPair.output finish (SharedBankStageInput.raw (LabelCall.bank out v d) leave.tapes) common ls)
      (r+b+1+l+1) := by
  intro rs cs pair common ls setup finish
  have join := SharedBankPair.pair_hoare entry run rs (route.slots_injective.comp (Fin.castAdd_injective t 24)) cs
    (Fin.castLE_injective _) ((copyRoute_payload route leading entered v d).trans
      (copyLabel_payload A D entered controls headers arithmetic cs (fun _ => rfl)).symm)
  apply SharedBankPair.pair_hoare join exitRun common (SharedBankFrames.commonSlots_injective ..) ls
    (leave.slots_injective.comp (Fin.castAdd_injective t 24))
  rw [SharedBankPair.output,SharedBankFrames.payload_common]
  exact (copyLabel_payload A D added controls finalHeaders finalArithmetic cs (fun _ => rfl)).trans
    (copyRoute_payload leave leaveLeading added v d).symm

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
        out (Fin.last 142080) = 0 ∧ out src = data src ∧
        (∀ k, k ≠ Fin.last 142080 → (∀ j : Fin 661, j.val ∈ life.targets → io j ≠ k) → out k = data k) ∧
        ∀ (j : Fin 661), j.val ∈ life.targets → ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B),
          chartRead (view (out (io j))) g z = chartRead (view (data (io j))) g z +
            chartRead (view (data src)) g {z with a := copyActive (move (copyActive.symm z.a))} := by
  intro io src
  obtain ⟨C,rev,fwd,states,machine,run⟩ := copyWindow_hoare n r d life scheduled
  refine ⟨_,_,states,machine,?_⟩
  intro w B K hw hB hK W N prepare hs view move data bs count bank
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨exec,_,_⟩ := (run w hw).2.2 hW data bs count
  let regs := life.targets.attach.map fun j =>
    (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
  have unchanged (k : Fin 142081)
      (outside : ∀ j : Fin 661, j.val ∈ life.targets → io j ≠ k) : k ∉ regs.map io := by
    rintro h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hj
    exact outside _ a.property rfl
  refine ⟨_,exec,Function.update_self ..,?_,?_,?_⟩
  · have off : src ≠ Fin.last 142080 := Fin.castSucc_ne_last _
    have outside (j : Fin 661) (hj : j.val ∈ life.targets) : io j ≠ src := by
      intro eq
      have same := congrArg Fin.val (ownerTape_injective n r d eq)
      have bound := (Copy.target_bounds life scheduled _ hj).2
      have lo := (Copy.source_bounds life scheduled).1
      change j.val = life.source at same
      omega
    have absent := unchanged src outside
    dsimp only [regs,io] at absent
    simp only [Function.update_of_ne off,ite_eq_right absent]
  · intro k off outside
    have absent := unchanged k outside
    dsimp only [regs,io] at absent
    simp only [Function.update_of_ne off,ite_eq_right absent]

  intro j member g z
  have target := List.mem_map_of_mem (f := ownerTape n r d)
    (List.mem_map_of_mem (f := fun k : {k // k ∈ life.targets} =>
      (⟨k.val,((Copy.target_bounds life scheduled _ k.property).2.trans (by decide : 222 < 661))⟩ : Fin 661))
      (List.mem_attach life.targets ⟨j.val,member⟩))
  have off : io j ≠ Fin.last 142080 := Fin.castSucc_ne_last _
  change io j ∈ _ at target
  simp only [Function.update_of_ne off,ite_eq_left target]
  exact copyLabel_window_read (life.sourceFrame,0) (data src) (data (io j)) g z

open IntegerMultBounds.Networks.Certificates.PR589 M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- Execute the scheduled charts on both sides of the actual COPY body.
The returned target is read in its original chart, with the retained source
read through the relative chart and the selected local frame change. -/
theorem routedCopy_runs [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) :
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    ∃ (entry leave : Graph.Block (142081+24) prime) (P Q : ℕ)
      (A D : List (FlatCoordinateSchedule.Op 16)) (states : ℕ) (body : Program _ states prime),
      ∀ (w B K : ℕ), 0 < w → 0 < B → 0 < K →
      let v := copyLabelLayout w B K
      let W := B*prime^(64*(w*64))*K
      let V := volume prime v
      let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
      let readSource := fun (z : LabelEntry.Cell v B) => {z with a := copyActive (move (copyActive.symm z.a))}
      let bank := fun data => LabelCall.bank (copyOwners (v := v) data) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))
      let routeCost := fun C => C*V+(63+252*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∀ (x : Fin 142081 → Fin V → ZMod 2) (bs : List Bool), Counter.value bs = V →
      let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1
      let prep := fun data => copyPrepared (w := w) (W := W) A D ((copyOwners (v := v) data).append controls)
      let rs := fun i => entry.slots (Fin.castAdd 24 i)
      let cs := fun i : Fin 142081 => Fin.castLE (by omega : 142081 ≤ _) i
      let pair := SharedBankPair.program entry.program body rs cs
      let common := SharedBankFrames.commonSlots 142081 entry.tapes _
      let ls := fun i => leave.slots (Fin.castAdd 24 i)
      ∃ entered added out,
        let setup := SharedBankPair.input (SharedBankStageInput.raw (bank x) entry.tapes)
          (prep entered (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W)) rs cs
        let finish := SharedBankPair.output (SharedBankStageInput.raw (bank entered) entry.tapes)
          (prep added (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W)) rs cs
        HoareTime (SharedBankPair.program pair leave.program common ls)
          (fun z => z = SharedBankPair.input setup (SharedBankStageInput.raw (bank added) leave.tapes) common ls)
          (fun z => z = SharedBankPair.output finish (SharedBankStageInput.raw (bank out) leave.tapes) common ls)
          (routeCost P + (copyWindowWork (FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D)
            life.targets.length V bs.length + cost (copyChild w W) hs) + 1 + routeCost Q + 1) ∧
        ∀ j ∈ life.targets, ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell v B),
          chartRead (out (io j)) g z = chartRead (x (io j)) g z +
            chartRead (x (io life.source)) (g*(registerChart w n j).transpose*registerChart w n life.source) (readSource z) := by
  intro io
  obtain ⟨entry,P,leading,enter⟩ := copyWindow_routes n r d true life scheduled
  obtain ⟨leave,Q,leaveLeading,exitRun⟩ := copyWindow_routes n r d false life scheduled
  obtain ⟨A,D,states,body,run⟩ := copyLabel_window_runs n r d life scheduled
  refine ⟨entry,leave,P,Q,A,D,states,body,?_⟩
  intro w B K hw hB hK v W V move readSource bank routeCost hs x bs count controls prep rs cs pair common ls
  have pos : v.Positive := ⟨pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _,Nat.zero_lt_one,
    Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _),Nat.zero_lt_one,hK⟩
  obtain ⟨entered,source,targets,_,en⟩ := enter v w B hw hB rfl pos x
  let size := copyLabel_volume w B K
  let data := fun k (i : Fin ((prime^w)^16*W)) => entered k (Fin.cast size.symm i)
  let view := fun (a : Fin ((prime^w)^16*W) → ZMod 2) (i : Fin V) => a (Fin.cast size i)
  have cancel (k) : view (data k) = entered k := by funext i; simp [view,data]
  obtain ⟨y,exec,_,_,_,add⟩ := run w B K hw hB hK data bs (count.trans size)
  let added := fun k => view (y k)
  obtain ⟨out,_,back,_,ex⟩ := exitRun v w B hw hB rfl pos added
  refine ⟨entered,added,out,?_⟩
  intro setup finish
  constructor
  · dsimp only at exec
    rw [copyOwners_controls size data bs,copyOwners_controls size y bs] at exec
    have eq : (fun k => view (data k)) = entered := funext cancel
    change HoareTime body (fun z => z = prep (fun k => view (data k)) _ _) (fun z => z = prep added _ _) _ at exec
    rw [eq,← size] at exec
    exact copyRoute_window_return entry leading v _ (copyOwners x) (copyOwners entered) A D controls _ _
      body (copyOwners added) (copyOwners out) _ _ leave leaveLeading en exec ex
  · intro j hj g z
    have jBound := ((Copy.target_bounds life scheduled j hj).2.trans (by decide : 222 < 661))
    have jVal : (Fin.ofNat 661 j).val = j := Nat.mod_eq_of_lt jBound
    have srcEq : Fin.ofNat 661 life.source = ⟨life.source,(Copy.source_bounds life scheduled).2⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (Copy.source_bounds life scheduled).2)
    have action (l : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) : chartRead (added (io j)) l = chartRead (entered (io j)) l +
        (fun c => chartRead (entered (io life.source)) l (readSource c)) := by
      funext c
      have h := add (Fin.ofNat 661 j) (by rwa [jVal]) l c
      change chartRead (added (io j)) l c = chartRead (view (data (io j))) l c +
        chartRead (view (data (ownerTape n r d ⟨life.source,_⟩))) l (readSource c) at h
      simpa only [cancel,io,srcEq,Pi.add_apply] using h
    apply congrFun (chartRead_copy_add n life.source j _ _ _ _ _ _ source ?_ (back j hj)
      (fun a c => a (readSource c)) action g) z
    intro l
    rw [dataChart_transpose w n (Copy.target_bounds life scheduled j hj).2]
    exact chartRead_transport (targets j hj) l

end IntegerMultBounds.MathlibTM2.M6.BitNode
