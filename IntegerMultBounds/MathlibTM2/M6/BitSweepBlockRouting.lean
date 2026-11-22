module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderReturnTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitSweepWindowRead
public import IntegerMultBounds.MathlibTM2.M6.BitSweepGatherLoop

/-! Run a sweep address conversion on contiguous inherited blocks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host CompactRows
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

/-- A conversion on contiguous blocks lifts to the staged owner layout. Both
transposes preserve the record clock needed by the return pass. -/
theorem sweepBlockRouting_exec {P U : Type} {q alphabet : ℕ}
    (body : P → Pr P 8 q alphabet U) (middle : Pr P 8 q alphabet U)
    (w B W : ℕ) (hb : 0 < B) (hw : 0 < W) :
    let M := prime^w
    let A := M^16
    let K := M^112*W
    let N := prime^(64*(w*64))
    ∀ (x : Fin (A*(B*K)) → Fin (alphabet+4)) (y : Fin (B*(A*K)) → Fin (alphabet+4))
      (S : Stacks 8 alphabet) (u : HS 8 q alphabet U) (record row : List (Fin (alphabet+4)))
      (cost : ℕ), record.length = K → row.length = B*K →
      (∀ v : HS 8 q alphabet U,
        let ready := fun word => transposeStacks S word []
          (List.replicate A record.reverse).flatten record row
        ∃ z steps, z.user = v.user ∧ Exec body middle
          (mk v (ready (List.ofFn (compactTranspose x)))) steps (mk z (ready (List.ofFn y))) ∧ steps ≤ cost) →
      ∃ z steps, z.user = u.user ∧ Exec body
        (.seq (.seq (.act (peekR 6)) transposeLoop) (middle.seq (.seq (.act (peekR 3)) returnTransposeLoop)))
        (mk u (transposeStacks S [] (List.ofFn x) [] record row)) steps
        (mk z (transposeStacks S [] (List.ofFn (compactTranspose y)) [] record row)) ∧
        steps ≤ cost + 104*(A*(B*N*K))+4 := by
  intro M A K N x y S u record row cost len width convert
  have hk : 0 < K := Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) hw
  obtain ⟨v,clock,t,rfl,user,enter,paid⟩ :=
    remainderCompactTranspose_exec body w B K hb hk x S u record row len width
  obtain ⟨v',s,midUser,run,midPaid⟩ := convert v
  obtain ⟨z,j,lastUser,leave,lastPaid⟩ := remainderCompactReturn_exec body w B K hb hk y S v' record row len
  exact ⟨z,_,lastUser.trans (midUser.trans user),Exec.seq enter (Exec.seq run leave),by
    change t ≤ 52*(A*(B*N*K))+2 at paid
    change j ≤ 52*(A*(B*N*K))+2 at lastPaid
    omega⟩

/-- In block order, each complete coordinate vector occupies its ordinary
rank, including its trailing spectator. -/
theorem compactTranspose_stagedOwnerIndex {M B W : ℕ} {α : Type}
    (x : Fin (M^16*(B*(M^112*W))) → α) (b : Fin B) (j : Fin (M^128*W)) :
    compactTranspose x (finProdFinEquiv (b,j.cast (ordinaryCompact_width M W).symm)) =
      x (stagedOwnerIndex b j) := by
  simp only [compactTranspose,stagedOwnerIndex,Equiv.symm_apply_apply]

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩
open IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine

/-- Active addresses select a pair of coordinate ranks independently of the
inherited block and the position in its spectator record. -/
theorem activeWindowAddress_record (w : ℕ) (s : Swap.Shear.State Axis (ZMod (prime^w))) :
    ∃ (a : Fin ((prime^w)^16)) (t : Fin ((prime^w)^112)), ∀ {B W : ℕ} (b : Fin B) (j : Fin W),
      activeWindowAddress b s j = finProdFinEquiv (a,finProdFinEquiv (b,finProdFinEquiv (t,j))) := by
  let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
  let h := Equiv.arrowCongr (@finProdFinEquiv 8 7) (Equiv.refl (ZMod (prime^w)))
  refine ⟨FlatCoordinateLayout.rank (AffineFieldCoordinates.embed
    (M8.Exchange.transform D⁻¹ D⁻¹ (chartHalves s).1)),
    chartAddress.copyExterior ((h.prodCongr h) (chartHalves s).2),?_⟩
  intro B W b j
  simp [activeWindowAddress,chartAddress,-copyAddress_index,FlatCoordinateLayout.index,D,h]

/-- A role conversion can move whole spectator records. Every block uses
the same pair of coordinate ranks. -/
theorem sweepRoleEquiv_record (w : ℕ) (n : Fin 9) (r : Role)
    (s : Swap.Shear.State Axis (ZMod (prime^w))) :
    ∃ (a : Fin ((prime^w)^16)) (t : Fin ((prime^w)^112)), ∀ {B W : ℕ} (b : Fin B) (j : Fin W),
      sweepRoleEquiv w B W n r (b,s,j) = finProdFinEquiv (a,finProdFinEquiv (b,finProdFinEquiv (t,j))) := by
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · let H := Swap.Modular.reduce (prime^w) ((port r.port.val).stageRoute n)
    obtain ⟨a,t,cell⟩ := activeWindowAddress_record w (M8.Exchange.transform H H s)
    refine ⟨a,t,?_⟩
    intro B W b j
    simp only [sweepRoleEquiv,active,↓reduceIte,Equiv.trans_apply,Equiv.prodCongr_apply,
      Prod.map_apply,Equiv.refl_apply,activeWindowEquiv_apply]
    exact cell b j
  · let x := helperSlotField (port r.port.val) none w s
    refine ⟨FlatCoordinateLayout.rank (x ∘ Fin.castAdd 112),FlatCoordinateLayout.rank (x ∘ Fin.natAdd 16),?_⟩
    intro B W b j
    simp only [sweepRoleEquiv,active,↓reduceIte]
    exact stagedOwnerIndex_index x b j

/-- The rectangular record table is a bijection. It can be shared by all
inherited blocks, regardless of the length of a spectator record. -/
theorem sweepRecordPermutation (w : ℕ) (n : Fin 9) (r : Role) :
    ∃ table : Swap.Shear.State Axis (ZMod (prime^w)) ≃ Fin ((prime^w)^16) × Fin ((prime^w)^112),
      ∀ {B W : ℕ} (s) (b : Fin B) (j : Fin W), sweepRoleEquiv w B W n r (b,s,j) =
        finProdFinEquiv ((table s).1,finProdFinEquiv (b,finProdFinEquiv ((table s).2,j))) := by
  classical
  choose a t cell using sweepRoleEquiv_record w n r
  let f := fun s => (a s,t s)
  let pack := fun (p : Fin ((prime^w)^16) × Fin ((prime^w)^112)) =>
    finProdFinEquiv (p.1,finProdFinEquiv ((0 : Fin 1),finProdFinEquiv (p.2,(0 : Fin 1))))
  have inj : Function.Injective pack := by
    intro p q h
    simpa only [pack,EmbeddingLike.apply_eq_iff_eq,Prod.mk.injEq,true_and,and_true,Prod.ext_iff] using h
  have atOne (s) : sweepRoleEquiv w 1 1 n r (0,s,0) = pack (f s) := cell s 0 0
  have bij : Function.Bijective f := by
    constructor
    · intro s v eqn
      have same := (sweepRoleEquiv w 1 1 n r).injective ((atOne s).trans ((congrArg pack eqn).trans (atOne v).symm))
      exact congrArg (fun p => p.2.1) same
    · intro p
      obtain ⟨⟨b,s,j⟩,eqn⟩ := (sweepRoleEquiv w 1 1 n r).surjective (pack p)
      rw [Subsingleton.elim b 0,Subsingleton.elim j 0,atOne] at eqn
      exact ⟨s,inj eqn⟩
  exact ⟨Equiv.ofBijective f bij,fun s b j => cell s b j⟩

/-- Consuming the selector stream and gathering every record stays within the
padded node volume, uniformly in the inherited block count and width. -/
theorem sweepRecordGather_volume (w B W : ℕ) (hw : 0 < W) :
    let M := prime^w
    let rows := M^128
    let labels := prime^(64*(w*64))
    B*(rows*(rows*(16*W+18)+26)+2) ≤ 62*(M^16*(B*labels*(M^112*W))) := by
  intro M rows labels
  have hm : 0 < M := pow_pos prime_prime.pos _
  have hr : 1 ≤ rows := pow_pos hm _
  have room : rows ≤ labels := by
    change (prime^w)^128 ≤ prime^(64*(w*64))
    rw [← pow_mul]
    exact Nat.pow_le_pow_right prime_prime.pos (by omega)
  have cost : rows*(16*W+18)+26 ≤ 60*(labels*W) := by
    have hrow : 1 ≤ rows*W := Nat.mul_pos hr hw
    calc
      _ ≤ rows*(34*W)+26*(rows*W) := by gcongr <;> omega
      _ = 60*(rows*W) := by ring
      _ ≤ _ := by gcongr
  have large : 1 ≤ rows*(labels*W) := Nat.mul_pos hr (Nat.mul_pos (hr.trans room) hw)
  calc
    _ ≤ B*(rows*(60*(labels*W))+2*(rows*(labels*W))) := by gcongr <;> omega
    _ = _ := by rw [show rows = M^16*M^112 by rw [← pow_add]]; ring

/-- The padded node volume pays for any cubic setup per block and the physical
record gather at every positive inherited record width. -/
theorem sweepPhysicalBlock_volume (w B W C : ℕ) (hw : 0 < W) :
    let M := prime^w
    let n := M^128
    let labels := prime^(64*(w*64))
    B*(C*n^3+(n*(n*(16*W+18)+26)+2)) ≤ (C+62)*(M^16*(B*labels*(M^112*W))) := by
  intro M n labels
  have room : n^2 ≤ labels := by
    change ((prime^w)^128)^2 ≤ prime^(64*(w*64))
    rw [← pow_mul,← pow_mul]
    exact Nat.pow_le_pow_right prime_prime.pos (by omega)
  have bound : C*n^3 ≤ C*n*(labels*W) := calc
    _ = C*n*n^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (room.trans (Nat.le_mul_of_pos_right _ hw))
  have size : n = M^16*M^112 := by rw [← pow_add]
  have build := Nat.mul_le_mul_left B bound
  have run := sweepRecordGather_volume w B W hw
  change B*(n*(n*(16*W+18)+26)+2) ≤ 62*(M^16*(B*labels*(M^112*W))) at run
  rw [Nat.mul_add]
  calc
    _ ≤ B*(C*n*(labels*W))+62*(M^16*(B*labels*(M^112*W))) := Nat.add_le_add build run
    _ = _ := by rw [size]; ring

/-- Include the in-place scan's consumption and final ordered writeback. -/
theorem sweepBlockScan_volume (w B W C : ℕ) (hw : 0 < W) :
    let M := prime^w
    let n := M^128
    let labels := prime^(64*(w*64))
    let cost := C*n^3+n*(n*(16*W+18)+26)+2
    B*(cost+10*(n*W)+12)+4 ≤ (C+84)*(M^16*(B*labels*(M^112*W)))+4 := by
  intro M n labels cost
  have physical := sweepPhysicalBlock_volume w B W C hw
  have bill : B*cost ≤ (C+62)*(M^16*(B*labels*(M^112*W))) := by
    simpa only [cost,Nat.add_assoc] using physical
  have positive : 1 ≤ n*W := Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) hw
  have perBlock : 10*(n*W)+12 ≤ 22*(n*W) := by omega
  have fit : n*W ≤ labels*(n*W) := Nat.le_mul_of_pos_left _ (pow_pos prime_prime.pos _)
  have extra := Nat.mul_le_mul_left B (perBlock.trans (Nat.mul_le_mul_left 22 fit))
  have split : n = M^16*M^112 := by rw [← pow_add]
  calc
    _ = B*cost+B*(10*(n*W)+12)+4 := by ring
    _ ≤ (C+62)*(M^16*(B*labels*(M^112*W)))+B*(22*(labels*(n*W)))+4 := by gcongr
    _ = _ := by rw [split]; ring

/-- Compiling a fresh mask stream and consuming it in each inherited block
still costs a constant times the padded node volume. -/
theorem sweepCompiledGather_volume (w B W L : ℕ) (hw : 0 < W) (width : L ≤ (prime^w)^128+1) :
    let M := prime^w
    let n := M^128
    let labels := prime^(64*(w*64))
    let compile := n*(Routing.descriptorCompileCallCost L n+2)+2*(n*(L+1))+4
    let gather := n*(n*(16*W+18)+26)+2
    B*(compile+gather) ≤ 362*(M^16*(B*labels*(M^112*W))) := by
  intro M n labels compile gather
  have hn : 0 < n := pow_pos (pow_pos prime_prime.pos _) _
  exact (Nat.mul_le_mul_left B (Nat.add_le_add_right (sweepPermutationMasks_cost hn width) gather)).trans
    (sweepPhysicalBlock_volume w B W 300 hw)

end IntegerMultBounds.MathlibTM2.M6.BitNode
