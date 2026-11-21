module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildLayout
public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence
public import IntegerMultBounds.MathlibTM2.Cover.LabelMask

/-! One ranked transpose across the ordinary records of a PR589 directory. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address)
open Shared50RecursiveNodeTranspose (swapAddress)

noncomputable def ordinaryDirectoryChild (parent : Descriptor) (r g w : ℕ) : Descriptor :=
  {ordinaryChildDescriptor r g w (parent.between*parent.afterD) with
    beforeRows := parent.beforeRows, rows := parent.rows, beforeH := parent.beforeH}

theorem ordinaryDirectoryChild_volume (parent : Descriptor) (r g w : ℕ) :
    let row := ordinaryChildDescriptor r g w (parent.between*parent.afterD)
    LabelMask.records parent * volume prime row = volume prime (ordinaryDirectoryChild parent r g w) := by
  simp only [volume,ordinaryDirectoryChild,ordinaryChildDescriptor,LabelMask.records,one_mul]
  ring

theorem ordinaryDirectorySpectators (parent : Descriptor) (r g w : ℕ) :
    CopyChildLayout.spectators (ordinaryDirectoryChild parent r g w) =
      CopyChildLayout.spectators (rankDescriptor prime (r*(w+1)) (g*(w+1)) parent) := by
  simp only [CopyChildLayout.spectators,ordinaryDirectoryChild,ordinaryChildDescriptor,rankDescriptor,
    pow_add]
  ring

/-- Reindex the concatenated record payloads as the single scheduled rank child. -/
noncomputable def ordinaryDirectoryLayout (parent : Descriptor) (r g w : ℕ) :=
  let batch := ordinaryDirectoryChild parent r g w
  let child := rankDescriptor prime (r*(w+1)) (g*(w+1)) parent
  let change := CopyChildLayout.changeLayout batch child (Nat.mul_comm ..) (ordinaryDirectorySpectators parent r g w)
  (finCongr (ordinaryDirectoryChild_volume parent r g w)).trans
    ((CopyChildLayout.flatAddress batch).symm.trans (change.trans (CopyChildLayout.flatAddress child)))

private theorem directoryRow_index (parent : Descriptor) (r g w : ℕ)
    (a : Fin parent.beforeRows) (row : Fin parent.rows) (b : Fin parent.beforeH)
    (i : Address (ordinaryChildDescriptor r g w (parent.between*parent.afterD))) :
    let j := finProdFinEquiv (finProdFinEquiv (a,row),b)
    let z : Address (ordinaryDirectoryChild parent r g w) := ⟨a,row,b,i.h,i.middle,i.d,i.after⟩
    (finProdFinEquiv (j,RecursiveInterchangeScaling.index i)).cast (ordinaryDirectoryChild_volume parent r g w) =
      RecursiveInterchangeScaling.index z := by
  intro j z
  apply Fin.ext
  change (RecursiveInterchangeScaling.index i).val + volume prime (ordinaryChildDescriptor r g w (parent.between*parent.afterD))*j.val = (RecursiveInterchangeScaling.index z).val
  rw [RecursiveInterchangeScaling.index_val,RecursiveInterchangeScaling.index_val]
  have ha : i.beforeRows.val = 0 := Nat.lt_one_iff.mp i.beforeRows.isLt
  have hr : i.row.val = 0 := Nat.lt_one_iff.mp i.row.isLt
  have hb : i.before.val = 0 := Nat.lt_one_iff.mp i.before.isLt
  simp only [j,finProdFinEquiv,Equiv.coe_fn_mk,z,RecursiveInterchangeLayout.index,ha,hr,hb,
    volume,ordinaryDirectoryChild,ordinaryChildDescriptor]
  ring

/-- In directory order, the recursive transpose acts separately within
each contiguous packed record and leaves its record index fixed. -/
theorem ordinaryDirectoryRowTranspose (parent : Descriptor) (r g w : ℕ) :
    let packed := ordinaryChildDescriptor r g w (parent.between*parent.afterD)
    let batch := ordinaryDirectoryChild parent r g w
    ∀ {α : Type} (word : Fin (volume prime batch) → α) (j : Fin (LabelMask.records parent)),
      let cell := fun k : Fin (volume prime packed) =>
        (finProdFinEquiv (j,k)).cast (ordinaryDirectoryChild_volume parent r g w)
      ∀ k, Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (word ∘ cell) k =
        Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word (cell k) := by
  intro packed batch α word j cell i
  obtain ⟨⟨ar,b⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨a,row⟩,rfl⟩ := finProdFinEquiv.surjective ar
  obtain ⟨addr,rfl⟩ := (CopyChildLayout.flatAddress packed).surjective i
  let place (k : Address packed) : Address batch := ⟨a,row,b,k.h,k.middle,k.d,k.after⟩
  have atCell (k : Address packed) : cell (CopyChildLayout.flatAddress packed k) =
      CopyChildLayout.flatAddress batch (place k) := directoryRow_index parent r g w a row b k
  have left := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd packed.rows)
    (word ∘ cell) (swapAddress addr)
  have right := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd batch.rows)
    word (swapAddress (place addr))
  calc
    _ = word (cell (CopyChildLayout.flatAddress packed (swapAddress addr))) := left
    _ = word (CopyChildLayout.flatAddress batch (swapAddress (place addr))) :=
      congrArg word (atCell (swapAddress addr))
    _ = _ := right.symm.trans (congrArg (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) (atCell addr).symm)

/-- The same record reads hold on the scheduled child's spectator layout. -/
theorem ordinaryDirectoryTranspose (parent : Descriptor) (r g w : ℕ) :
    let packed := ordinaryChildDescriptor r g w (parent.between*parent.afterD)
    let child := rankDescriptor prime (r*(w+1)) (g*(w+1)) parent
    let layout := ordinaryDirectoryLayout parent r g w
    ∀ {α : Type} (word : Fin (volume prime child) → α) (j : Fin (LabelMask.records parent)),
      let cell := fun i : Fin (volume prime packed) => layout (finProdFinEquiv (j,i))
      ∀ i, Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (word ∘ cell) i =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word (cell i) := by
  intro packed child layout α word j cell i
  let batch := ordinaryDirectoryChild parent r g w
  let change := CopyChildLayout.changeLayout batch child (Nat.mul_comm ..) (ordinaryDirectorySpectators parent r g w)
  let chart := (CopyChildLayout.flatAddress batch).symm.trans (change.trans (CopyChildLayout.flatAddress child))
  exact (ordinaryDirectoryRowTranspose parent r g w (word ∘ chart) j i).trans
    (transpose_changeLayout batch child (Nat.mul_comm ..) (ordinaryDirectorySpectators parent r g w) word _)

/-- The two descriptor packings put corresponding cells at the same tape offset. -/
theorem ordinaryDirectoryPack_index (parent : Descriptor) (r g w : ℕ) :
    let batch := ordinaryDirectoryChild parent r g w
    let child := rankDescriptor prime (r*(w+1)) (g*(w+1)) parent
    let eqn := ordinaryDirectoryChild_volume parent r g w
    ∀ i, (CopyChildLayout.packActive child (ordinaryDirectoryLayout parent r g w i)).val =
      (CopyChildLayout.packActive batch (i.cast eqn)).val := by
  intro batch child eqn i
  let a := (CopyChildLayout.flatAddress batch).symm (i.cast eqn)
  have source : RecursiveInterchangeScaling.index a = i.cast eqn :=
    (CopyChildLayout.flatAddress batch).apply_symm_apply _
  have same := CopyChildLayout.packActive_change batch child (Nat.mul_comm ..) (ordinaryDirectorySpectators parent r g w) a
  exact same.trans (congrArg (fun k => (CopyChildLayout.packActive batch k).val) source)

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- One scheduled call covers all directory records of the occurrence. Its
volume is one role share, including every record's trailing spectators. -/
theorem scheduledDirectoryTranspose (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let parent := role node 142080
    let r := nodeChildren5[i.val]
    let g := 64-r
    let packed := ordinaryChildDescriptor r g w (parent.between*parent.afterD)
    let child := scheduledChild prime node i
    let records := LabelMask.records parent
    let batch := ordinaryDirectoryChild parent r g w
    ScheduledChildShape prime node i batch ∧
      records*volume prime packed*142080 = volume prime node ∧
      ∃ layout : Fin (records*volume prime packed) ≃ Fin (volume prime child),
      (∀ k, (CopyChildLayout.packActive child (layout k)).val =
        (CopyChildLayout.packActive (ordinaryDirectoryChild parent r g w)
          (k.cast (ordinaryDirectoryChild_volume parent r g w))).val) ∧
      ∀ {α : Type} (word : Fin (volume prime child) → α) (j : Fin records),
        let cell := fun k : Fin (volume prime packed) => layout (finProdFinEquiv (j,k))
        ∀ k, Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (word ∘ cell) k =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word (cell k) := by
  intro parent r g packed child records batch
  have weight := (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2
  have same : child = rankDescriptor prime (r*(w+1)) (g*(w+1)) parent := by
    simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    rfl
  change volume prime child * 142080 = volume prime node at weight
  rw [same] at weight ⊢
  let layout := ordinaryDirectoryLayout parent r g w
  have size := Fintype.card_congr layout
  simp only [Fintype.card_fin] at size
  have shape : ScheduledChildShape prime node i batch := by
    constructor
    · change batch.width = child.width
      rw [same]
      exact Nat.mul_comm ..
    · rfl
    · change volume prime batch = volume prime child
      rw [same,← ordinaryDirectoryChild_volume]
      exact size
  exact ⟨shape,(congrArg (· * 142080) size).trans weight,layout,ordinaryDirectoryPack_index parent r g w,
    fun word j => ordinaryDirectoryTranspose parent r g w word j⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- On the concatenated directory tape the scheduled transpose is conjugate
to the batch transpose, including at the boundaries between adjacent records. -/
theorem scheduledDirectoryCoordinates (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let parent := role node 142080
    let r := nodeChildren5[i.val]
    let g := 64-r
    let batch := ordinaryDirectoryChild parent r g w
    let child := scheduledChild prime node i
    ∃ e : Fin (volume prime batch) ≃ Fin (volume prime child),
      (∀ k, (CopyChildLayout.packActive child (e k)).val = (CopyChildLayout.packActive batch k).val) ∧
      ∀ {α : Type} (x : Fin (volume prime child) → α),
        Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) (x ∘ e) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ e := by
  intro parent r g batch child
  obtain ⟨_,_,layout,offset,action⟩ := scheduledDirectoryTranspose node i w aligned rows
  let size := ordinaryDirectoryChild_volume parent r g w
  let e := (finCongr size).symm.trans layout
  refine ⟨e,fun k => ?_,?_⟩
  · obtain ⟨j,rfl⟩ := (finCongr size).surjective k
    simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
    exact offset j
  · intro α x
    funext k
    obtain ⟨p,rfl⟩ := (finCongr size).surjective k
    obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective p
    have batchRead := ordinaryDirectoryRowTranspose parent r g w (x ∘ e) j k
    have scheduledRead := action x j k
    simp only [Function.comp_def,e,Equiv.trans_apply,Equiv.symm_apply_apply,finCongr_apply] at batchRead scheduledRead ⊢
    exact batchRead.symm.trans scheduledRead

end IntegerMultBounds.MathlibTM2.M6.BitNode
