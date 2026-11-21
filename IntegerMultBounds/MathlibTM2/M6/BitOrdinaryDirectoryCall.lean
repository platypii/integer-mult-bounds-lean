module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLayout
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScan

/-! Call the recursive transpose once on the packed directory and recover each row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

/-- The input list is the concatenation produced by the row scanner. The
returned tape contains the recursive result for every prepared row, with the
same call budget and the same frame as the directory-wide transpose. -/
theorem ordinaryDirectoryCall_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (f : P) (port : Fin T) (parent : Descriptor) (r g w : ℕ) :
    let W := parent.between*parent.afterD
    let packed := ordinaryChildDescriptor r g w W
    let batch := ordinaryDirectoryChild parent r g w
    let R := LabelMask.records parent
    let size := ordinaryDirectoryChild_volume parent r g w
    let N := (prime^(w+1))^((r+g)+(r+g))*W
    ∀ (ready : ℕ → (Fin N → ZMod 2) → Prop) (rows : List (List (Fin (prime+4))))
      (u : HS T Q prime U) (S : Stacks T prime) (budget : ℕ),
    List.Forall₂ (fun j tape => ∃ word, ready j word ∧
      tape = payloadWord (SparseRoleCircuit.encode ∘ word ∘ ordinaryRecursivePosition r g w W)) (List.range R) rows →
    (∀ z, readAt blank (S.L port) (S.R port) z = readAt blank [] rows.flatten z) →
    (∀ word : Fin (volume prime batch) → ZMod 2, RecordPayload port (fun _ => blank) 0 word S →
      ∃ y F t, y.user = u.user ∧ t ≤ budget ∧ Exec body (body f) (mk u S) t (mk y F) ∧
        RecordPayload port (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
        (∀ k, k ≠ port → F.L k = S.L k ∧ F.R k = S.R k)) →
    ∃ y F t, ∃ out : Fin (volume prime batch) → ZMod 2, y.user = u.user ∧ t ≤ budget+2 ∧
      Exec body (.call f) (mk u S) t (mk y F) ∧ RecordPayload port (fun _ => blank) 0 out F ∧
      (∀ k, k ≠ port → F.L k = S.L k ∧ F.R k = S.R k) ∧
      ∀ j : Fin R, ∃ word, ready j word ∧ ∀ k : Fin (volume prime packed),
        ownerRow size out j k = ordinaryChildOutput (r := r) (g := g) (w := w) word
          (ordinaryRecursivePosition r g w W k) := by
  intro W packed batch R size N ready rows u S budget prepared input child
  let action := fun j (row : Fin (volume prime packed) → ZMod 2) =>
    ∃ word, ready j word ∧ row = word ∘ ordinaryRecursivePosition r g w W
  obtain ⟨before,records,encoded⟩ := ownerRows_pack size (action := action) (rows := rows) (by
    apply prepared.imp
    intro j tape h
    obtain ⟨word,ok,eqn⟩ := h
    exact ⟨_,⟨word,ok,rfl⟩,eqn⟩)
  obtain ⟨y,F,t,user,paid,run,output,frame⟩ := child before (by
    intro z
    rw [sub_zero,input,encoded,← payload_reads]
    simp only [List.map_ofFn]
    rfl)
  refine ⟨y,F,_,_,user,Nat.add_le_add_right paid 2,Exec.call run,output,frame,?_⟩
  intro j
  obtain ⟨word,ok,read⟩ := records j
  refine ⟨word,ok,fun k => ?_⟩
  let cell := fun k : Fin (volume prime packed) => (finProdFinEquiv (j,k)).cast size
  have same : before ∘ cell = word ∘ ordinaryRecursivePosition r g w W := by
    funext k
    have hk := congrFun read k
    rw [ownerRow,dite_eq_left (show j.val < LabelMask.records parent from j.isLt)] at hk
    exact hk
  have returned := ordinaryDirectoryRowTranspose parent r g w before j k
  change Shared50RecursiveNodeRows.transpose _ (before ∘ cell) k = _ at returned
  rw [same] at returned
  rw [ownerRow,dite_eq_left j.isLt,← returned]
  exact ((ordinaryChildOutput_eq_iff word _).mp rfl k).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
