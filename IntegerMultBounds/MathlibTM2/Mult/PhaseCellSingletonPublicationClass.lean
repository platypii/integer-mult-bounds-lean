module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPublicationClasses
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonPublicationReplicas

/-! Identify executed singleton replica publication with the class fold's
output operation, including clipped cores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {A s width k : ℕ}

def singletonCoreWindows (hw : 0 < width) (hk : k ∈ coreIndices s width) :
    PublicationWindows s (coreLength s width k) :=
  coreSubsetPublicationWindows s width (coreLength s width k) hw [k]
    (singletonCorePublication s width k hk).sublist

@[simp] theorem singletonCoreWindows_origins (hw : 0 < width) (hk : k ∈ coreIndices s width) :
    (singletonCoreWindows hw hk).origins = [coreStart width k] := rfl

/-- The replica executor and the restoring class fold describe identical bytes. -/
theorem singletonPublication_class_output (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (W : ℕ) (row : List GaussianInt) (ambient : List (Fin (A+4))) :
    PublicationReplica.output (singletonCoreWindows hw hk) W
      (⟨[row],[row],ambient⟩ : PublicationReplica A) =
      (singletonCorePublication s width k hk).output W hw (fun _ => row) ambient := by
  simp [PublicationReplica.output,PublicationReplica.words,CorePublicationClass.output,
    singletonCorePublication,singletonCoreWindows]

/-- Archive publication is the same pointwise class update on each ambient
replica. Structural recursion avoids expanding concrete replica banks. -/
theorem singletonPublicationReplicas_class_output
    (hw : 0 < width) (hk : k ∈ coreIndices s width) (W : ℕ)
    (rows : List (List GaussianInt)) (ambient : List (List (Fin (A+4)))) :
    (singletonPublicationReplicas rows ambient).flatMap
      (PublicationReplica.output (singletonCoreWindows hw hk) W) =
      (List.zipWith (fun row line =>
        (singletonCorePublication s width k hk).output W hw (fun _ => row) line)
        rows ambient).flatten := by
  induction rows generalizing ambient with
  | nil => simp [singletonPublicationReplicas]
  | cons row rows ih =>
    cases ambient with
    | nil => simp [singletonPublicationReplicas]
    | cons line ambient =>
      simp only [singletonPublicationReplicas,List.zipWith_cons_cons,List.flatMap_cons,
        List.flatten_cons,singletonPublication_class_output]
      exact congrArg ((singletonCorePublication s width k hk).output W hw (fun _ => row) line ++ ·)
        (ih ambient)

private theorem zipWith_ofFn_eq {α β γ : Type} (f : α → β → γ) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    List.zipWith f (List.ofFn x) (List.ofFn y) = List.ofFn (fun j => f (x j) (y j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.zipWith_cons_cons]
    exact congrArg (f (x 0) (y 0) :: ·) (ih (fun j => x j.succ) (fun j => y j.succ))

/-- Directly matches the ambient bank representation of
restoringPublicationClasses_exec_within. -/
theorem singletonPublicationReplicas_ofFn_output {B : ℕ}
    (hw : 0 < width) (hk : k ∈ coreIndices s width) (W : ℕ)
    (rows : Fin B → List GaussianInt) (ambient : Fin B → List (Fin (A+4))) :
    (singletonPublicationReplicas (List.ofFn rows) (List.ofFn ambient)).flatMap
      (PublicationReplica.output (singletonCoreWindows hw hk) W) =
      (List.ofFn fun j =>
        (singletonCorePublication s width k hk).output W hw (fun _ => rows j) (ambient j)).flatten := by
  rw [singletonPublicationReplicas_class_output,zipWith_ofFn_eq]

/-- Whole-bank publication preserves ambient byte volume, including an empty
replica bank. This is the boundary-stock fact needed by sequence composition. -/
theorem singletonPublication_class_length (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (W : ℕ) (rows : List (List GaussianInt)) (ambient : List (List (Fin (A+4))))
    (hlen : rows.length = ambient.length)
    (hrows : ∀ row ∈ rows, row.length = coreLength s width k)
    (hambient : ∀ line ∈ ambient, line.length = s*W) :
    (List.zipWith (fun row line =>
      (singletonCorePublication s width k hk).output W hw (fun _ => row) line)
      rows ambient).flatten.length = ambient.flatten.length := by
  let windows := singletonCoreWindows hw hk
  obtain ⟨hn,_,_,_,hvalid⟩ := singletonPublicationReplicas_spec windows
    (by simp [windows]) W rows ambient hlen hrows hambient
  let replicas := singletonPublicationReplicas rows ambient
  change replicas.length = rows.length at hn
  have houtputs : ∀ line ∈ replicas.map (PublicationReplica.output windows W), line.length = s*W := by
    intro line hline
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hline
    exact (hvalid r hr).output_length
  rw [←singletonPublicationReplicas_class_output hw hk W rows ambient]
  change (replicas.map (PublicationReplica.output windows W)).flatten.length = ambient.flatten.length
  rw [length_flatten_const _ houtputs,length_flatten_const _ hambient,List.length_map,hn,hlen]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
