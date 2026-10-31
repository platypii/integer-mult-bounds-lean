module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData

/-! A proof-only core-indexed view of returned tile rows. It supplies the
publication scheduler's row and padding contracts without another tape pass or
an assumed equality between computed output and a separately chosen row map. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Unselected cores have no row in this class. Selected cores read the actual
returned row at their index in the ordered class. This is not a machine pass. -/
def indexedCoreRows {N B : ℕ} (ks : List ℕ) (hN : ks.length = N)
    (values : Fin N → Fin B → List GaussianInt) (j : Fin B) (k : ℕ) : List GaussianInt :=
  if h : k ∈ ks then values ⟨ks.idxOf k,by rw [←hN]; exact List.idxOf_lt_length_of_mem h⟩ j else []

theorem indexedCoreRows_get {N B : ℕ} (ks : List ℕ) (hN : ks.length = N) (hnodup : ks.Nodup)
    (values : Fin N → Fin B → List GaussianInt) (i : Fin N) (j : Fin B) :
    indexedCoreRows ks hN values j (ks[i.val]'(by rw [hN]; exact i.isLt)) = values i j := by
  simp only [indexedCoreRows,dite_eq_left (List.getElem_mem (show i.val < ks.length by rw [hN]; exact i.isLt)),
    hnodup.idxOf_getElem]

theorem indexedCoreRows_map {N B : ℕ} (ks : List ℕ) (hN : ks.length = N) (hnodup : ks.Nodup)
    (values : Fin N → Fin B → List GaussianInt) (j : Fin B) :
    ks.map (indexedCoreRows ks hN values j) = List.ofFn (fun i => values i j) := by
  apply List.ext_getElem (by simp [hN])
  intro i hi hi'
  simp only [List.getElem_map,List.getElem_ofFn]
  exact indexedCoreRows_get ks hN hnodup values ⟨i,by simpa only [List.length_ofFn] using hi'⟩ j

/-- Transfer any per-row certificate from returned array positions to core keys. -/
theorem indexedCoreRows_forall {N B : ℕ} (ks : List ℕ) (hN : ks.length = N) (hnodup : ks.Nodup)
    (values : Fin N → Fin B → List GaussianInt) (j : Fin B)
    (R : ℕ → List GaussianInt → Prop)
    (h : ∀ i : Fin N, R (ks[i.val]'(by rw [hN]; exact i.isLt)) (values i j)) :
    ∀ k ∈ ks, R k (indexedCoreRows ks hN values j k) := by
  intro k hk
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp hk
  let i : Fin N := ⟨n,by rw [←hN]; exact hn⟩
  have hr := indexedCoreRows_get ks hN hnodup values i j
  change indexedCoreRows ks hN values j ks[n] = values i j at hr
  rw [he] at hr
  rw [hr]
  simpa only [i,he] using h i

namespace CorePublicationClass

theorem indices_nodup {s width : ℕ} (g : CorePublicationClass s width) : g.indices.Nodup :=
  List.Nodup.sublist g.sublist (List.nodup_range.filter _)
end CorePublicationClass

namespace ArchiveTilePlan.Result
variable {s width N B : ℕ} {g : CorePublicationClass s width}
    {values : Fin N → Fin B → List GaussianInt}

def coreRows (_tile : Result g.length values) (hN : g.indices.length = N) : Fin B → ℕ → List GaussianInt :=
  indexedCoreRows g.indices hN values

theorem coreRows_length (tile : Result g.length values) (hN : g.indices.length = N)
    (j : Fin B) (k : ℕ) (hk : k ∈ g.indices) : (tile.coreRows hN j k).length = g.length := by
  apply indexedCoreRows_forall g.indices hN g.indices_nodup values j (fun _ row => row.length = g.length) _ k hk
  intro i
  rw [←tile.realRows i j]
  exact tile.rowLength _ _

def publicationReplica {A : ℕ} (tile : Result g.length values) (hN : g.indices.length = N)
    (ambient : List (Fin (A+4))) (j : Fin B) : PublicationReplica A :=
  ⟨List.ofFn (fun i => tile.padded i j),g.indices.map (tile.coreRows hN j),ambient⟩

/-- All padding premises follow from the actual transpose's returned result. -/
theorem publicationReplica_valid {A : ℕ} (tile : Result g.length values) (hN : g.indices.length = N)
    (w : ℕ) (hw : 0 < width) (ambient : List (Fin (A+4))) (hambient : ambient.length = s*w) (j : Fin B) :
    (tile.publicationReplica hN ambient j).Valid
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist) w (tile.capacity-N) := by
  refine ⟨by simp [publicationReplica,coreSubsetPublicationWindows,PublicationWindows.restrict],?_,?_,?_,?_,hambient⟩
  · intro row hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    exact tile.coreRows_length hN j k hk
  · intro row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact tile.rowLength i j
  · simp only [publicationReplica,List.length_map,List.length_ofFn,hN]
    have := tile.capacity_ge
    omega
  · change (List.ofFn fun i => tile.padded i j).flatten.drop ((tile.capacity-N)*g.length) =
      (g.indices.map (tile.coreRows hN j)).flatten
    rw [coreRows,indexedCoreRows_map g.indices hN g.indices_nodup]
    exact paddedArchiveRows_drop tile.capacity_ge values tile.padded tile.rowLength tile.realRows j

/-- The scheduler consumes exactly the transpose's returned replica-major bytes. -/
theorem publicationReplica_inputs {A : ℕ} (tile : Result g.length values) (hN : g.indices.length = N)
    (w : ℕ) (ambient : Fin B → List (Fin (A+4))) :
    (List.ofFn fun j => tile.publicationReplica hN (ambient j) j).flatMap (PublicationReplica.input w) =
      (List.ofFn fun j => cstream A w (List.ofFn fun i => tile.padded i j).flatten).flatten := by
  simp only [List.flatMap,List.map_ofFn,Function.comp_def,publicationReplica,PublicationReplica.input]

end ArchiveTilePlan.Result
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
