import IntegerMultBounds.Machine.RecursiveRowsClean

/-! Reconstruct the actual flat input array from arbitrary literal row words.
This removes any caller-supplied serialization codec when specializing clean
cyclic splitting and merging to delimited coefficient records. -/
namespace IntegerMultBounds.Machine.RecursiveRowsFromWords
noncomputable section
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (groups rowLength pack)
variable {q c : ℕ} {v : Descriptor}

def entry {H B : ℕ} (rs : Fin H → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=B) (h : Fin H) (j : Fin c) (k : Fin B) : Fin (q+4) :=
  (rs h j).get (Fin.cast (hl h j).symm k)

def cells {H B : ℕ} (rs : Fin H → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=B) (i : Fin (H*(c*B))) : Fin (q+4) :=
  let hjk := finProdFinEquiv.symm i
  let jk := finProdFinEquiv.symm hjk.2
  entry rs hl hjk.1 jk.1 jk.2

theorem row_cells {H B : ℕ} (rs : Fin H → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=B) (h : Fin H) (j : Fin c) :
    List.ofFn (fun k : Fin B => cells rs hl (pack h (pack j k)))=rs h j := by
  simp only [cells,pack,Equiv.symm_apply_apply]
  change List.ofFn (fun k => (rs h j).get (Fin.cast (hl h j).symm k))=rs h j
  rw [← List.ofFn_congr (hl h j) (rs h j).get,List.ofFn_get]

def array (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) : Fin (volume q v) → Fin (q+4) :=
  fun i => cells rs hl (Fin.cast (RecursiveInterchangeRows.volume_split q c v hd) i)

theorem rows_array (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    RecursiveInterchangeRows.rows q c v hd (array hd rs hl)=rs := by
  funext h j
  simp only [RecursiveInterchangeRows.rows,RecursiveInterchangeRows.view,array,
    Fin.cast_cast,Fin.cast_eq_self]
  exact row_cells rs hl h j

theorem source_word (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    List.ofFn (array hd rs hl)=CyclicRowSplit.sourceWord rs := by
  rw [← RecursiveInterchangeRows.source_word q c v hd (array hd rs hl),rows_array]

theorem role_word (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) (j : Fin c) :
    List.ofFn (RecursiveInterchangeRows.roleArray q c v hd (array hd rs hl) j)=
      CyclicRowSplit.roleWord rs j := by
  rw [← RecursiveInterchangeRows.role_word q c v hd (array hd rs hl),rows_array]

def sourcePayload (rs : Fin (groups c v) → Fin c → List (Fin (q+4))) : Tapes (1+c) q :=
  CyclicRowCopy.payload (putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord rs)) (fun _ _ => blank) 0 (fun _ => 0)

def rolePayload (rs : Fin (groups c v) → Fin c → List (Fin (q+4))) : Tapes (1+c) q :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => putWord (fun _ => blank) 0 (CyclicRowSplit.roleWord rs j)) 0 (fun _ => 0)

theorem source_payload (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    RecursiveRowsConstruct.sourcePayload (array hd rs hl)=sourcePayload rs := by
  simp only [RecursiveRowsConstruct.sourcePayload,RecursiveRowsConstruct.word,source_word,sourcePayload]

theorem role_payload (hd : c ∣ v.rows) (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    RecursiveRowsMove.rolePayload hd (array hd rs hl)=rolePayload rs := by
  simp only [RecursiveRowsMove.rolePayload,RecursiveRowsConstruct.word,role_word,rolePayload]

/-- Clean destructive splitting of literal words, without a serialization
existence assumption: the input array is constructed from those very words. -/
theorem splits (hq : 2≤q) (hc : 0<c) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    HoareTime (RecursiveRowsClean.splitProgram hq (c:=c))
      (fun w => w=RecursiveRowsClean.bank hs (sourcePayload rs))
      (fun w => w=RecursiveRowsClean.bank hs (rolePayload rs))
      (RecursiveRowsClean.bound c (volume q v)) := by
  have hh := RecursiveRowsClean.split_hoare hq hc hs v hv hp hd (array hd rs hl)
  rw [source_payload,role_payload] at hh
  exact hh

/-- Clean literal inverse merge. Its role sources are physically erased. -/
theorem merges (hq : 2≤q) (hc : 0<c) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (rs : Fin (groups c v) → Fin c → List (Fin (q+4)))
    (hl : ∀ h j,(rs h j).length=rowLength q v) :
    HoareTime (RecursiveRowsClean.mergeProgram hq (Equiv.refl (Fin c)))
      (fun w => w=RecursiveRowsClean.bank hs (rolePayload rs))
      (fun w => w=RecursiveRowsClean.bank hs (sourcePayload rs))
      (RecursiveRowsClean.bound c (volume q v)) := by
  have hh := RecursiveRowsClean.merge_hoare hq (Equiv.refl (Fin c)) hc hs v hv hp hd (array hd rs hl)
  have hm : RecursiveRowsConstruct.mergePayload (Equiv.refl (Fin c)) hd (array hd rs hl)
      (fun _ => blank)=rolePayload rs := by
    simp only [RecursiveRowsConstruct.mergePayload,Equiv.refl_symm,Equiv.refl_apply,
      RecursiveRowsConstruct.word,role_word,rolePayload]
  rw [source_payload,hm] at hh
  exact hh

end
end IntegerMultBounds.Machine.RecursiveRowsFromWords
