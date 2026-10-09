import IntegerMultBounds.Machine.CompactRowSplit
import IntegerMultBounds.Compact.Layout

/-! The complete-record endpoint is the compact role equivalence, with the
whole within-row suffix retained. Symbols need not be binary or clean. -/
namespace IntegerMultBounds.Machine.CompactRowArray
noncomputable section
open CompactRowHeaders (descriptor)
open RecursiveInterchangeLayout (volume role)
open RecursiveInterchangeRows (pack)
variable {a c rows l : ℕ}

theorem volume_eq : volume a (descriptor (rows*c) l) = (rows*c)*l := by
  simp [volume,descriptor]

theorem groups_eq (hc : 0 < c) :
    RecursiveInterchangeRows.groups c (descriptor (rows*c) l) = rows := by
  simp [RecursiveInterchangeRows.groups,descriptor,hc]

theorem rowLength_eq : RecursiveInterchangeRows.rowLength a (descriptor (rows*c) l) = l := by
  simp [RecursiveInterchangeRows.rowLength,descriptor]

theorem role_volume_eq (hc : 0 < c) :
    volume a (role (descriptor (rows*c) l) c) = rows*l := by
  rw [RecursiveInterchangeRows.role_volume,groups_eq hc,rowLength_eq]

def sourceArray (x : Fin ((rows*c)*l) → Fin (a+4)) :
    Fin (volume a (descriptor (rows*c) l)) → Fin (a+4) :=
  fun i => x (Fin.cast (volume_eq (a := a)) i)

def roleArray (x : Fin ((rows*c)*l) → Fin (a+4)) (j : Fin c) :
    Fin (rows*l) → Fin (a+4) := fun z =>
  let ik := finProdFinEquiv.symm z
  x (pack (pack ik.1 j) ik.2)

/-- Literal suffix coordinates stay with their complete row. -/
theorem role_entry (x : Fin ((rows*c)*l) → Fin (a+4))
    (j : Fin c) (i : Fin rows) (k : Fin l) :
    roleArray x j (pack i k) =
      x (pack ((IntegerMultBounds.Compact.Layout.splitRows rows c (Fin l)).symm
        (j,(i,k))).1 k) := by
  simp [roleArray,pack,IntegerMultBounds.Compact.Layout.splitRows]

theorem native_roleArray (hc : 0 < c) (x : Fin ((rows*c)*l) → Fin (a+4)) (j : Fin c)
    (z : Fin (volume a (role (descriptor (rows*c) l) c))) :
    RecursiveInterchangeRows.roleArray a c (descriptor (rows*c) l)
      (by simp [descriptor]) (sourceArray x) j z =
      roleArray x j (Fin.cast (role_volume_eq (a := a) hc) z) := by
  let ik := finProdFinEquiv.symm (Fin.cast (RecursiveInterchangeRows.role_volume a c
    (descriptor (rows*c) l)) z)
  have hi : RecursiveInterchangeRows.groups c (descriptor (rows*c) l) = rows := groups_eq hc
  have hk : RecursiveInterchangeRows.rowLength a (descriptor (rows*c) l) = l := rowLength_eq
  have he : finProdFinEquiv.symm (Fin.cast (role_volume_eq (a := a) hc) z) =
      (Fin.cast hi ik.1,Fin.cast hk ik.2) := by
    apply finProdFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change z.val = (pack (Fin.cast hi ik.1) (Fin.cast hk ik.2)).val
    rw [RecursiveInterchangeRows.pack_val]
    have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply
      (Fin.cast (RecursiveInterchangeRows.role_volume a c (descriptor (rows*c) l)) z))
    change (pack ik.1 ik.2).val = z.val at h
    simp only [RecursiveInterchangeRows.pack_val,hk] at h
    exact h.symm
  change x (Fin.cast (volume_eq (a := a)) (Fin.cast _ (pack ik.1 (pack j ik.2)))) = _
  rw [roleArray,he]
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeRows.pack_val]
  simp only [hk]
  ring

theorem native_role_word (hc : 0 < c) (x : Fin ((rows*c)*l) → Fin (a+4)) (j : Fin c) :
    List.ofFn (RecursiveInterchangeRows.roleArray a c (descriptor (rows*c) l)
      (by simp [descriptor]) (sourceArray x) j) = List.ofFn (roleArray x j) := by
  have h := List.ofFn_congr (role_volume_eq (a := a) hc)
    (RecursiveInterchangeRows.roleArray a c (descriptor (rows*c) l)
      (by simp [descriptor]) (sourceArray x) j)
  rw [h]
  apply congrArg List.ofFn
  funext z
  have h := native_roleArray hc x j (Fin.cast (role_volume_eq (a := a) hc).symm z)
  have he : Fin.cast (role_volume_eq (a := a) hc) (Fin.cast (role_volume_eq (a := a) hc).symm z) = z := Fin.ext rfl
  rw [he] at h
  exact h

def inputPayload (x : Fin ((rows*c)*l) → Fin (a+4)) : Tapes (1+c) a :=
  CyclicRowCopy.payload (RecursiveRowsConstruct.word x) (fun _ _ => blank) 0 (fun _ => 0)

def outputPayload (x : Fin ((rows*c)*l) → Fin (a+4)) : Tapes (1+c) a :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => RecursiveRowsConstruct.word (roleArray x j)) 0 (fun _ => 0)

theorem native_input (x : Fin ((rows*c)*l) → Fin (a+4)) :
    RecursiveRowsConstruct.sourcePayload (c := c) (sourceArray x) = inputPayload x := by
  have hw : List.ofFn (sourceArray x) = List.ofFn x := by
    exact (List.ofFn_congr (volume_eq (a := a)) (sourceArray x)).trans (by
      apply congrArg List.ofFn
      funext z
      have he : Fin.cast (volume_eq (a := a)) (Fin.cast (volume_eq (a := a)).symm z) = z := Fin.ext rfl
      exact congrArg x he)
  simp only [RecursiveRowsConstruct.sourcePayload,inputPayload,RecursiveRowsConstruct.word,hw]

theorem native_output (hc : 0 < c) (x : Fin ((rows*c)*l) → Fin (a+4)) :
    RecursiveRowsMove.rolePayload (by simp [descriptor]) (sourceArray x) = outputPayload x := by
  have hw : (fun j : Fin c => RecursiveRowsConstruct.word
      (RecursiveInterchangeRows.roleArray a c (descriptor (rows*c) l)
        (by simp [descriptor]) (sourceArray x) j)) =
      fun j : Fin c => RecursiveRowsConstruct.word (roleArray x j) := by
    funext j
    simp only [RecursiveRowsConstruct.word,native_role_word hc x j]
  exact congrArg (fun f => CyclicRowCopy.payload (a := a) (fun _ => blank) f 0 (fun _ => 0)) hw

/-- One fixed machine realizes the compact complete-row equivalence from
original canonical runtime row, role and record-width headers. -/
theorem splits (ha : 2 ≤ a) (hc : 0 < c) (hr : 0 < rows) (hl : 0 < l)
    (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CompactRowHeaders.originalValues (rows*c) c l i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (x : Fin ((rows*c)*l) → Fin (a+4)) :
    HoareTime (CompactRowSplit.program (c := c) ha)
      (fun w => w = CompactRowSplit.bank (inputPayload x) hs)
      (fun w => w = CompactRowSplit.bank (outputPayload x) hs)
      (RecursiveRowsClean.bound c ((rows*c)*l)+146*((rows*c)+c+l+1)+2) := by
  have hh := CompactRowSplit.splits ha hc (rows*c) l (Nat.mul_pos hr hc) hl
    (by simp) hs hv hcan (sourceArray x)
  simpa only [native_input,native_output hc,volume_eq] using hh


def constant (c : ℕ) :=
  (2+5*RecursiveRowsMove.TapeCount c)*(RecursiveRowsQuotient.constant c+1099)+
    11*RecursiveRowsMove.TapeCount c+590

theorem budget_linear (hc : 0 < c) (hr : 0 < rows) (hl : 0 < l) :
    RecursiveRowsClean.bound c ((rows*c)*l)+146*((rows*c)+c+l+1)+2 ≤
      constant c*((rows*c)*l) := by
  have hR := Nat.mul_pos hr hc
  have hV := Nat.mul_pos hR hl
  have hRV := Nat.le_mul_of_pos_right (rows*c) hl
  have hcR := Nat.le_mul_of_pos_left c hr
  have hlV := Nat.le_mul_of_pos_left l hR
  have hb := RecursiveRowsClean.bound_linear c ((rows*c)*l) hV
  unfold constant
  nlinarith

/-- Including descriptor construction and erasure, the complete split costs
at most a role-count-dependent constant times the literal record volume. -/
theorem splits_linear (ha : 2 ≤ a) (hc : 0 < c) (hr : 0 < rows) (hl : 0 < l)
    (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CompactRowHeaders.originalValues (rows*c) c l i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i))
    (x : Fin ((rows*c)*l) → Fin (a+4)) :
    HoareTime (CompactRowSplit.program (c := c) ha)
      (fun w => w = CompactRowSplit.bank (inputPayload x) hs)
      (fun w => w = CompactRowSplit.bank (outputPayload x) hs)
      (constant c*((rows*c)*l)) :=
  (splits ha hc hr hl hs hv hcan x).consequence (fun _ h => h) (fun _ h => h)
    (budget_linear hc hr hl)


end
end IntegerMultBounds.Machine.CompactRowArray
