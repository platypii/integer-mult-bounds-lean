import IntegerMultBounds.Machine.CompactComplexNonleafEventProgress
import IntegerMultBounds.Machine.CompactComplexScalarIntegerRows
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema

/-! Genuine child addresses retain outer-row, polynomial and untouched global
binary spectators. Actual network wires occupy the original cyclic row slots.
The selected child interval is supplied by the original recursive call slot. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafChildAddress
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open Networks
open RecursiveInterchangeRows (pack)
abbrev Wire := ComplexFramedExecution.Wire
def roles := Fintype.card Wire
abbrev Index (s : Shape) (rows ell : ℕ) := Fin (ButterflySpectatorGeometry.Size rows s.bits (2^ell))
abbrev Address (k : ℕ) := BinaryColumns.Address arity (arity^k)
abbrev View (s : Shape) (rows ell : ℕ) :=
  (Fin (rows/roles) × Wire) × (BinaryWalsh.Address s.bits × Fin (2^ell))

/-- The actual finite wire order is the same one used by the scalar compiler. -/
def wireIndex : Wire ≃ Fin roles := CompactComplexScalarIntegerRows.wireIndex

attribute [local irreducible] roles wireIndex

def rowLayout (rows : ℕ) (hd : roles ∣ rows) : (Fin (rows/roles) × Wire) ≃ Fin rows :=
  ((Equiv.prodCongr (Equiv.refl _) wireIndex).trans finProdFinEquiv).trans
    (finCongr (Nat.div_mul_cancel hd))

/-- Literal row-major layout: cyclic role is between the outer row and the
complete immutable binary/polynomial suffix. -/
def layout (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows) : View s rows ell ≃ Index s rows ell :=
  (Equiv.prodCongr (rowLayout rows hd) FlatCoordinateLayout.arrayEquiv).trans finProdFinEquiv

theorem layout_val (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (row : Fin (rows/roles)) (wire : Wire) (x : BinaryWalsh.Address s.bits) (poly : Fin (2^ell)) :
    (layout s rows ell hd ((row,wire),(x,poly))).val=
      (row.val*roles+(wireIndex wire).val)*(2^s.bits*2^ell)+(FlatCoordinateLayout.rank x).val*2^ell+poly.val := by
  have hl : layout s rows ell hd ((row,wire),(x,poly))=
    pack (Fin.cast (Nat.div_mul_cancel hd) (pack row (wireIndex wire)))
      (FlatCoordinateLayout.index x poly) := rfl
  rw [hl,RecursiveInterchangeRows.pack_val]
  simp only [Fin.val_cast,RecursiveInterchangeRows.pack_val,FlatCoordinateLayout.index_val]
  omega


variable {s : Shape} {left k : ℕ}

/-- Network slot precedes its residual-column index, as in the retained
node's `slots * f` address geometry. -/
def axisIndex (slot : Fin arity) (column : Fin (arity^k)) : Fin (arity^(k+1)) :=
  Fin.cast (by rw [pow_succ,Nat.mul_comm]) (pack slot column)

def axis (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (i : Fin (arity^(k+1))) : Fin s.bits :=
  ButterflyAxisWalsh.coordinate s.bits
    (CompactSpectatorVisitGeometry.selected s rho.val left i.val)
    (CompactSpectatorVisitGeometry.selected_lt rho visit i)

theorem axis_injective (rho : Fin s.chunk) (visit : Visit s.active left (k+1)) :
    Function.Injective (axis rho visit) := by
  intro i j h
  have he := congrArg Fin.rev h
  have hv := congrArg Fin.val he
  simp only [axis,ButterflyAxisWalsh.coordinate,Fin.rev_rev] at hv
  exact CompactSpectatorVisitGeometry.selected_injective rho visit hv

def flatten (a : Address k) (i : Fin (arity^(k+1))) : ZMod 2 :=
  let z := finProdFinEquiv.symm (Fin.cast (by rw [pow_succ,Nat.mul_comm]) i)
  a z.2 z.1

theorem flatten_axisIndex (a : Address k) (slot : Fin arity) (column : Fin (arity^k)) :
    flatten a (axisIndex slot column)=a column slot := by
  simp [flatten,axisIndex,pack]

def address (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) : Address k :=
  fun column slot => x (axis rho visit (axisIndex slot column))

def insert (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) (a : Address k) : BinaryWalsh.Address s.bits :=
  Function.extend (axis rho visit) (flatten a) x

theorem insert_axis (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) (a : Address k)
    (slot : Fin arity) (column : Fin (arity^k)) :
    insert rho visit x a (axis rho visit (axisIndex slot column))=a column slot := by
  rw [insert,(axis_injective rho visit).extend_apply,flatten_axisIndex]

theorem address_insert (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) (a : Address k) : address rho visit (insert rho visit x a)=a := by
  funext column slot
  exact insert_axis rho visit x a slot column

theorem insert_frame (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) (a : Address k) (t : Fin s.bits)
    (ht : ¬∃ i,axis rho visit i=t) : insert rho visit x a t=x t :=
  Function.extend_apply' _ _ _ ht

theorem insert_address (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (x : BinaryWalsh.Address s.bits) : insert rho visit x (address rho visit x)=x := by
  funext t
  by_cases ht : ∃ i,axis rho visit i=t
  · obtain ⟨i,rfl⟩ := ht
    rw [insert,(axis_injective rho visit).extend_apply]
    have hi := finProdFinEquiv.apply_symm_apply
      (Fin.cast (by rw [pow_succ,Nat.mul_comm] : arity^(k+1)=arity*arity^k) i)
    simpa [flatten,address,axisIndex,pack] using congrArg (fun j => x (axis rho visit
      (Fin.cast (by rw [pow_succ,Nat.mul_comm] : arity*arity^k=arity^(k+1)) j))) hi
  · exact insert_frame rho visit x _ t ht

/-- Every output uses its own genuine surrounding spectators. -/
def inputIndex (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (anchor : Index s rows ell) (wire : Wire) (a : Address k) : Index s rows ell :=
  let v := (layout s rows ell hd).symm anchor
  layout s rows ell hd ((v.1.1,wire),(insert rho visit v.2.1 a,v.2.2))

def outputWire (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (i : Index s rows ell) : Wire := ((layout s rows ell hd).symm i).1.2

def outputAddress (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (i : Index s rows ell) : Address k := address rho visit ((layout s rows ell hd).symm i).2.1

theorem input_output (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1)) (i : Index s rows ell) :
    inputIndex s rows ell hd rho visit i (outputWire s rows ell hd i)
      (outputAddress s rows ell hd rho visit i)=i := by
  simp only [inputIndex,outputWire,outputAddress,insert_address]
  exact (layout s rows ell hd).apply_symm_apply i

/-- The actual call occurrence chooses both the parent role and the child
interval. Equal-looking edges retain their distinct original sites. -/
def selectedRole (call : ComplexRecursiveCallSchema.Call) : Fin roles := wireIndex call.role

theorem childVisit (visit : Visit s.active left (k+2)) (call : ComplexRecursiveCallSchema.Call) :
    Visit s.active (left+call.slot.val*arity^(k+1)) (k+1) := Visit.child visit call.slot

theorem child_position (rho : Fin s.chunk) (visit : Visit s.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call) (slot : Fin arity) (column : Fin (arity^k)) :
    (axis rho (childVisit visit call) (axisIndex slot column)).val=
      s.bits-1-(s.H+s.B+(s.active-1-
        (left+call.coordinate.val*arity^(k+1)+slot.val*arity^k+column.val))*s.chunk+rho.val) := by
  have hi : (axisIndex slot column).val=slot.val*arity^k+column.val := by
    simp only [axisIndex,Fin.val_cast,RecursiveInterchangeRows.pack_val]
  simp only [axis,ButterflyAxisWalsh.coordinate,Fin.val_rev,
    CompactSpectatorVisitGeometry.selected,hi,ComplexRecursiveCallSchema.slot_val]
  rw [show left+call.coordinate.val*arity^(k+1)+(slot.val*arity^k+column.val)=
    left+call.coordinate.val*arity^(k+1)+slot.val*arity^k+column.val by omega]
  omega


/-- The input wire lookup is the actual role splitter's cyclic address,
including the complete binary and polynomial suffix. -/
theorem role_layout (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (row : Fin (rows/roles)) (wire : Wire) (x : BinaryWalsh.Address s.bits) (poly : Fin (2^ell)) :
    CompactNativeRoleReservedBridge.role s rows roles ell hd f (wireIndex wire)
      (pack row (FlatCoordinateLayout.index x poly))=
      f (layout s rows ell hd ((row,wire),(x,poly))) := by
  refine (CompactNativeRoleReservedBridge.global_index s rows roles ell hd f row (wireIndex wire)
    (FlatCoordinateLayout.index x poly)).trans ?_
  apply congrArg f
  apply Fin.ext
  change (pack (pack row (wireIndex wire)) (FlatCoordinateLayout.index x poly)).val=
    (layout s rows ell hd ((row,wire),(x,poly))).val
  simp only [RecursiveInterchangeRows.pack_val,FlatCoordinateLayout.index_val,layout_val]
  omega

/-- Actual input lookup changes only the wire and child-selected address.
Its old outer row and polynomial spectator are recovered literally. -/
theorem input_index_view (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (anchor : Index s rows ell) (wire : Wire) (a : Address k) :
    (layout s rows ell hd).symm (inputIndex s rows ell hd rho visit anchor wire a)=
      ((((layout s rows ell hd).symm anchor).1.1,wire),
        (insert rho visit ((layout s rows ell hd).symm anchor).2.1 a,
          ((layout s rows ell hd).symm anchor).2.2)) := by
  exact (layout s rows ell hd).symm_apply_apply _

/-- Grid propagation uses concrete address maps on every genuine spectator
slice. Only the completed child execution equality remains for induction. -/
theorem selected_grid (s : Shape) (rows ell q n M : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (before child : CompactSpectatorVisitGeometry.Array s rows ell)
    (hg : CompactSpectatorInheritedGrid.Grid s rows ell q n M before)
    (hcompleted : ∀ i,CompactSpectatorInheritedGrid.decoded s rows ell q
      (n+2*arity^(k+1)) child i=
      FramedCircuit.run (ComplexFramedExecution.network (arity^k))
        (fun wire a => CompactSpectatorInheritedGrid.decoded s rows ell q n before
          (inputIndex s rows ell hd rho visit i wire a))
        (outputWire s rows ell hd i) (outputAddress s rows ell hd rho visit i)) :
    CompactSpectatorInheritedGrid.Grid s rows ell q (n+2*arity^(k+1))
      (M*4^(2*arity^(k+1))) child := by
  intro i
  rw [hcompleted]
  exact CompactComplexDenominatorPolicy.network_grid n k M _
    (fun wire a => hg (inputIndex s rows ell hd rho visit i wire a))
    (outputWire s rows ell hd i) (outputAddress s rows ell hd rho visit i)

/-- Rejoining the genuine returned network wires reconstructs the selected
parent stream without changing any binary or polynomial address. -/
def returned (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (streams : Wire → CompactSpectatorVisitGeometry.Array s (rows/roles) ell) :
    CompactSpectatorVisitGeometry.Array s rows ell :=
  CompactComplexStoppedEventProgress.reserved s rows roles ell hd
    (fun j => streams (wireIndex.symm j))

theorem returned_layout (s : Shape) (rows ell : ℕ) (hd : roles ∣ rows)
    (streams : Wire → CompactSpectatorVisitGeometry.Array s (rows/roles) ell)
    (row : Fin (rows/roles)) (wire : Wire) (x : BinaryWalsh.Address s.bits) (poly : Fin (2^ell)) :
    returned s rows ell hd streams (layout s rows ell hd ((row,wire),(x,poly)))=
      streams wire (pack row (FlatCoordinateLayout.index x poly)) := by
  rw [←role_layout s rows ell hd (returned s rows ell hd streams) row wire x poly]
  unfold returned
  rw [CompactComplexStoppedEventProgress.reserved_role,Equiv.symm_apply_apply]

theorem returned_decoded (s : Shape) (rows ell q n : ℕ) (hd : roles ∣ rows)
    (streams : Wire → CompactSpectatorVisitGeometry.Array s (rows/roles) ell)
    (i : Index s rows ell) :
    CompactSpectatorInheritedGrid.decoded s rows ell q n (returned s rows ell hd streams) i=
      CompactSpectatorInheritedGrid.decoded s (rows/roles) ell q n
        (streams (outputWire s rows ell hd i))
        (pack ((layout s rows ell hd).symm i).1.1
          (FlatCoordinateLayout.index ((layout s rows ell hd).symm i).2.1
            ((layout s rows ell hd).symm i).2.2)) := by
  unfold CompactSpectatorInheritedGrid.decoded
  apply congrArg (ButterflyStreamSemantics.decode (CompactSpectatorInheritedGrid.half s q) n)
  have h := returned_layout s rows ell hd streams ((layout s rows ell hd).symm i).1.1
    ((layout s rows ell hd).symm i).1.2 ((layout s rows ell hd).symm i).2.1
    ((layout s rows ell hd).symm i).2.2
  change returned s rows ell hd streams (layout s rows ell hd ((layout s rows ell hd).symm i))=_ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- Input decoding agrees with the exact cyclic role word of the source-ready
selected stream, after overriding only its actual child address coordinates. -/
theorem input_role_decoded (s : Shape) (rows ell q n : ℕ) (hd : roles ∣ rows)
    (rho : Fin s.chunk) (visit : Visit s.active left (k+1))
    (before : CompactSpectatorVisitGeometry.Array s rows ell)
    (anchor : Index s rows ell) (wire : Wire) (a : Address k) :
    CompactSpectatorInheritedGrid.decoded s rows ell q n before
        (inputIndex s rows ell hd rho visit anchor wire a)=
      CompactSpectatorInheritedGrid.decoded s (rows/roles) ell q n
        (CompactNativeRoleReservedBridge.role s rows roles ell hd before (wireIndex wire))
        (pack ((layout s rows ell hd).symm anchor).1.1
          (FlatCoordinateLayout.index (insert rho visit ((layout s rows ell hd).symm anchor).2.1 a)
            ((layout s rows ell hd).symm anchor).2.2)) := by
  unfold CompactSpectatorInheritedGrid.decoded inputIndex
  apply congrArg (ButterflyStreamSemantics.decode (CompactSpectatorInheritedGrid.half s q) n)
  exact (role_layout s rows ell hd before _ wire _ _).symm

end
end IntegerMultBounds.Machine.CompactComplexNonleafChildAddress
