import IntegerMultBounds.Machine.ButterflyAxisKernel
import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Concrete identification with the binary Walsh translation kernel on the
repository's common row-major coordinate layout. The physical least-significant
axis t is the reversed coordinate of the most-significant-first address codec. -/
namespace IntegerMultBounds.Machine.ButterflyAxisWalsh
noncomputable section
open ButterflyAxisArray ButterflyAxisDecoded ButterflyAxisKernel
open ButterflyAxisHeadersGeometry ButterflyAxisHeadersData
open RecursiveInterchangeRows (pack pack_val)
open Networks

def coordinate (D t : ℕ) (ht : t<D) : Fin D := (⟨t,ht⟩ : Fin D).rev

theorem suffix_fields (D t : ℕ) (ht : t<D) : FlatCoordinateLayout.suffixFields (coordinate D t ht)=t := by
  unfold FlatCoordinateLayout.suffixFields coordinate
  simp only [Fin.val_rev]
  omega

theorem prefix_size (D t R p : ℕ) (ht : t<D) :
    RecursiveInterchangeRows.groups 2 (descriptor D t R p)=
      FlatCoordinateLayout.prefixSize (Q := 2) (coordinate D t ht) := by
  rw [groups_eq]
  unfold higher FlatCoordinateLayout.prefixSize coordinate
  simp only [Fin.val_rev]
  congr 1

theorem suffix_size (D t R : ℕ) (ht : t<D) :
    lower t R=FlatCoordinateLayout.suffixSize (Q := 2) (W := R) (coordinate D t ht) := by
  simp only [lower,FlatCoordinateLayout.suffixSize,suffix_fields]

def high (D t R p : ℕ) (ht : t<D) (x : BinaryWalsh.Address D) :
    Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) :=
  Fin.cast (prefix_size D t R p ht).symm
    ⟨FlatCoordinateLayout.prefixIndex x (coordinate D t ht),FlatCoordinateLayout.prefix_lt x _⟩

def low (D t R : ℕ) (ht : t<D) (x : BinaryWalsh.Address D) (r : Fin R) : Fin (lower t R) :=
  Fin.cast (suffix_size D t R ht).symm
    ⟨FlatCoordinateLayout.suffix x (coordinate D t ht) r,FlatCoordinateLayout.suffix_lt x _ r⟩

def digit (z : ZMod 2) : Fin 2 := ⟨z.val,ZMod.val_lt z⟩

/-- The actual packed row coordinate is the common layout's coordinate update. -/
theorem packed_update (D t R p : ℕ) (ht : t<D) (x : BinaryWalsh.Address D) (r : Fin R) (z : ZMod 2) :
    Fin.cast (size_eq D t R p ht) (pack (high D t R p ht x) (pack (digit z) (low D t R ht x r)))=
      FlatCoordinateLayout.index (Function.update x (coordinate D t ht) z) r := by
  apply Fin.ext
  simp only [Fin.val_cast,pack_val,high,low,digit]
  rw [FlatCoordinateLayout.index_update]
  rw [suffix_size D t R ht]
  omega

/-- Swapping the physical binary role is addition of one in the address field. -/
theorem swap_digit (z : ZMod 2) : swapBit (digit z)=digit (z+1) := by
  fin_cases z <;> decide

def direction (D t : ℕ) (ht : t<D) : BinaryWalsh.Address D := Pi.single (coordinate D t ht) 1

theorem add_direction (D t : ℕ) (ht : t<D) (x : BinaryWalsh.Address D) :
    x+direction D t ht=Function.update x (coordinate D t ht) (x (coordinate D t ht)+1) := by
  funext k
  by_cases hk : k=coordinate D t ht
  · subst k; simp [direction]
  · simp [direction,Pi.single_eq_of_ne hk,Function.update_of_ne hk]

/-- The physical partner lookup is the literal binary address translation,
with the trailing polynomial index unchanged. -/
theorem translation_index {α : Type*} (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → α)
    (x : BinaryWalsh.Address D) (r : Fin R) :
    translation D t R p ht f (FlatCoordinateLayout.index x r)=
      f (FlatCoordinateLayout.index (x+direction D t ht) r) := by
  have hx := packed_update D t R p ht x r (x (coordinate D t ht))
  rw [Function.update_eq_self] at hx
  rw [←hx]
  change view D t R p ht (translation D t R p ht f)
    (high D t R p ht x) (digit (x (coordinate D t ht))) (low D t R ht x r)=_
  unfold translation
  rw [view_join]
  unfold view
  rw [swap_digit,packed_update,add_direction]

/-- The full decoded selected-axis operation is exactly the existing Walsh
kernel, for each untouched trailing record coordinate. -/
theorem axis_walsh (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → ℂ)
    (x : BinaryWalsh.Address D) (r : Fin R) :
    axis D t R p ht f (FlatCoordinateLayout.index x r)=
      BinaryWalsh.kernel 1 (direction D t ht) (fun y => f (FlatCoordinateLayout.index y r)) x := by
  rw [axis_kernel,translation_index,BinaryWalsh.kernel_apply,BinaryPhase.phase_one]

/-- Exact ordered kernel list executed by the runtime selected-axis interval. -/
def directions (D start n : ℕ) (hfit : start+n≤D) : List (ZMod 4 × BinaryWalsh.Address D) :=
  List.ofFn (fun i : Fin n => (1,direction D (start+i) (by have := i.isLt; omega)))

theorem directions_length (D start n : ℕ) (hfit : start+n≤D) :
    (directions D start n hfit).length=n := by simp [directions]

theorem directions_succ (D start n : ℕ) (hfit : start+(n+1)≤D) :
    directions D start (n+1) hfit=directions D start n (by omega)++[(1,direction D (start+n) (by omega))] := by
  unfold directions
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl

private theorem kernelRun_append {D : ℕ} (as bs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (as++bs) f=
      BinaryWalsh.kernelRun bs (BinaryWalsh.kernelRun as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

/-- Every trailing polynomial coordinate undergoes precisely the specified
sequence of Walsh kernels in the actual physical execution order. -/
theorem run_walsh (D start R p n : ℕ) (hfit : start+n≤D) (f : Fin (Size D R) → ℂ) (r : Fin R) :
    (fun x => complexRun D start R p n f (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D start n hfit) (fun x => f (FlatCoordinateLayout.index x r)) := by
  induction n with
  | zero => simp [complexRun,directions,BinaryWalsh.kernelRun]
  | succ n ih =>
    have ht : start+n<D := by omega
    funext x
    simp only [complexRun,complexStep,dite_eq_left ht]
    rw [axis_walsh,ih (by omega),directions_succ,kernelRun_append]
    rfl

/-- End-to-end decoded correctness of the native counted interval is stated in
the repository's existing BinaryWalsh semantics and common physical layout. -/
theorem decoded_walsh (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f)
    (hn : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (r : Fin R) :
    (fun x => decoded D R p n (ButterflyAxisSchedule.run D start R p n f) (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D start n hfit)
        (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)) := by
  rw [decoded_run_normalized D start R p n hfit f hw hn]
  exact run_walsh D start R p n hfit _ r

/-- The actual fixed machine computes the claimed kernel sequence within the
paid linear-volume-per-axis budget, including runtime header construction. -/
theorem range_correct (D start R p n : ℕ) (hfit : start+n≤D) (hR : 0<R) (hn : 0<n)
    (f : Array D R) (hw : Width D R p f)
    (hunit : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (bs : List Bool) (hc : Counter.value bs=n) (hb : GrowingCounterData.Canonical bs) :
    HoareTime ButterflyAxisSchedule.rangeProgram
      (fun v => v=ButterflyAxisSchedule.rangeBank D start R p 0 f bs)
      (fun v => v=ButterflyAxisSchedule.rangeBank D start R p n f bs ∧
        ∀ r : Fin R, (fun x => decoded D R p n (ButterflyAxisSchedule.run D start R p n f)
          (FlatCoordinateLayout.index x r))=BinaryWalsh.kernelRun (directions D start n hfit)
            (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)))
      (ButterflyAxisSchedule.constant*ButterflyAxisHeadersBudget.logicalVolume D R p*n) :=
  (ButterflyAxisSchedule.range_runs_linear D start R p n hfit hR hn f hw bs hc hb).consequence
    (fun _ h => h) (fun _ h => ⟨h,fun r => decoded_walsh D start R p n hfit f hw hunit r⟩) le_rfl

/-- The small-dimension fallback counts all axes directly from its original
D header and returns the exact full kernel product with all work tapes blank. -/
theorem all_correct (D R p : ℕ) (hD : 0<D) (hR : 0<R)
    (f : Array D R) (hw : Width D R p f)
    (hunit : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1) :
    HoareTime ButterflyAxisSchedule.allProgram
      (fun v => v=ButterflyAxisSchedule.allBank D R p 0 f)
      (fun v => v=ButterflyAxisSchedule.allBank D R p D f ∧
        ∀ r : Fin R, (fun x => decoded D R p D (ButterflyAxisSchedule.run D 0 R p D f)
          (FlatCoordinateLayout.index x r))=BinaryWalsh.kernelRun (directions D 0 D (by omega))
            (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)))
      (ButterflyAxisSchedule.constant*ButterflyAxisHeadersBudget.logicalVolume D R p*D) :=
  (ButterflyAxisSchedule.all_runs_linear D R p hD hR f hw).consequence
    (fun _ h => h) (fun _ h => ⟨h,fun r => decoded_walsh D 0 R p D (by omega) f hw hunit r⟩) le_rfl

end
end IntegerMultBounds.Machine.ButterflyAxisWalsh
