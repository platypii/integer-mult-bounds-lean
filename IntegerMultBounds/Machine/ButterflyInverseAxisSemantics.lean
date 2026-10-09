import IntegerMultBounds.Machine.ButterflyInverseAxisSchedule

/-! The physically exchanged inverse merge realizes the inverse Walsh kernel.
All arithmetic stages retain the same grid and signed-width guard; the counted
inverse interval realizes the sign-negated list in the established semantics. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisSemantics
noncomputable section
open ButterflyAxisArray (Array Width Size)
open ButterflyAxisSemantics (Grid grid_initial)
open ButterflyAxisDecoded (decoded)
open Networks

/-- Each charged inverse axis is exactly the existing negative-phase kernel. -/
theorem axis_walsh (D t R p : ℕ) (ht : t<D) (f : Fin (Size D R) → ℂ)
    (x : BinaryWalsh.Address D) (r : Fin R) :
    ButterflyInverseAxisArray.axis D t R p ht f (FlatCoordinateLayout.index x r)=
      BinaryWalsh.kernel (-1) (ButterflyAxisWalsh.direction D t ht)
        (fun y => f (FlatCoordinateLayout.index y r)) x := by
  unfold ButterflyInverseAxisArray.axis
  rw [ButterflyAxisWalsh.translation_index,ButterflyAxisWalsh.axis_walsh,
    BinaryWalsh.kernel_forward,BinaryWalsh.kernel_backward]
  have hd : ButterflyAxisWalsh.direction D t ht+ButterflyAxisWalsh.direction D t ht=0 := by
    funext k
    change ButterflyAxisWalsh.direction D t ht k+ButterflyAxisWalsh.direction D t ht k=0
    have hh : ∀ z : ZMod 2,z+z=0 := by intro z; fin_cases z <;> decide
    exact hh _
  rw [add_assoc,hd,add_zero]
  ring

theorem grid_run (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p 0 f) :
    Grid D R p n (ButterflyInverseAxisSchedule.run D start R p n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht]
    exact ButterflyInverseAxisArray.grid_apply D (start+n) R p n ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R p n f hw) (ih (by omega))

def complexStep (D t R p : ℕ) (f : Fin (Size D R) → ℂ) : Fin (Size D R) → ℂ :=
  if ht : t<D then ButterflyInverseAxisArray.axis D t R p ht f else f

def complexRun (D start R p : ℕ) : ℕ → (Fin (Size D R) → ℂ) → (Fin (Size D R) → ℂ)
  | 0,f => f
  | n+1,f => complexStep D (start+n) R p (complexRun D start R p n f)

theorem decoded_run (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p 0 f) :
    decoded D R p n (ButterflyInverseAxisSchedule.run D start R p n f)=
      complexRun D start R p n (decoded D R p 0 f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht,complexRun,complexStep]
    rw [ButterflyInverseAxisArray.decoded_apply D (start+n) R p n ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R p n f hw)
      (grid_run D start R p n (by omega) f hw hg),ih (by omega)]

/-- Same actual axis order, with every kernel sign negated. -/
def directions (D start n : ℕ) (hfit : start+n≤D) :=
  BinaryWalsh.negateKernels (ButterflyAxisWalsh.directions D start n hfit)

theorem directions_succ (D start n : ℕ) (hfit : start+(n+1)≤D) :
    directions D start (n+1) hfit=directions D start n (by omega)++
      [(-1,ButterflyAxisWalsh.direction D (start+n) (by omega))] := by
  simp only [directions,ButterflyAxisWalsh.directions_succ,BinaryWalsh.negateKernels,
    List.map_append,List.map_cons,List.map_nil]

private theorem kernelRun_append {D : ℕ} (as bs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (as++bs) f=
      BinaryWalsh.kernelRun bs (BinaryWalsh.kernelRun as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

theorem run_walsh (D start R p n : ℕ) (hfit : start+n≤D) (f : Fin (Size D R) → ℂ) (r : Fin R) :
    (fun x => complexRun D start R p n f (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D start n hfit) (fun x => f (FlatCoordinateLayout.index x r)) := by
  induction n with
  | zero => simp [complexRun,directions,ButterflyAxisWalsh.directions,BinaryWalsh.negateKernels,BinaryWalsh.kernelRun]
  | succ n ih =>
    have ht : start+n<D := by omega
    funext x
    simp only [complexRun,complexStep,dite_eq_left ht]
    rw [axis_walsh,ih (by omega),directions_succ,kernelRun_append]
    rfl

theorem decoded_walsh (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f)
    (hn : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (r : Fin R) :
    (fun x => decoded D R p n (ButterflyInverseAxisSchedule.run D start R p n f) (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D start n hfit)
        (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)) := by
  rw [decoded_run D start R p n hfit f hw (grid_initial D R p f hn)]
  exact run_walsh D start R p n hfit _ r

theorem prefixes (D start R p n : ℕ) (hfit : start+n≤D)
    (f : Array D R) (hw : Width D R p f)
    (hn : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (j : ℕ) (hj : j≤n) :
    Width D R p (ButterflyInverseAxisSchedule.run D start R p j f) ∧
    Grid D R p j (ButterflyInverseAxisSchedule.run D start R p j f) ∧
    p+j≤p+D ∧ 4*(2^p*4^j)<2^(ButterflyGuard.halfWidth p D) := by
  exact ⟨ButterflyInverseAxisSchedule.width_run D start R p j f hw,
    grid_run D start R p j (by omega) f hw (grid_initial D R p f hn),
    ButterflyGuard.precision_le p D j (by omega),ButterflyGuard.guard p D j (by omega)⟩

end
end IntegerMultBounds.Machine.ButterflyInverseAxisSemantics
