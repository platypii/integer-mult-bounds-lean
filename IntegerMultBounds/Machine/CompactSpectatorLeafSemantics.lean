import IntegerMultBounds.Machine.CompactSpectatorLeafGuardHeaders
import IntegerMultBounds.Machine.CompactSpectatorLeafLoop
import IntegerMultBounds.Machine.CompactSpectatorInverseLeafLoop
import IntegerMultBounds.Machine.ButterflyInverseAxisCorrect

/-! The actual sparse leaf's ordered full-address axes realize its literal Walsh
kernel list for every outer row and polynomial spectator. Every prefix advances
precision, carries its own numerator grid and uses the original fixed two-pass
signed width. The inverse consumes the forward grid without normalization. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open ButterflyIndependentGuardHeaders (reservation)
open ButterflySpectatorSemantics (Width Grid decoded)
open Networks
variable (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)

abbrev forward (n : ℕ) (f : Array s rows ell) :=
  CompactSpectatorLeafLoop.run s rows ell (reservation s.bits q) rho visit n f
abbrev inverse (n : ℕ) (f : Array s rows ell) :=
  CompactSpectatorInverseLeafLoop.run s rows ell (reservation s.bits q) rho visit n f

def position (_visit : Visit s.active left k) (i : Fin (arity^k)) := CompactSpectatorLeafHeaders.selected s rho.val (left+i.val)
theorem position_lt (i : Fin (arity^k)) : position s rho visit i<s.bits := by
  simpa [position,CompactSpectatorLeafHeaders.selected,CompactSpectatorVisitGeometry.selected] using
    CompactSpectatorVisitGeometry.selected_lt rho visit i

include rho visit in
theorem count_le_bits : arity^k≤s.bits := by
  have hf := visit.fits
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have hm : s.active≤s.active*s.chunk := Nat.le_mul_of_pos_right _ hK
  unfold Shape.bits
  omega

def directions (n : ℕ) (hn : n≤arity^k) : List (ZMod 4 × BinaryWalsh.Address s.bits) :=
  List.ofFn (fun i : Fin n => (1,ButterflyAxisWalsh.direction s.bits
    (position s rho visit ⟨i.val,lt_of_lt_of_le i.isLt hn⟩) (position_lt s rho visit _)))

theorem directions_succ (n : ℕ) (hn : n+1≤arity^k) :
    directions s rho visit (n+1) hn=directions s rho visit n (by omega)++
      [(1,ButterflyAxisWalsh.direction s.bits (position s rho visit ⟨n,by omega⟩) (position_lt s rho visit _))] := by
  unfold directions
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl

private theorem kernelRun_append {D : ℕ} (xs ys : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (xs++ys) f=
      BinaryWalsh.kernelRun ys (BinaryWalsh.kernelRun xs f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem forward_grid (n j : ℕ) (hn : n≤arity^k) (hj : j+n≤2*s.bits)
    (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f) (hg : Grid rows s.bits (2^ell) q j f) :
    Grid rows s.bits (2^ell) q (j+n) (forward s rows ell q rho visit n f) := by
  induction n with
  | zero => simpa only [forward,CompactSpectatorLeafLoop.run,Nat.add_zero] using hg
  | succ n ih =>
    have hi : n<arity^k := by omega
    simp only [forward,CompactSpectatorLeafLoop.run,dite_eq_left hi]
    have hh := ButterflySpectatorSemantics.forward_grid rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) q (j+n) (position_lt s rho visit _) (by omega)
      (forward s rows ell q rho visit n f)
      (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit n f hw)
      (ih (by omega) (by omega))
    simpa only [position,CompactSpectatorLeafAxis.result,Nat.add_assoc] using hh

theorem inverse_grid (n j : ℕ) (hn : n≤arity^k) (hj : j+n≤2*s.bits)
    (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f) (hg : Grid rows s.bits (2^ell) q j f) :
    Grid rows s.bits (2^ell) q (j+n) (inverse s rows ell q rho visit n f) := by
  induction n with
  | zero => simpa only [inverse,CompactSpectatorInverseLeafLoop.run,Nat.add_zero] using hg
  | succ n ih =>
    have hi : n<arity^k := by omega
    simp only [inverse,CompactSpectatorInverseLeafLoop.run,dite_eq_left hi]
    have hh := ButterflySpectatorSemantics.inverse_grid rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) q (j+n) (position_lt s rho visit _) (by omega)
      (inverse s rows ell q rho visit n f)
      (CompactSpectatorInverseLeafLoop.width_run s rows ell (reservation s.bits q) rho visit n f hw)
      (ih (by omega) (by omega))
    simpa only [position,CompactSpectatorInverseLeafAxis.result,Nat.add_assoc] using hh

theorem forward_walsh (n j : ℕ) (hn : n≤arity^k) (hj : j+n≤2*s.bits)
    (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f) (hg : Grid rows s.bits (2^ell) q j f)
    (row : Fin rows) (poly : Fin (2^ell)) :
    (fun x => decoded rows s.bits (2^ell) q (j+n) (forward s rows ell q rho visit n f)
      (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
      BinaryWalsh.kernelRun (directions s rho visit n hn)
        (fun x => decoded rows s.bits (2^ell) q j f
          (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  induction n with
  | zero => simp [forward,CompactSpectatorLeafLoop.run,directions,BinaryWalsh.kernelRun]
  | succ n ih =>
    have hi : n<arity^k := by omega
    have hd := ButterflySpectatorSemantics.forward_decoded rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) q (j+n) (position_lt s rho visit _) (by omega)
      (forward s rows ell q rho visit n f)
      (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit n f hw)
      (forward_grid s rows ell q rho visit n j (by omega) (by omega) f hw hg)
    have hd' : decoded rows s.bits (2^ell) q (j+(n+1)) (forward s rows ell q rho visit (n+1) f)=
        ButterflySpectatorSemantics.axis rows s.bits (position s rho visit ⟨n,hi⟩)
          (2^ell) (reservation s.bits q) (position_lt s rho visit _)
          (decoded rows s.bits (2^ell) q (j+n) (forward s rows ell q rho visit n f)) := by
      simpa only [forward,CompactSpectatorLeafLoop.run,dite_eq_left hi,position,
        CompactSpectatorLeafAxis.result,Nat.add_assoc] using hd
    rw [hd']
    have ha := congrFun (ButterflySpectatorSemantics.axis_row rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) (reservation s.bits q) (position_lt s rho visit _)
      (decoded rows s.bits (2^ell) q (j+n) (forward s rows ell q rho visit n f)) row)
    funext x
    rw [ha (FlatCoordinateLayout.index x poly),ButterflyAxisWalsh.axis_walsh,
      ih (by omega) (by omega),directions_succ,kernelRun_append]
    rfl

theorem inverse_walsh (n j : ℕ) (hn : n≤arity^k) (hj : j+n≤2*s.bits)
    (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f) (hg : Grid rows s.bits (2^ell) q j f)
    (row : Fin rows) (poly : Fin (2^ell)) :
    (fun x => decoded rows s.bits (2^ell) q (j+n) (inverse s rows ell q rho visit n f)
      (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
      BinaryWalsh.kernelRun (BinaryWalsh.negateKernels (directions s rho visit n hn))
        (fun x => decoded rows s.bits (2^ell) q j f
          (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  induction n with
  | zero => simp [inverse,CompactSpectatorInverseLeafLoop.run,directions,BinaryWalsh.negateKernels,BinaryWalsh.kernelRun]
  | succ n ih =>
    have hi : n<arity^k := by omega
    have hd := ButterflySpectatorSemantics.inverse_decoded rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) q (j+n) (position_lt s rho visit _) (by omega)
      (inverse s rows ell q rho visit n f)
      (CompactSpectatorInverseLeafLoop.width_run s rows ell (reservation s.bits q) rho visit n f hw)
      (inverse_grid s rows ell q rho visit n j (by omega) (by omega) f hw hg)
    have hd' : decoded rows s.bits (2^ell) q (j+(n+1)) (inverse s rows ell q rho visit (n+1) f)=
        ButterflySpectatorSemantics.inverseAxis rows s.bits (position s rho visit ⟨n,hi⟩)
          (2^ell) (reservation s.bits q) (position_lt s rho visit _)
          (decoded rows s.bits (2^ell) q (j+n) (inverse s rows ell q rho visit n f)) := by
      simpa only [inverse,CompactSpectatorInverseLeafLoop.run,dite_eq_left hi,position,
        CompactSpectatorInverseLeafAxis.result,Nat.add_assoc] using hd
    rw [hd']
    have ha := congrFun (ButterflySpectatorSemantics.inverse_row rows s.bits
      (position s rho visit ⟨n,hi⟩) (2^ell) (reservation s.bits q) (position_lt s rho visit _)
      (decoded rows s.bits (2^ell) q (j+n) (inverse s rows ell q rho visit n f)) row)
    funext x
    rw [ha (FlatCoordinateLayout.index x poly),ButterflyInverseAxisSemantics.axis_walsh,
      ih (by omega) (by omega),directions_succ]
    simp only [BinaryWalsh.negateKernels,List.map_append,List.map_cons,List.map_nil,kernelRun_append]
    rfl

def result (f : Array s rows ell) := inverse s rows ell q rho visit (arity^k)
  (forward s rows ell q rho visit (arity^k) f)

theorem roundtrip_decoded (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f)
    (hu : ∀ i,‖decoded rows s.bits (2^ell) q 0 f i‖≤1) (row : Fin rows) (poly : Fin (2^ell)) :
    (fun x => decoded rows s.bits (2^ell) q (2*arity^k) (result s rows ell q rho visit f)
      (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
      (fun x => decoded rows s.bits (2^ell) q 0 f
        (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  have hb := count_le_bits s rho visit
  have hg := ButterflySpectatorSemantics.initial_grid rows s.bits (2^ell) q f hu
  have hf := forward_walsh s rows ell q rho visit (arity^k) 0 (by omega) (by omega) f hw hg row poly
  have hi := inverse_walsh s rows ell q rho visit (arity^k) (arity^k) (by omega) (by omega)
    (forward s rows ell q rho visit (arity^k) f)
    (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit (arity^k) f hw)
    (by simpa only [Nat.zero_add] using forward_grid s rows ell q rho visit (arity^k) 0 (by omega) (by omega) f hw hg) row poly
  simp only [Nat.zero_add] at hf
  rw [hf,ButterflyInverseAxisCorrect.kernelRun_inverse] at hi
  simpa only [←two_mul,result] using hi


/-- All outer rows, global coordinates and polynomial spectators are covered;
the decoded whole physical array returns exactly to its original values. -/
theorem roundtrip_whole (f : Array s rows ell) (hw : Width rows s.bits (2^ell) q f)
    (hu : ∀ i,‖decoded rows s.bits (2^ell) q 0 f i‖≤1) :
    decoded rows s.bits (2^ell) q (2*arity^k) (result s rows ell q rho visit f)=
      decoded rows s.bits (2^ell) q 0 f := by
  funext i
  obtain ⟨⟨row,z⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨x,poly⟩,hx⟩ := (FlatCoordinateLayout.arrayEquiv (d:=s.bits) (Q:=2) (W:=2^ell)).surjective z
  change FlatCoordinateLayout.index x poly=z at hx
  subst z
  exact congrFun (roundtrip_decoded s rows ell q rho visit f hw hu row poly) x

end
end IntegerMultBounds.Machine.CompactSpectatorLeafSemantics
