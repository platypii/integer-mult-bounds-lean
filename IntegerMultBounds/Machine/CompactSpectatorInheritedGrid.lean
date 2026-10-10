import IntegerMultBounds.Machine.ButterflyInheritedStream
import IntegerMultBounds.Machine.CompactSpectatorLeafSemantics
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardOriginal
import IntegerMultBounds.Machine.CompactRecursiveDependencyBudget
import IntegerMultBounds.Machine.CompactNativeRoleChildPrecision

/-! Actual inherited dyadic precision is independent of the baseline metadata
which fixes the stored signed width. Directional leaf arithmetic consumes the
existing words without normalization or resizing. Controller propagation of
the inherited precision and Path remains separate. -/
namespace IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry CompactRecursiveDependencyBudget
open CompactSpectatorVisitGeometry (Array)
open Networks Networks.GaussianPrecision
open ButterflyIndependentGuardHeaders (reservation)

abbrev half (s : Shape) (q : ℕ) := ButterflyGuard.halfWidth q (2*s.bits)
def decoded (s : Shape) (rows ell q n : ℕ) (f : Array s rows ell) :=
  fun i => ButterflyStreamSemantics.decode (half s q) n (f i)
def Grid (s : Shape) (rows ell q n M : ℕ) (f : Array s rows ell) :=
  ∀ i,BoundedGrid n M (decoded s rows ell q n f i)
abbrev Width (s : Shape) (rows ell q : ℕ) (f : Array s rows ell) :=
  ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f

 theorem guard_mono (b M r t : ℕ) (hrt : r≤t) (hg : 4*(M*4^t)<2^b) :
    4*(M*4^r)<2^b := by
  exact (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left M
    (Nat.pow_le_pow_right (by decide : 0<4) hrt))).trans_lt hg

theorem axis_grid (s : Shape) (rows ell q n M t : ℕ) (ht : t<s.bits)
    (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n M f) (hguard : 4*M<2^(half s q)) :
    Grid s rows ell q (n+1) (4*M)
      (ButterflySpectatorGeometry.applyAxis rows s.bits t (2^ell) (reservation s.bits q) ht f) := by
  intro i
  unfold decoded ButterflySpectatorGeometry.applyAxis ButterflySpectatorGeometry.unshape
    ButterflyAxisSerialization.joined ButterflyStreamSemantics.transformed ButterflySpectatorGeometry.reshape
  apply ButterflyInheritedStream.result_grid _ _ (half s q) n M
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · exact hg _
  · exact hg _
  · exact hguard

theorem inverse_axis_grid (s : Shape) (rows ell q n M t : ℕ) (ht : t<s.bits)
    (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n M f) (hguard : 4*M<2^(half s q)) :
    Grid s rows ell q (n+1) (4*M)
      (ButterflyInverseSpectatorGeometry.applyAxis rows s.bits t (2^ell) (reservation s.bits q) ht f) := by
  intro i
  unfold decoded ButterflyInverseSpectatorGeometry.applyAxis ButterflySpectatorGeometry.unshape
    ButterflyAxisSerialization.joined ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped
    ButterflyStreamSemantics.transformed ButterflySpectatorGeometry.reshape
  apply ButterflyInheritedStream.result_grid _ _ (half s q) n M
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · exact hg _
  · exact hg _
  · exact hguard

theorem axis_decoded (s : Shape) (rows ell q n M t : ℕ) (ht : t<s.bits)
    (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n M f) (hguard : 4*M<2^(half s q)) :
    decoded s rows ell q (n+1)
      (ButterflySpectatorGeometry.applyAxis rows s.bits t (2^ell) (reservation s.bits q) ht f)=
      ButterflySpectatorSemantics.axis rows s.bits t (2^ell) (reservation s.bits q) ht
        (decoded s rows ell q n f) := by
  funext i
  unfold decoded ButterflySpectatorGeometry.applyAxis ButterflySpectatorGeometry.unshape
    ButterflyAxisSerialization.joined ButterflyStreamSemantics.transformed
    ButterflySpectatorSemantics.axis ButterflySpectatorSemantics.join ButterflySpectatorSemantics.view
    ButterflySpectatorGeometry.reshape
  apply ButterflyInheritedStream.result_decode _ _ (half s q) n M
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · exact hg _
  · exact hg _
  · exact hguard

theorem inverse_axis_decoded (s : Shape) (rows ell q n M t : ℕ) (ht : t<s.bits)
    (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n M f) (hguard : 4*M<2^(half s q)) :
    decoded s rows ell q (n+1)
      (ButterflyInverseSpectatorGeometry.applyAxis rows s.bits t (2^ell) (reservation s.bits q) ht f)=
      ButterflySpectatorSemantics.inverseAxis rows s.bits t (2^ell) (reservation s.bits q) ht
        (decoded s rows ell q n f) := by
  unfold ButterflySpectatorSemantics.inverseAxis
  funext i
  unfold decoded ButterflyInverseSpectatorGeometry.applyAxis ButterflySpectatorGeometry.unshape
    ButterflyAxisSerialization.joined ButterflyInverseAxisRouting.transformed ButterflyInverseAxisRouting.swapped
    ButterflyStreamSemantics.transformed ButterflySpectatorSemantics.join ButterflySpectatorSemantics.view
    ButterflySpectatorGeometry.reshape
  apply ButterflyInheritedStream.result_decode _ _ (half s q) n M
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw _
  · exact hg _
  · exact hg _
  · exact hguard

abbrev forward := CompactSpectatorLeafSemantics.forward
abbrev inverse := CompactSpectatorLeafSemantics.inverse
open CompactSpectatorLeafSemantics (position position_lt directions directions_succ)

variable (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
  (visit : Visit s.active left k)

theorem forward_grid (t n M : ℕ) (ht : t≤arity^k) (f : Array s rows ell)
    (hw : Width s rows ell q f) (hg : Grid s rows ell q n M f)
    (hguard : 4*(M*4^t)<2^(half s q)) :
    Grid s rows ell q (n+t) (M*4^t) (forward s rows ell q rho visit t f) := by
  induction t with
  | zero => simpa only [forward,CompactSpectatorLeafSemantics.forward,CompactSpectatorLeafLoop.run,Nat.add_zero,pow_zero,Nat.mul_one] using hg
  | succ t ih =>
    have hi : t<arity^k := by omega
    have hprev := ih (by omega) (guard_mono _ M t (t+1) (by omega) hguard)
    have hh := axis_grid s rows ell q (n+t) (M*4^t)
      (position s rho visit ⟨t,hi⟩) (position_lt s rho visit _)
      (forward s rows ell q rho visit t f)
      (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit t f hw)
      hprev (guard_mono _ M t (t+1) (by omega) hguard)
    simpa only [forward,CompactSpectatorLeafSemantics.forward,CompactSpectatorLeafLoop.run,dite_eq_left hi,position,
      CompactSpectatorLeafAxis.result,Nat.add_assoc,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem inverse_grid (t n M : ℕ) (ht : t≤arity^k) (f : Array s rows ell)
    (hw : Width s rows ell q f) (hg : Grid s rows ell q n M f)
    (hguard : 4*(M*4^t)<2^(half s q)) :
    Grid s rows ell q (n+t) (M*4^t) (inverse s rows ell q rho visit t f) := by
  induction t with
  | zero => simpa only [inverse,CompactSpectatorLeafSemantics.inverse,CompactSpectatorInverseLeafLoop.run,Nat.add_zero,pow_zero,Nat.mul_one] using hg
  | succ t ih =>
    have hi : t<arity^k := by omega
    have hprev := ih (by omega) (guard_mono _ M t (t+1) (by omega) hguard)
    have hh := inverse_axis_grid s rows ell q (n+t) (M*4^t)
      (position s rho visit ⟨t,hi⟩) (position_lt s rho visit _)
      (inverse s rows ell q rho visit t f)
      (CompactSpectatorInverseLeafLoop.width_run s rows ell (reservation s.bits q) rho visit t f hw)
      hprev (guard_mono _ M t (t+1) (by omega) hguard)
    simpa only [inverse,CompactSpectatorLeafSemantics.inverse,CompactSpectatorInverseLeafLoop.run,dite_eq_left hi,position,
      CompactSpectatorInverseLeafAxis.result,Nat.add_assoc,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

private theorem kernelRun_append {D : ℕ} (xs ys : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (xs++ys) f=
      BinaryWalsh.kernelRun ys (BinaryWalsh.kernelRun xs f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem forward_walsh (t n M : ℕ) (ht : t≤arity^k) (f : Array s rows ell)
    (hw : Width s rows ell q f) (hg : Grid s rows ell q n M f)
    (hguard : 4*(M*4^t)<2^(half s q)) (row : Fin rows) (poly : Fin (2^ell)) :
    (fun x => decoded s rows ell q (n+t) (forward s rows ell q rho visit t f)
      (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
      BinaryWalsh.kernelRun (directions s rho visit t ht)
        (fun x => decoded s rows ell q n f
          (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  induction t with
  | zero => simp [forward,CompactSpectatorLeafSemantics.forward,CompactSpectatorLeafLoop.run,directions,BinaryWalsh.kernelRun]
  | succ t ih =>
    have hi : t<arity^k := by omega
    have hprevguard := guard_mono (half s q) M t (t+1) (by omega) hguard
    have hd := axis_decoded s rows ell q (n+t) (M*4^t)
      (position s rho visit ⟨t,hi⟩) (position_lt s rho visit _)
      (forward s rows ell q rho visit t f)
      (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit t f hw)
      (forward_grid s rows ell q rho visit t n M (by omega) f hw hg hprevguard) hprevguard
    have hd' : decoded s rows ell q (n+(t+1)) (forward s rows ell q rho visit (t+1) f)=
        ButterflySpectatorSemantics.axis rows s.bits (position s rho visit ⟨t,hi⟩)
          (2^ell) (reservation s.bits q) (position_lt s rho visit _)
          (decoded s rows ell q (n+t) (forward s rows ell q rho visit t f)) := by
      simpa only [forward,CompactSpectatorLeafSemantics.forward,CompactSpectatorLeafLoop.run,dite_eq_left hi,
        position,CompactSpectatorLeafAxis.result,Nat.add_assoc] using hd
    rw [hd']
    have ha := congrFun (ButterflySpectatorSemantics.axis_row rows s.bits
      (position s rho visit ⟨t,hi⟩) (2^ell) (reservation s.bits q) (position_lt s rho visit _)
      (decoded s rows ell q (n+t) (forward s rows ell q rho visit t f)) row)
    funext x
    rw [ha (FlatCoordinateLayout.index x poly),ButterflyAxisWalsh.axis_walsh,
      ih (by omega) hprevguard,directions_succ,kernelRun_append]
    rfl

theorem inverse_walsh (t n M : ℕ) (ht : t≤arity^k) (f : Array s rows ell)
    (hw : Width s rows ell q f) (hg : Grid s rows ell q n M f)
    (hguard : 4*(M*4^t)<2^(half s q)) (row : Fin rows) (poly : Fin (2^ell)) :
    (fun x => decoded s rows ell q (n+t) (inverse s rows ell q rho visit t f)
      (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
      BinaryWalsh.kernelRun (BinaryWalsh.negateKernels (directions s rho visit t ht))
        (fun x => decoded s rows ell q n f
          (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  induction t with
  | zero => simp [inverse,CompactSpectatorLeafSemantics.inverse,CompactSpectatorInverseLeafLoop.run,
      directions,BinaryWalsh.negateKernels,BinaryWalsh.kernelRun]
  | succ t ih =>
    have hi : t<arity^k := by omega
    have hprevguard := guard_mono (half s q) M t (t+1) (by omega) hguard
    have hd := inverse_axis_decoded s rows ell q (n+t) (M*4^t)
      (position s rho visit ⟨t,hi⟩) (position_lt s rho visit _)
      (inverse s rows ell q rho visit t f)
      (CompactSpectatorInverseLeafLoop.width_run s rows ell (reservation s.bits q) rho visit t f hw)
      (inverse_grid s rows ell q rho visit t n M (by omega) f hw hg hprevguard) hprevguard
    have hd' : decoded s rows ell q (n+(t+1)) (inverse s rows ell q rho visit (t+1) f)=
        ButterflySpectatorSemantics.inverseAxis rows s.bits (position s rho visit ⟨t,hi⟩)
          (2^ell) (reservation s.bits q) (position_lt s rho visit _)
          (decoded s rows ell q (n+t) (inverse s rows ell q rho visit t f)) := by
      simpa only [inverse,CompactSpectatorLeafSemantics.inverse,CompactSpectatorInverseLeafLoop.run,dite_eq_left hi,
        position,CompactSpectatorInverseLeafAxis.result,Nat.add_assoc] using hd
    rw [hd']
    have ha := congrFun (ButterflySpectatorSemantics.inverse_row rows s.bits
      (position s rho visit ⟨t,hi⟩) (2^ell) (reservation s.bits q) (position_lt s rho visit _)
      (decoded s rows ell q (n+t) (inverse s rows ell q rho visit t f)) row)
    funext x
    rw [ha (FlatCoordinateLayout.index x poly),ButterflyInverseAxisSemantics.axis_walsh,
      ih (by omega) hprevguard,directions_succ]
    simp only [BinaryWalsh.negateKernels,List.map_append,List.map_cons,List.map_nil,kernelRun_append]
    rfl

def dependencyCoefficient (C : ℕ) := Nat.clog 2 (C+1)+2*volumeCoefficient

/-- Actual path growth and pending axis work fit the existing unchanged
signed fields once the real chunk width pays the fixed dependency constant. -/
theorem guard_from_path {left exponent levels frames returned : ℕ}
    (path : Path s.active left exponent levels frames returned) (p C t : ℕ)
    (hp : p≤q) (hchunk : dependencyCoefficient C≤s.chunk) (ht : t≤s.bits) :
    4*(CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^t)<2^(half s q) := by
  have hb := path.guard p C
  have hm := Nat.mul_le_mul_right s.active hchunk
  have hv : dependencyCoefficient C*s.active≤s.bits := by
    unfold Shape.bits
    nlinarith
  have hpos : 0<4^(t+1) := pow_pos (by decide) _
  have h := Nat.mul_lt_mul_of_pos_right hb hpos
  have hl : 4*(CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^t)=
      CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^(t+1) := by
    rw [pow_succ]
    ring
  have hr : 2^(p+dependencyCoefficient C*s.active+1)*4^(t+1)=
      2^(p+dependencyCoefficient C*s.active+1+2*(t+1)) := by
    rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_add]
  rw [←hl] at h
  change 4*(CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^t)<
    2^(p+dependencyCoefficient C*s.active+1)*4^(t+1) at h
  rw [hr] at h
  exact h.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (by
    unfold half ButterflyGuard.halfWidth
    omega))

open Filter in
/-- The actual multiplier's growing K eventually pays every fixed dependency
coefficient; no permanently supplied sufficiently-large-chunk hypothesis. -/
theorem eventually_chunk_capacity (C : ℕ) : ∀ᶠ inputSize : ℕ in atTop,
    dependencyCoefficient C≤Sizes.K inputSize := by
  have hx := ((tendsto_rpow_atTop (mul_pos Sizes.epsilon_pos Sizes.spacing_pos)).comp
    TimeBound.tendsto_precision).eventually_ge_atTop (24*(dependencyCoefficient C:ℝ))
  filter_upwards [hx,Sizes.eventually_K_ge] with inputSize hlarge hk
  change 24*(dependencyCoefficient C:ℝ)≤TimeBound.precision inputSize^(Parameters.epsilon*Parameters.spacing) at hlarge
  have h : (dependencyCoefficient C:ℝ)≤Sizes.K inputSize := by nlinarith
  exact_mod_cast h

/-- Corrected role metadata fixes the same literal field widths as the
leaf's private baseline, without asserting anything about the denominator. -/
theorem width_from_retained_role (metadataP : ℕ) (hP : 2*s.bits≤metadataP)
    (f : Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s metadataP ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s metadataP) :
    Width s rows ell (metadataP-2*s.bits) f := by
  intro i
  have h := hw i
  rw [CompactNativeRoleChildPrecision.stored_width s metadataP hP] at h
  have he : ButterflyAxisHeadersData.width s.bits (reservation s.bits (metadataP-2*s.bits))=
      ButterflyGuard.width (reservation s.bits (metadataP-2*s.bits)) s.bits := by
    unfold ButterflyAxisHeadersData.width ButterflyGuard.width ButterflyGuard.halfWidth
    omega
  rw [he] at h
  exact h

/-- The actual retained reservation's private baseline already dominates the
original numerator precision, independently of the actual inherited exponent. -/
theorem actual_baseline_ge (c m d D G K originalP : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    originalP≤CompactNativeRoleReservedBridge.precision c m d D K originalP-
      2*(CompactReservationNativeRows.shape c m d D G K).bits := by
  rw [(CompactNativeRoleChildPrecision.actual_precision c m d D G K originalP hK hD).2]
  omega

/-- Grid uniqueness bounds the actual stored signed numerators consumed by
both directions; the bound uses their true inherited denominator n. -/
theorem signed_guards_from_path {levels frames returned : ℕ}
    (path : Path s.active left k levels frames returned) (p C n : ℕ)
    (hp : p≤q) (hchunk : dependencyCoefficient C≤s.chunk)
    (f : Array s rows ell)
    (hg : Grid s rows ell q n (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (i : Fin (ButterflySpectatorGeometry.Size rows s.bits (2^ell))) :
    |ButterflySigned.signedValue (half s q) (f i).1|<(2^(half s q):ℕ) ∧
    |ButterflySigned.signedValue (half s q) (f i).2|<(2^(half s q):ℕ) := by
  have hb := ButterflyGuard.represented_bound _ _ n _ (hg i)
  have hguard := guard_from_path s q path p C 0 hp hchunk (by omega)
  simp only [pow_zero,Nat.mul_one] at hguard
  have hlt : CompactRecursiveGridBudget.bound p C levels (frames+2*returned)<2^(half s q) := by omega
  have hlt' : (CompactRecursiveGridBudget.bound p C levels (frames+2*returned):ℤ)<(2^(half s q):ℕ) := by
    exact_mod_cast hlt
  exact ⟨hb.1.trans_lt hlt',hb.2.trans_lt hlt'⟩

open Filter in
theorem eventually_actual_chunk_capacity (C : ℕ) : ∀ᶠ inputSize : ℕ in atTop,
    ∀ D payload : ℕ,dependencyCoefficient C≤(actualShape inputSize D payload).chunk := by
  filter_upwards [eventually_chunk_capacity C] with inputSize hk D payload
  exact hk

def kernelList (dir : CompactSpectatorLeafGuardOriginal.Direction) (t : ℕ) (ht : t≤arity^k) :=
  match dir with
  | .forward => directions s rho visit t ht
  | .inverse => BinaryWalsh.negateKernels (directions s rho visit t ht)

theorem directional_semantics (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (n M : ℕ) (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n M f) (hguard : 4*(M*4^(arity^k))<2^(half s q))
    (row : Fin rows) (poly : Fin (2^ell)) :
    let out := CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f
    Grid s rows ell q (n+arity^k) (M*4^(arity^k)) out ∧
      (fun x => decoded s rows ell q (n+arity^k) out
        (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
        BinaryWalsh.kernelRun (kernelList s rho visit dir (arity^k) (by omega))
          (fun x => decoded s rows ell q n f
            (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  cases dir
  · exact ⟨forward_grid s rows ell q rho visit _ n M (by omega) f hw hg hguard,
      forward_walsh s rows ell q rho visit _ n M (by omega) f hw hg hguard row poly⟩
  · exact ⟨inverse_grid s rows ell q rho visit _ n M (by omega) f hw hg hguard,
      inverse_walsh s rows ell q rho visit _ n M (by omega) f hw hg hguard row poly⟩

/-- The actual fixed directional machine's tape proof and inherited decoded
Walsh semantics share exactly the same input and unchanged record widths. -/
theorem physical_leaf_from_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    {levels frames returned : ℕ} (path : Path s.active left k levels frames returned)
    (p C n slots right source target : ℕ) (hp : p≤q)
    (hchunk : dependencyCoefficient C≤s.chunk)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : Array s rows ell) (hw : Width s rows ell q f)
    (hg : Grid s rows ell q n (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (row : Fin rows) (poly : Fin (2^ell)) :
    HoareTime (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
      (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none) (CompactSpectatorLeafAxis.word f)
        (CompactSpectatorLeafOriginal.values s rows ell q rho.val left (arity^k) slots right source target))
      (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none)
        (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f))
        (CompactSpectatorLeafOriginal.values s rows ell q rho.val left (arity^k) slots right source target))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho visit slots right source target) ∧
      (fun x => decoded s rows ell q (n+arity^k)
        (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)
        (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly)))=
        BinaryWalsh.kernelRun (kernelList s rho visit dir (arity^k) (by omega))
          (fun x => decoded s rows ell q n f
            (RecursiveInterchangeRows.pack row (FlatCoordinateLayout.index x poly))) := by
  have hguard := guard_from_path s q path p C (arity^k) hp hchunk
    (CompactSpectatorLeafSemantics.count_le_bits s rho visit)
  exact ⟨CompactSpectatorLeafGuardOriginal.phase_runs dir s rows ell q rho visit
      slots right source target hG hA hr f hw,
    (directional_semantics s rows ell q rho visit dir n _ f hw hg hguard row poly).2⟩

end
end IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
