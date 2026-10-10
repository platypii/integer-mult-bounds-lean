import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrent
import IntegerMultBounds.Machine.CompactNativeRoleOriginalBudget
import IntegerMultBounds.Machine.CompactRecursiveDependencyBudget

/-! The actual unchanged-row node merger has a uniform native-volume bound.
The true dependency Path derives legal grouping from the one original row pad;
the complete generated-header/merge/cleanup runtime is paid by OriginalBudget. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexNonleafRoleMergeCurrent
variable {s c : ℕ}

def constant (c : ℕ) := CompactNativeRoleOriginalBudget.constant c

theorem cost_linear (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    cost c sh rows ell p rho left count slots right src dst ≤
      constant c*volume rows sh ell p := by
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have h := CompactNativeRoleOriginalBudget.cost_linear true (rows/c) c sh ell p rho left
    count slots right src dst hc hn hA hG hK
  rw [Nat.div_mul_cancel hd] at h
  exact h

/-- Actual dependency descent cannot exceed the original padded recursion
depth. Both the remaining node exponent and every enclosing level are counted. -/
theorem path_depth {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) (d : ℕ) (hactive : active≤d) :
    levels+k≤CompactGlobalRowPadding.depth arity d := by
  induction path with
  | root i =>
    have hfit := CompactComplexRecursiveGeometry.piece_fits active i
    have hpow : arity^(CompactComplexRecursiveGeometry.pieceExponent active i)≤
        arity^(CompactGlobalRowPadding.depth arity d) := by
      exact (show arity^(CompactComplexRecursiveGeometry.pieceExponent active i)≤d by omega).trans
        (Nat.le_pow_clog (by decide) d)
    simpa only [Nat.zero_add] using
      (Nat.pow_le_pow_iff_right (by decide : 1<arity)).mp hpow
  | @child left k levels frames returned prior call ih => omega

/-- A genuine nonleaf Path leaves one row-divisor factor available at its own
current node, including a root node with zero enclosing levels. -/
theorem path_rows {active left k levels frames returned : ℕ}
    (path : Path active left k levels frames returned) (c d K : ℕ)
    (hc : 0<c) (hK : 0<K) (hactive : active≤d) (hk : 0<k) :
    0<CompactGlobalRowPadding.rowsAt c arity d K levels ∧
      c ∣ CompactGlobalRowPadding.rowsAt c arity d K levels := by
  have hdepth := path_depth path d hactive
  exact ⟨CompactGlobalRowPadding.rowsAt_positive c arity d K levels hc hK (by omega),
    CompactGlobalRowPadding.split_divides c arity d K levels hc hK (by omega)⟩

/-- The uniform runtime bound belongs to the literal same-row machine and
returns the permanent bank with every appended private tape blank at head zero. -/
theorem runs_linear (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh rows c ell hd f j))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=(bank sh rows ell p rho left count slots right src dst f v).append
        (SharedBank.empty 7 2))
      (constant c*volume rows sh ell p) := by
  have h := actual_runs sh rows ell p rho left count slots right src dst
    hc hr hd hG hA hK f hw v hh hs hroles
  rw [output_eq_append] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear sh rows ell p rho left count slots right src dst hc hr hd hA hG hK)

/-- All grouping and positivity obligations in the paid actual execution are
discharged by the genuine current-node dependency Path and original geometry. -/
theorem runs_from_path (sh : Shape) {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (d K ell p rho count slots right src dst : ℕ)
    (hc : 0<c) (hK : 0<K) (hactive : sh.active≤d) (hk : 0<k)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh
      (CompactGlobalRowPadding.rowsAt c arity d K levels) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hh : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank (CompactSpectatorLeafSetup.raw sh
        (CompactGlobalRowPadding.rowsAt c arity d K levels) ell p rho left count slots right src dst))
    (hs : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      v.tape CompactComplexNonleafRoleEntry.source=fun _ => blank)
    (hroles : ∀ j : Fin c,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      v.tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh
            (CompactGlobalRowPadding.rowsAt c arity d K levels) c ell
            (path_rows path c d K hc hK hactive hk).2 f j))) :
    HoareTime (program s c) (fun z => z=v.append (SharedBank.empty 7 2))
      (fun z => z=(bank sh (CompactGlobalRowPadding.rowsAt c arity d K levels)
        ell p rho left count slots right src dst f v).append (SharedBank.empty 7 2))
      (constant c*volume (CompactGlobalRowPadding.rowsAt c arity d K levels) sh ell p) :=
  runs_linear sh _ ell p rho left count slots right src dst hc
    (path_rows path c d K hc hK hactive hk).1
    (path_rows path c d K hc hK hactive hk).2 hG hA hchunk f hw v hh hs hroles

/-- The one original row pad also pays the merger in original native volume. -/
theorem cost_original (sh : Shape) {left k levels frames returned : ℕ}
    (path : Path sh.active left k levels frames returned)
    (d K ell p rho count slots right src dst : ℕ)
    (hc : 0<c) (hK : 0<K) (hactive : sh.active≤d) (hk : 0<k)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk) :
    cost c sh (CompactGlobalRowPadding.rowsAt c arity d K levels)
        ell p rho left count slots right src dst ≤
      (2*constant c)*volume (CompactGlobalRowPadding.originalRows c arity d K) sh ell p := by
  have h := cost_linear sh (CompactGlobalRowPadding.rowsAt c arity d K levels)
    ell p rho left count slots right src dst hc
    (path_rows path c d K hc hK hactive hk).1
    (path_rows path c d K hc hK hactive hk).2 hA hG hchunk
  have hv := Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell p)
    (CompactGlobalRowPadding.rowsAt_le_twice_original c arity d K levels hc hK)
  have hm := Nat.mul_le_mul_left (constant c) hv
  unfold volume at h ⊢
  exact h.trans (by simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hm)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrentBudget
