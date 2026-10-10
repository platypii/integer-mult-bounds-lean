import IntegerMultBounds.Machine.CompactSpectatorInheritedGrid
import IntegerMultBounds.Machine.NativeSignedGapReturn

/-! Genuine return-gap width bounds from the actual complex25 scalar rows and
real dependency paths. The scalar numerator certificate itself pays every row's
denominator bit. These are arithmetic/controller metadata connection lemmas;
physical propagation of the stated precision budget is not asserted here. -/
namespace IntegerMultBounds.Machine.CompactNativeReturnGapBudget
noncomputable section
open Networks Networks.GaussianPrecision
open CompactComplexRecursiveGeometry CompactRecursiveDependencyBudget
open CompactGadgetReservationShape (Shape)
attribute [local irreducible] ComplexRank25.program GlobalGrouped.program
  GlobalGrouped.stage GlobalGrouped.partialStage GlobalGrouped.invocationGroups
  GlobalGrouped.localGroups ComplexFramedExecution.rows

theorem scalarBound_denominator {ι : Type*} (d B : ℕ)
    (gs : List (Circuit.Gate ι ℂ)) (M : ℕ) :
    M*2^(gs.length*d)≤scalarBound d B gs M := by
  induction gs generalizing M with
  | nil => simp [scalarBound]
  | cons g gs ih =>
    have hh := ih (M*2^d+g.terms.length*(2*B*M))
    have hm := Nat.mul_le_mul_right (2^(gs.length*d))
      (Nat.le_add_right (M*2^d) (g.terms.length*(2*B*M)))
    calc
      _ = (M*2^d)*2^(gs.length*d) := by
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul,pow_add]; ring
      _ ≤ (M*2^d+g.terms.length*(2*B*M))*2^(gs.length*d) := hm
      _ ≤ _ := hh

private theorem scalarBound_rows {ι : Type*} (gs : Circuit.Program ι ℚ) :
    2^gs.length ≤ scalarBound 1 52 (RationalScalarGrid.castRows gs) 1 := by
  have hh := scalarBound_denominator 1 52 (RationalScalarGrid.castRows gs) 1
  simpa only [Nat.one_mul, Nat.mul_one, RationalScalarGrid.castRows, List.length_map] using hh

private theorem log_budget (rows growth C : ℕ) (hp : 2^rows≤growth) (hC : growth≤C) :
    rows≤Nat.clog 2 (C+1) := by
  exact Nat.le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr
    (hp.trans hC |>.trans_lt (Nat.lt_succ_self C)))

/-- No gigantic program is normalized: the scalar certificate gives one factor
of two per literal row, including unused-role denominator raising. -/
theorem actual_rows_clog (C : ℕ) (hC : CompactFramedScalarGrid.growthConstant≤C) :
    ComplexFramedExecution.rows.length≤Nat.clog 2 (C+1) := by
  have hp : 2^ComplexFramedExecution.rows.length≤CompactFramedScalarGrid.growthConstant := by
    unfold CompactFramedScalarGrid.growthConstant
    exact scalarBound_rows ComplexFramedExecution.rows
  exact log_budget ComplexFramedExecution.rows.length CompactFramedScalarGrid.growthConstant C hp hC

/-- The actual inherited path contributions, current literal scalar prefix,
and pending native axes. No unconstrained denominator variable is substituted. -/
def precision (p levels frames returned g axes : ℕ) :=
  p+levels*ComplexFramedExecution.rows.length+frames+2*returned+
    (CompactFramedScalarGrid.rows g).length+axes

def gap (p levels frames returned g axes target : ℕ) :=
  precision p levels frames returned g axes-target

private theorem numeric_budget (p C q active chunk bits levels frames returned prefixRows rows axes : ℕ)
    (hrows : rows≤Nat.clog 2 (C+1)) (hprefix : prefixRows≤rows)
    (hlevels : levels+1≤active) (hvolume : frames+2*returned≤volumeCoefficient*active)
    (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤chunk)
    (hbits : active*chunk≤bits) :
    p+levels*rows+frames+2*returned+prefixRows+axes≤q+bits+axes := by
  have hscalar : levels*rows+prefixRows≤rows*active := by
    calc
      _ ≤ levels*rows+rows := Nat.add_le_add_left hprefix _
      _ = (levels+1)*rows := by ring
      _ ≤ active*rows := Nat.mul_le_mul_right _ hlevels
      _ = _ := Nat.mul_comm _ _
  have hco : rows+volumeCoefficient≤chunk := by
    unfold CompactSpectatorInheritedGrid.dependencyCoefficient at hchunk
    omega
  have hmul := Nat.mul_le_mul_right active hco
  have hcap : (rows+volumeCoefficient)*active≤bits := by
    rw [Nat.mul_comm chunk active] at hmul
    omega
  have hcombine : levels*rows+frames+2*returned+prefixRows≤(rows+volumeCoefficient)*active := by
    rw [Nat.add_mul]
    omega
  omega

/-- One extra current g fits in the genuine path level potential. The
existing eventual chunk reservation pays its denominator rows automatically. -/
theorem precision_le {left k levels frames returned : ℕ} (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk) :
    precision p levels frames returned g axes≤q+s.bits+axes := by
  have hlevels : levels+1≤s.active := by
    have hh := path.levels_le
    have hw : 1≤arity^k := Nat.one_le_pow _ _ (by decide)
    omega
  exact numeric_budget p C q s.active s.chunk s.bits levels frames returned
    (CompactFramedScalarGrid.rows g).length ComplexFramedExecution.rows.length axes
    (actual_rows_clog C hC) (prefix_rows_le g) hlevels path.volume_bound hp hchunk
    (by unfold Shape.bits; omega)

/-- Real pending forward/inverse axes and frame work are at most twice the
retained global binary width; the actual exponent therefore fits the same
unchanged signed field as the already-proved inherited numerator guard. -/
theorem precision_le_half {left k levels frames returned : ℕ} (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) :
    precision p levels frames returned g axes≤CompactSpectatorInheritedGrid.half s q := by
  have hh := precision_le s path p C q g axes hC hp hchunk
  unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth
  omega

/-- The executable gap inequality follows from the path and actual scalar
certificate, rather than being supplied as a caller cost allowance. -/
theorem gap_le_field {left k levels frames returned : ℕ} (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes target : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) :
    gap p levels frames returned g axes target≤CompactSpectatorInheritedGrid.half s q+1 := by
  have hh := precision_le_half s path p C q g axes hC hp hchunk haxes
  unfold gap
  omega

/-- Corrected retained metadata fixes the literal signed field capacity. -/
theorem retained_gap_le_width {left k levels frames returned : ℕ} (s : Shape)
    (path : Path s.active left k levels frames returned) (p C metadataP g axes target : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤metadataP-2*s.bits)
    (hP : 2*s.bits≤metadataP)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) :
    gap p levels frames returned g axes target≤CompactNativeRoleHeaders.recordWidth s metadataP := by
  have hh := gap_le_field s path p C (metadataP-2*s.bits) g axes target hC hp hchunk haxes
  unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width
    CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at *
  omega

/-- Actual original reservation descriptors supply the baseline inequality;
no independently supplied baseline or width allowance is needed. -/
theorem actual_gap_le_width (c m d D G K p C g axes target : ℕ)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape c m d D G K).active
      left k levels frames returned) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤
      (CompactReservationNativeRows.shape c m d D G K).chunk)
    (haxes : axes≤2*(CompactReservationNativeRows.shape c m d D G K).bits) :
    gap p levels frames returned g axes target≤CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape c m d D G K)
      (CompactNativeRoleReservedBridge.precision c m d D K p) :=
  retained_gap_le_width _ path _ _ _ _ _ _ hC
    (CompactSpectatorInheritedGrid.actual_baseline_ge c m d D G K p hK hD)
    (CompactNativeRoleChildPrecision.actual_precision c m d D G K p hK hD).1 hchunk haxes

open CompactSpectatorVisitGeometry (Array)
open NativeSignedReturnPrecision (fields)

/-- The inherited-width array gives actual real and imaginary field lengths. -/
theorem array_width (s : Shape) (rows ell q : ℕ) (f : Array s rows ell)
    (hw : CompactSpectatorInheritedGrid.Width s rows ell q f) :
    ∀ c∈List.ofFn f,c.1.length=CompactSpectatorInheritedGrid.half s q+1 ∧
      c.2.length=CompactSpectatorInheritedGrid.half s q+1 := by
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw i

/-- The execution consumes exactly the original row-major native coefficient
word, with polynomial spectators; it does not require a newly chosen encoding. -/
theorem array_serialization (s : Shape) (rows ell : ℕ) (f : Array s rows ell) :
    NativeSignedGapReturn.word (fields (List.ofFn f))=CompactSpectatorLeafAxis.word f := by
  unfold NativeSignedGapReturn.word CompactSpectatorLeafAxis.word ButterflyStreamData.full
  rw [NativeSignedReturnPrecision.native_serialization]
  simp only [List.flatMap, List.map_ofFn, ButterflyStreamData.encoded]
  rfl

/-- Actual dependency and denominator budgets discharge the native executable's
width precondition. Its return uses one scan and linear original volume time.
The runtime gap and length headers are explicit: synthesizing them in the
recursive controller and propagating Path are still separate obligations. -/
theorem array_runs {left k levels frames returned : ℕ} (s : Shape)
    (path : Path s.active left k levels frames returned) (p C q g axes target rows ell : ℕ)
    (hC : CompactFramedScalarGrid.growthConstant≤C) (hp : p≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤s.chunk)
    (haxes : axes≤2*s.bits) (f : Array s rows ell)
    (hw : CompactSpectatorInheritedGrid.Width s rows ell q f) (hrows : 0<rows)
    (bs ls : List Bool) (hgap : Counter.value bs=gap p levels frames returned g axes target)
    (hlen : Counter.value ls=NativeSignedReturnStream.volume (fields (List.ofFn f)))
    (hb : GrowingCounterData.Canonical bs) (hl : GrowingCounterData.Canonical ls) :
    HoareTime NativeSignedGapReturn.program
      (fun v => v=CountedLoopHeaderClean.bank (NativeSignedGapReturn.input (fields (List.ofFn f)) bs ls))
      (fun v => v=CountedLoopHeaderClean.bank (NativeSignedGapReturn.output (fields (List.ofFn f))
        (gap p levels frames returned g axes target) bs ls))
      (129*NativeSignedReturnStream.volume (fields (List.ofFn f))+324) := by
  have hfield := array_width s rows ell q f hw
  have hd := gap_le_field s path p C q g axes target hC hp hchunk haxes
  have hfg : ∀ w∈fields (List.ofFn f),gap p levels frames returned g axes target≤w.length := by
    intro w h
    obtain ⟨c,hc,hmem⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl|rfl
    · rw [(hfield c hc).1]; exact hd
    · rw [(hfield c hc).2]; exact hd
  have hn : fields (List.ofFn f)≠[] := by
    have hs : 0<ButterflySpectatorGeometry.Size rows s.bits (2^ell) :=
      Nat.mul_pos hrows (Nat.mul_pos (by positivity) (by positivity))
    have hc : f ⟨0,hs⟩∈List.ofFn f := List.mem_ofFn.mpr ⟨⟨0,hs⟩,rfl⟩
    have hm : (f ⟨0,hs⟩).1∈fields (List.ofFn f) := List.mem_flatMap.mpr ⟨_,hc,by simp⟩
    intro he
    rw [he] at hm
    exact List.not_mem_nil hm
  exact NativeSignedGapReturn.runs_linear _ _ hfg hn bs ls hgap hlen hb hl

/-- Coarser-grid divisibility, rather than the width bound, justifies precision
return. Every actual stored coefficient retains its width and exact value. -/
theorem array_exact (s : Shape) (p q levels frames returned g axes target rows ell M : ℕ)
    (htarget : target≤precision p levels frames returned g axes)
    (f : Array s rows ell) (hw : CompactSpectatorInheritedGrid.Width s rows ell q f)
    (hg : ∀ i,BoundedGrid target M (CompactSpectatorInheritedGrid.decoded s rows ell q
      (precision p levels frames returned g axes) f i)) :
    ∀ i, ((RadixSignedShiftRight.shifted^[gap p levels frames returned g axes target]) (f i).1).length=
      CompactSpectatorInheritedGrid.half s q+1 ∧
      ((RadixSignedShiftRight.shifted^[gap p levels frames returned g axes target]) (f i).2).length=
      CompactSpectatorInheritedGrid.half s q+1 ∧
      NativeSignedReturnPrecision.decoded (CompactSpectatorInheritedGrid.half s q) target
        ((RadixSignedShiftRight.shifted^[gap p levels frames returned g axes target]) (f i).1,
          (RadixSignedShiftRight.shifted^[gap p levels frames returned g axes target]) (f i).2)=
      CompactSpectatorInheritedGrid.decoded s rows ell q (precision p levels frames returned g axes) f i := by
  have he : target+gap p levels frames returned g axes target=precision p levels frames returned g axes :=
    Nat.add_sub_of_le htarget
  have hfield := array_width s rows ell q f hw
  have hgrid : ∀ c∈List.ofFn f,BoundedGrid target M
      (NativeSignedReturnPrecision.decoded (CompactSpectatorInheritedGrid.half s q)
        (target+gap p levels frames returned g axes target) c) := by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    rw [he]
    exact hg i
  have hh := NativeSignedReturnPrecision.coefficient_exact (List.ofFn f)
    (CompactSpectatorInheritedGrid.half s q) target
    (gap p levels frames returned g axes target) M hfield hgrid
  intro i
  rw [←he]
  exact hh (f i) (List.mem_ofFn.mpr ⟨i,rfl⟩)

/-- Original reservation metadata discharges the fixed return machine's actual
field-length precondition, including every polynomial spectator. -/
theorem actual_array_capacity (c m d D G K p C g axes target rows ell : ℕ)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape c m d D G K).active
      left k levels frames returned) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤
      (CompactReservationNativeRows.shape c m d D G K).chunk)
    (haxes : axes≤2*(CompactReservationNativeRows.shape c m d D G K).bits)
    (f : Array (CompactReservationNativeRows.shape c m d D G K) rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth
        (CompactReservationNativeRows.shape c m d D G K)
        (CompactNativeRoleReservedBridge.precision c m d D K p) ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth
        (CompactReservationNativeRows.shape c m d D G K)
        (CompactNativeRoleReservedBridge.precision c m d D K p)) :
    ∀ w∈fields (List.ofFn f),gap p levels frames returned g axes target≤w.length := by
  have hd := actual_gap_le_width c m d D G K p C g axes target path hK hD hC hchunk haxes
  intro w h
  obtain ⟨z,hz,hmem⟩ := List.mem_flatMap.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl|rfl
  · rw [(hw i).1]; exact hd
  · rw [(hw i).2]; exact hd

end
end IntegerMultBounds.Machine.CompactNativeReturnGapBudget
