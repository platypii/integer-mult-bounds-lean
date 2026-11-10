module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
public import IntegerMultBounds.MathlibTM2.Routing.RetainedFieldRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedRecoveryPayload
public import IntegerMultBounds.NLogN.PhaseCellTargetCoreSelectionGeometry

/-! A retained target field is the ordinary cyclic line consumed by C-selection.
Spectator coordinates remain fixed through the numerical input handoff. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Routing
  RetainedHaloTensor RectangularHaloCoordinates
variable {ι : Type} [DecidableEq ι]

def retainedTensorLine (axis : ι → Axis) (retained : Finset ι)
    (f : (ι → ℕ) → GaussianInt) (coords : ι → ℕ × ℕ) (i : ι) :
    ZMod ((axis i).N*(axis i).L) → GaussianInt :=
  fun j => f (Function.update (project axis retained coords) i j.val)

theorem project_update_retained (axis : ι → Axis) (retained : Finset ι)
    (coords : ι → ℕ × ℕ) (i : ι) (hi : i ∈ retained) (k j : ℕ) :
    project axis retained (Function.update coords i (k,j)) =
      Function.update (project axis retained coords) i
        (sourceIndex (axis i).N (axis i).L (axis i).H k j) := by
  funext x
  by_cases hx : x = i
  · subst x; simp [project,hi]
  · simp [project,hx]

/-- The actual local field retains its original periodic ambient coordinates. -/
theorem retainedTensorLine_window (axis : ι → Axis) (retained : Finset ι)
    (f : (ι → ℕ) → GaussianInt) (coords : ι → ℕ × ℕ) (i : ι)
    (hi : i ∈ retained) (k : ℕ) (hH : (axis i).H ≤ (axis i).N*(axis i).L) :
    (List.range ((axis i).L+2*(axis i).H)).map
      (fun j => pullback axis retained f (Function.update coords i (k,j))) =
    cyclicInterval ((axis i).N*(axis i).L+k*(axis i).L-(axis i).H)
      ((axis i).L+2*(axis i).H) (retainedTensorLine axis retained f coords i) := by
  let : NeZero ((axis i).N*(axis i).L) := ⟨Nat.ne_of_gt (Nat.mul_pos (axis i).N_pos (axis i).L_pos)⟩
  rw [cyclicInterval_halo _ _ _ _ _ hH]
  apply List.map_congr_left
  intro j _
  rw [pullback,project_update_retained axis retained coords i hi]
  have hindex : sourceIndex (axis i).N (axis i).L (axis i).H k j < (axis i).N*(axis i).L :=
    Nat.mod_lt _ (Nat.mul_pos (axis i).N_pos (axis i).L_pos)
  simp only [retainedTensorLine,ZMod.val_natCast,Nat.mod_eq_of_lt hindex]

/-- The physical field permutation's endpoint is a batch of ordinary cyclic
target windows, in the actual spectator enumeration order. -/
theorem retainedFieldArchive_cyclic (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (fields : List (Sum ι ι)) (i : ι) (hi : i ∈ retained)
    (f : (ι → ℕ) → GaussianInt) (hH : (axis i).H ≤ (axis i).N*(axis i).L) :
    RetainedFieldRun.archive A w axis retained fields i f =
      (CoordinateEnumeration.enumerate (RetainedTensorEnumeration.width axis retained) fields
        (fun _ => 0)).flatMap fun coords =>
        cstream A w (cyclicInterval ((axis i).N*(axis i).L+coords (.inl i)*(axis i).L-(axis i).H)
          ((axis i).L+2*(axis i).H) (retainedTensorLine axis retained f
            (RetainedTensorEnumeration.unpack coords) i)) := by
  unfold RetainedFieldRun.archive
  apply List.flatMap_congr
  intro coords _
  congr 1
  simpa only [localLength,ite_eq_left hi] using
    retainedTensorLine_window axis retained f (RetainedTensorEnumeration.unpack coords) i hi
      (coords (.inl i)) hH

theorem retainedTensorLine_window_nonwrap (axis : ι → Axis) (retained : Finset ι)
    (f : (ι → ℕ) → GaussianInt) (coords : ι → ℕ × ℕ) (i : ι)
    (hi : i ∈ retained) (k : ℕ) (hH : (axis i).H ≤ (axis i).N*(axis i).L)
    (hguard : (axis i).H ≤ k*(axis i).L) :
    (List.range ((axis i).L+2*(axis i).H)).map
      (fun j => pullback axis retained f (Function.update coords i (k,j))) =
    cyclicInterval (k*(axis i).L-(axis i).H) ((axis i).L+2*(axis i).H)
      (retainedTensorLine axis retained f coords i) := by
  rw [retainedTensorLine_window axis retained f coords i hi k hH]
  unfold cyclicInterval
  apply List.map_congr_left
  intro j _
  congr 1
  rw [show (axis i).N*(axis i).L+k*(axis i).L-(axis i).H+j =
    (axis i).N*(axis i).L+(k*(axis i).L-(axis i).H+j) by omega,
    Nat.cast_add,ZMod.natCast_self,zero_add]

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node PhaseCellRationalArgs PhaseCellTargetCoreOwnership

/-- Restoring C-selection directly from a retained tensor field. The output
uses the original source-row selector, with no reconstructed full target line. -/
theorem retainedTensorRowSelection_exec {T Q A s : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P T Q A U}
    (axis : ι → Axis) (retained : Finset ι) (f : (ι → ℕ) → GaussianInt)
    (coords : ι → ℕ × ℕ) (i : ι) (hi : i ∈ retained) (k : ℕ)
    (hH : (axis i).H ≤ (axis i).N*(axis i).L)
    (hguard : (axis i).H ≤ k*(axis i).L)
    (dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T)
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (w radius : ℕ)
    (hst : s ≤ (axis i).N*(axis i).L) (hnear : (axis i).N*(axis i).L ≤ 2*s)
    (hL : 2 ≤ (axis i).L)
    (ha : radius ≤ cut s ((axis i).N*(axis i).L) (axis i).L k)
    (hb : cut s ((axis i).N*(axis i).L) (axis i).L (k+1)+radius ≤ s)
    (hpadding : 2*radius+3 ≤ (axis i).H) :
    let t := (axis i).N*(axis i).L
    let origin := k*(axis i).L-(axis i).H
    let span := (axis i).L+2*(axis i).H
    let a := cut s t (axis i).L k-radius
    let n := rows s t (axis i).L k+2*radius
    let F := retainedTensorLine axis retained f coords i
    ∀ (v : HS T Q A U) (S : Stacks T A),
    S.R control = (match localRowOrigins s t a n origin w with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps)) →
    S.R src = cstream A w ((List.range span).map
      (fun j => pullback axis retained f (Function.update coords i (k,j)))) →
    (S.R rowCount).length = 1 → (S.R wordR).length = w →
    (∀ j ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R j = []) →
    ∃ v' m, v'.user = v.user ∧ m ≤ n*(14*w+25)+12*(span*w)+6*w+38 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w (packedInterval a n (fun j => F (rowIndex s t j)))++S.R dst))}) := by
  dsimp only
  intro v S hc hs hrow hw hclean
  have ht := Nat.mul_pos (axis i).N_pos (axis i).L_pos
  have hrows := rows_pos s ((axis i).N*(axis i).L) (axis i).L k ht hnear hL
  have hn : 0 < rows s ((axis i).N*(axis i).L) (axis i).L k+2*radius := by omega
  have hwindow := owned_halo_contained s ((axis i).N*(axis i).L) (axis i).L k radius
    (axis i).H (NeZero.pos s) hst ht hnear hrows ha hguard hpadding
  rw [retainedTensorLine_window_nonwrap axis retained f coords i hi k hH hguard] at hs
  obtain ⟨v',m,hu,hm,he⟩ := cyclicRowSelection_exec dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR hreg w _ _ _ _ _ hn hwindow v S hc hs hrow hw hclean
  have hfit : cut s ((axis i).N*(axis i).L) (axis i).L k-radius+
      (rows s ((axis i).N*(axis i).L) (axis i).L k+2*radius) ≤ s := by
    have hmono := cut_mono s ((axis i).N*(axis i).L) (axis i).L (show k ≤ k+1 by omega)
    unfold rows
    omega
  refine ⟨v',m,hu,hm,?_⟩
  simpa only [cyclicInterval_eq_packed _ hfit] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
