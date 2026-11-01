module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairRecoveryOutput

/-! Identify the actual constructor's scalar solution order by its RHS data.
Choice of solutions is shared by equal fields, independent of replica index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s p u l target rhsExp t a b V : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

namespace GeneratedRecoveryJob
noncomputable def solutionMap
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (F : ZMod s → GaussianInt) : ZMod s → ℝ := by
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
    positivity
  exact Classical.choose (solves_exists (realMatrix s t p u) (haloVertices s a b) _ hμ
    (dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) h.hdom)
    (fun i => (value (packedHaloPrecision p l s t u target rhsExp a b) (F i)).re))

/-- The shared field-indexed choice solves the original active system. -/
theorem solutionMap_solves
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (F : ZMod s → GaussianInt) :
    Solves (realMatrix s t p u) (haloVertices s a b) (solutionMap h F)
      (fun i => (value (packedHaloPrecision p l s t u target rhsExp a b) (F i)).re) := by
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := h.hp; omega)
    positivity
  exact Classical.choose_spec (solves_exists (realMatrix s t p u) (haloVertices s a b) _ hμ
    (dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) h.hdom)
    (fun i => (value (packedHaloPrecision p l s t u target rhsExp a b) (F i)).re))

theorem ofBounds_solution
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i, ‖value (packedHaloPrecision p l s t u target rhsExp a b) (F i)‖ ≤ (2 : ℝ)^rhsExp)
    (j : ℕ) : (ofBounds h Fs hF).solution j = solutionMap h (Fs.reverse.getD j (fun _ => 0)) := by
  rfl
end GeneratedRecoveryJob

private theorem reverse_indices_getD {X Y : Type} (xs : List X) (x : X) (f : X → Y) :
    (List.finRange xs.length).reverse.map (fun j => f (xs.reverse.getD j.val x)) = xs.map f := by
  have hget (ys : List X) (n : ℕ) (hlen : ys.length = n) :
      (List.finRange n).map (fun j => f (ys.getD j.val x)) = ys.map f := by
    subst n
    rw [← List.ofFn_eq_map]
    have heq : (List.ofFn fun j : Fin ys.length => f (ys.getD j.val x)) =
        List.ofFn (fun j : Fin ys.length => f ys[j.val]) := by
      congr 1
      funext j
      rw [List.getD_eq_getElem _ _ j.isLt]
    exact heq.trans (List.ofFn_getElem_eq_map ys f)
  have h : (List.finRange xs.length).map (fun j => f (xs.reverse.getD j.val x)) = xs.reverse.map f := by
    exact hget xs.reverse xs.length (by simp)
  rw [List.map_reverse,h,← List.map_reverse,List.reverse_reverse]

/-- Reverse-indexed scalar recovery targets are exactly the real/imaginary
component targets in the original complex replica order. -/
theorem RawRecoveryJob.ofComplexBounds_solutionOrder
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u target rhsExp a b+8 ≤ W) :
    let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W hW
    let q := packedHaloPrecision p l s t u target rhsExp a b
    let y := fun F : ZMod s → GaussianInt =>
      GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
    (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) =
      complexComponentTargets (Fs.map (componentSolution y)) := by
  let q := packedHaloPrecision p l s t u target rhsExp a b
  let y := fun F : ZMod s → GaussianInt =>
    GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
  change (List.finRange (recoveryInputFields p q (complexComponentFields Fs)).length).reverse.map
    (fun j => GeneratedRecoveryJob.solutionMap bounds
      ((recoveryInputFields p q (complexComponentFields Fs)).reverse.getD j.val (fun _ => 0))) =
    complexComponentTargets (Fs.map (componentSolution y))
  rw [reverse_indices_getD]
  simpa only [recoveryInputFields,List.map_map,Function.comp_def,y] using
    (componentSolution_targets Fs y).symm

/-- Actual complex jobs feed pairing without a target-order or scalar-accuracy
premise. The target is the component solution map determined by the input fields. -/
theorem RawRecoveryJob.ofComplexBounds_pair_output_exec
    {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (bounds : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (W : ℕ) (hW : 2*packedHaloPrecision p l s t u target rhsExp a b+8 ≤ W) :
    let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W hW
    let q := packedHaloPrecision p l s t u target rhsExp a b
    let y := fun F : ZMod s → GaussianInt =>
      GeneratedRecoveryJob.solutionMap bounds (fun i => (2 : GaussianInt)^(q-p-1)*F i)
    let Zs := Fs.map (componentSolution y)
    ∀
    {replicas width count src buf saved tmp : Fin T}
    (_ : [replicas,width,count,src,buf,saved,tmp].Nodup) (_ : 4 ≤ A)
    {word : List (Fin (A+4))} (_ : r.output word)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (_ : (S.R replicas).length = Zs.length)
    (_ : (S.R width).length = r.problem.span*r.problem.wordWidth)
    (_ : S.R src = word++tail)
    (_ : S.R count = []) (_ : S.R buf = []) (_ : S.R saved = []) (_ : S.R tmp = []),
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Zs.length ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ Zs.length*(16*(r.problem.span*r.problem.wordWidth)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A r.problem.wordWidth
            (packedInterval r.problem.origin r.problem.span D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
        (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
          (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++tail))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs Gs := by
  dsimp only
  intro replicas width count src buf saved tmp hreg hA word houtput tail v S
    hreplicas hwidth hsrc hcount hbuf hsaved htmp
  exact (RawRecoveryJob.ofComplexBounds bounds Fs hF W hW).pair_output_exec hreg hA houtput
    _ (RawRecoveryJob.ofComplexBounds_solutionOrder bounds Fs hF W hW)
    tail v S hreplicas hwidth hsrc hcount hbuf hsaved htmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
