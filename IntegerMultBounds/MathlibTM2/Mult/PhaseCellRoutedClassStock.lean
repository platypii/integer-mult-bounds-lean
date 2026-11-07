module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock

/-! Cropping a routed halo cannot increase a class's boundary stock. This is
the nonaccumulation premise of the existing counted outer-loop theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} [NeZero s] {U : Type}
open ComputedRecoveryPlan (routedPayload)

theorem PackedNormalizedJob.outputs_length_le_routedPayload
    {jobs : List (PackedNormalizedJob A s)} {outputs : List (List (Fin (A+4)))}
    (h : List.Forall₂ PackedNormalizedJob.output jobs outputs) :
    outputs.reverse.flatten.length ≤ (jobs.flatMap routedPayload).length := by
  have hvolume (r : PackedNormalizedJob A s) : r.outputVolume ≤ (routedPayload r).length := by
    change r.outputVolume ≤ r.inputPayload.length
    rw [r.inputPayload_length]
    have hgeometry : coreLength s r.coreWidth r.k ≤ r.b-r.a := by have hh := r.haloLength; omega
    exact Nat.mul_le_mul_right r.W (Nat.mul_le_mul_left r.Fs.length hgeometry)
  have hnormal : outputs.flatten.length ≤ (jobs.flatMap routedPayload).length := by
    induction h with
    | nil => simp
    | @cons r word jobs words hr h ih =>
      simp only [List.flatten_cons,List.length_append,List.flatMap_cons]
      exact Nat.add_le_add (by rw [r.output_length hr]; exact hvolume r) ih
  simpa only [List.length_flatten,List.map_reverse,List.sum_reverse] using hnormal

namespace ComputedClassBanks

theorem routedClass_boundary_size_le (bank : ComputedClassBank → Fin T)
    (hinj : Function.Injective bank) (jobs : List (PackedNormalizedJob A s))
    (outputs : List (List (Fin (A+4)))) (houtputs : List.Forall₂ PackedNormalizedJob.output jobs outputs)
    (src : Fin T) (borrowed : List (Fin (A+4))) (v w : HS T Q A U) (S : Stacks T A)
    (hsource : S.R src = jobs.flatMap routedPayload++borrowed) (hsrcBank : ∀ k, src ≠ bank k) :
    mnSize (mk w {S with R := (Function.update (Function.update S.R src borrowed)
      (plan bank hinj).result (outputs.reverse.flatten++S.R (plan bank hinj).result))}) ≤ mnSize (mk v S) := by
  have hne : control bank .source ≠ (plan bank hinj).result := by
    simp [control,plan,RecoveryBanks.plan,recovery,hinj.eq_iff]
  have hsrcSource : control bank .source ≠ src := (hsrcBank (.control .source)).symm
  have hsrcResult : src ≠ (plan bank hinj).result := by
    simpa only [plan,RecoveryBanks.plan,recovery] using hsrcBank (.recovery (.control .result))
  have hreg : [control bank .source,src,(plan bank hinj).result].Nodup := by
    simp [hne,hsrcSource,hsrcResult]
  have hh := mn_consume_pair_appendR_size_nonincreasing v w S (control bank .source) src
    (plan bank hinj).result hreg [] (S.R (control bank .source)) (jobs.flatMap routedPayload) borrowed
    outputs.reverse.flatten rfl hsource (PackedNormalizedJob.outputs_length_le_routedPayload houtputs)
  simpa only [List.nil_append,Function.update_eq_self] using hh

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
