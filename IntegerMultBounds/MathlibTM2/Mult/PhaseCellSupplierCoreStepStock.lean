module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStep
public import IntegerMultBounds.MathlibTM2.Host.ConsumeRuns

/-! Proper-core calls publish fewer symbols than their routed halo payloads;
consuming the origin queue as well only decreases iteration-boundary stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s B L : ℕ} [NeZero s] {U : Type}

namespace PackedNormalizedJob

theorem inputPayload_length (r : PackedNormalizedJob A s) :
    r.inputPayload.length = r.Fs.length*(r.b-r.a)*r.W := by
  have hfit : r.a+(r.b-r.a) ≤ s := by
    have ha := r.bounds.hab
    have hb := r.hright
    have he := r.hbEq
    omega
  simp [inputPayload,length_cstream,List.length_flatten,List.map_map,Function.comp_def,
    packedInterval_length _ hfit]

theorem coreOutput_length_le_payload (r : PackedNormalizedJob A s)
    (rows : Fin 1 → Fin B → List GaussianInt) (hreplicas : r.Fs.length = B)
    (hcore : coreLength s r.coreWidth r.k = L) (hlen : ∀ i j, (rows i j).length = L) :
    ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten).length ≤
      r.inputPayload.length := by
  have hgeometry : L ≤ r.b-r.a := by have h := r.haloLength; omega
  rw [inputPayload_length,hreplicas]
  simp only [List.length_flatten,List.map_ofFn,Function.comp_def,length_cstream,hlen,List.sum_ofFn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.one_mul]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right r.W (Nat.mul_le_mul_left B hgeometry)

end PackedNormalizedJob

namespace SupplierSetupPlan

theorem coreStep_boundary_size_le (r : PackedNormalizedJob A s)
    (origins source result : Fin T) (hreg : [origins,source,result].Nodup)
    (V : ℕ) (originTail tail : List (Fin (A+4)))
    (v w : HS T Q A U) (S : Stacks T A)
    (horigins : S.R origins = binSyms V r.a++originTail)
    (hsource : S.R source = r.inputPayload++tail)
    (rows : Fin 1 → Fin B → List GaussianInt) (hreplicas : r.Fs.length = B)
    (hcore : coreLength s r.coreWidth r.k = L) (hlen : ∀ i j, (rows i j).length = L) :
    mnSize (Host.mk w {S with R := (Function.update
      (Function.update (Function.update S.R origins originTail) source tail) result
      ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R result))}) ≤
      mnSize (Host.mk v S) := by
  have hr := hreg
  regs_ne hr
  let E : Stacks T A := {S with R := Function.update S.R origins originTail}
  have hretire := mn_consume_appendR_size_nonincreasing v v S origins result
    ‹origins ≠ result› (binSyms V r.a) originTail [] horigins (by simp)
  have hresult : E.R result = S.R result := by simp [E,Ne.symm ‹origins ≠ result›]
  have hretire' : mnSize (Host.mk v E) ≤ mnSize (Host.mk v S) := by
    change mnSize (Host.mk v {E with R := Function.update E.R result ([]++S.R result)}) ≤ _ at hretire
    simpa only [List.nil_append,←hresult,Function.update_eq_self] using hretire
  have hconsume := mn_consume_appendR_size_nonincreasing v w E source result
    ‹source ≠ result› r.inputPayload tail _ (by simpa [E,Ne.symm ‹origins ≠ source›] using hsource)
    (r.coreOutput_length_le_payload rows hreplicas hcore hlen)
  rw [hresult] at hconsume
  exact hconsume.trans hretire'

end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
