module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierBatchCount

/-! Once per movement class, generate the ordered origins, restored-loop count
and shared supplier payload count from retained ordinary geometry and headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def prepareCoreClass (input : SupplierInputPlan T) (e : Fin 117 → Fin T)
    (count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (placedCoreOrigins e) (supplierBatchCount input count saved tmp)

theorem prepareCoreClass_exec_within (input : SupplierInputPlan T)
    (e : Fin 117 → Fin T) (he : Function.Injective e) (count saved tmp : Fin T)
    (hreg : [e 109,e 116,count,saved,tmp].Nodup)
    (hcountReg : [input.publication.headers 0,input.publication.headers 3,count,saved,tmp].Nodup)
    (hclassOff : ∀ i, input.classDest i ≠ e 109 ∧ input.classDest i ≠ e 116)
    (V width radius L : ℕ) (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (r : PackedNormalizedJob A s) (v : HS T Q A U) (S : Stacks T A)
    (hclass : input.ClassReady r S) (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hL : S.R (e 35) = binSyms V L) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedCoreOriginsCost V s width radius L+supplierBatchCountCost r ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*preparedCoreOriginsCost V s width radius L+2*supplierBatchCountCost r)) depth
        (prepareCoreClass input e count saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R (e 109)
          ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
          (e 116) (List.replicate (coreGatherIndices s width radius L).length tick))
          count (List.replicate r.inputPayload.length tick))}) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedCoreOrigins_exec_within (body := body) e he
    hwidth hwide hLfit hA hV v S h37 hs hw hr hL hz hblank h104 h106 h116 depth
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R (e 109)
    ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
    (e 116) (List.replicate (coreGatherIndices s width radius L).length tick))}
  have hframe (k : Fin T) (ho : k ≠ e 109) (hc : k ≠ e 116) : F.R k = S.R k := by simp [F,ho,hc]
  have hclassF : input.ClassReady r F := hclass.of_frame (by
    intro i; exact hframe _ (hclassOff i).1 (hclassOff i).2)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := supplierBatchCount_exec_within (body := body) input count saved tmp hcountReg
    r v₁ F hclassF
    (by rw [hframe count (Ne.symm ‹e 109 ≠ count›) (Ne.symm ‹e 116 ≠ count›)]; exact hcount)
    (by rw [hframe saved (Ne.symm ‹e 109 ≠ saved›) (Ne.symm ‹e 116 ≠ saved›)]; exact hsaved)
    (by rw [hframe tmp (Ne.symm ‹e 109 ≠ tmp›) (Ne.symm ‹e 116 ≠ tmp›)]; exact htmp) depth
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,mn_seq_within_add he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
