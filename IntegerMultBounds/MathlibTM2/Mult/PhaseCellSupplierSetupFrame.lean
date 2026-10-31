module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierSetupPlan

/-! Ordinary setup readiness depends on one fixed register support and the left
bank. Queue suffixes and accumulated results outside it may change freely. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T A s : ℕ} [NeZero s] {input : SupplierInputPlan T}

def scalarSupport (plan : SupplierSetupPlan input) : List (Fin T) :=
  List.ofFn (fun i => plan.scalar (.v i)) ++
    ([plan.scalar .wr,plan.scalar .wn,plan.scalar .acc] ++ List.ofFn (fun i => plan.scalar (.z i)))

theorem scalar_mem (plan : SupplierSetupPlan input) (i : TblR 25) : plan.scalar i ∈ plan.scalarSupport := by
  cases i with
  | v i => exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  | wr => simp [scalarSupport]
  | wn => simp [scalarSupport]
  | acc => simp [scalarSupport]
  | z i => exact List.mem_append_right _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

def support (plan : SupplierSetupPlan input) : List (Fin T) :=
  input.baseSupport ++ (plan.scalarSupport ++ (List.ofFn input.masters ++
    ([plan.word,plan.saved,plan.tmp,plan.queue] ++
      [plan.geometry 0,plan.geometry 1,plan.geometry 2,plan.geometry 3,plan.geometry 4,
        plan.geometry 94,plan.geometry 104,plan.geometry 115])))

theorem Ready.of_frame {plan : SupplierSetupPlan input} {r : PackedNormalizedJob A s} {S F : Stacks T A}
    (h : plan.Ready r S) (hR : ∀ k ∈ plan.support, F.R k = S.R k) (hL : F.L = S.L) : plan.Ready r F := by
  have hb (k : Fin T) (hk : k ∈ input.baseSupport) := hR k (List.mem_append_left _ hk)
  have hs (i : TblR 25) := hR _ (List.mem_append_right _ (List.mem_append_left _ (plan.scalar_mem i)))
  have hm (i : Fin 10) := hR _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))
  have hx (k : Fin T) (hk : k ∈ [plan.word,plan.saved,plan.tmp,plan.queue]) := hR k
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk))))
  have hg (k : Fin 117) (hk : k ∈ [(0 : Fin 117),1,2,3,4,94,104,115]) :
      F.R (plan.geometry k) = S.R (plan.geometry k) := by
    apply hR
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    simpa only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] using
      (List.mem_map.mpr ⟨k,hk,rfl⟩ : plan.geometry k ∈
        [(0 : Fin 117),1,2,3,4,94,104,115].map plan.geometry)
  refine ⟨h.base.of_frame hb hL,?_,?_,?_,?_⟩
  · intro i hi; rw [hs]; exact h.scalarBlank i hi
  · intro i; rw [hm]; exact h.mastersBlank i
  · intro k hk; rw [hx k hk]; exact h.scratchBlank k hk
  · intro k hk; rw [hg k hk]; exact h.geometryBlank k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
