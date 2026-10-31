module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan

/-! Generated supplier readiness and setup bills depend only on owned and
retained registers. Results outside this support can accumulate between calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T A s : ℕ} [NeZero s]

def support (plan : SupplierInputPlan T) : List (Fin T) :=
  List.ofFn plan.work ++ (List.ofFn plan.masters ++ (List.ofFn plan.parameters ++
    (List.ofFn plan.publication.retained ++ [plan.width,plan.core,plan.word,plan.span])))

theorem work_mem (plan : SupplierInputPlan T) (i : Fin 325) : plan.work i ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem masters_mem (plan : SupplierInputPlan T) (i : Fin 10) : plan.masters i ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inr (Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem parameters_mem (plan : SupplierInputPlan T) (i : Fin 8) : plan.parameters i ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inr (Or.inr (Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩)))

theorem retained_mem (plan : SupplierInputPlan T) (i : Fin 9) : plan.publication.retained i ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩))))

theorem extra_mem (plan : SupplierInputPlan T) {i : Fin T}
    (hi : i ∈ [plan.width,plan.core,plan.word,plan.span]) : i ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr hi)))

theorem Ready.of_frame {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S F : Stacks T A}
    (h : plan.Ready r S) (hR : ∀ i ∈ plan.support, F.R i = S.R i) (hL : F.L = S.L) :
    plan.Ready r F := by
  have hw (i : Fin 325) := hR _ (plan.work_mem i)
  have hm (i : Fin 10) := hR _ (plan.masters_mem i)
  have hp (i : Fin 8) := hR _ (plan.parameters_mem i)
  have hr (i : Fin 9) := hR _ (plan.retained_mem i)
  have hx (i : Fin T) (hi : i ∈ [plan.width,plan.core,plan.word,plan.span]) := hR i (plan.extra_mem hi)
  constructor
  · intro i; rw [hw]; exact h.blank i
  · intro i; rw [hL]; exact h.left i
  · intro i; rw [hm]; exact h.masters i
  · rw [hr]; exact h.radius
  · rw [hr]; exact h.geometryWidth
  · intro i; simpa only [PublicationInputPlan.headers,hr] using h.headers i
  · rw [hr]; exact h.payload
  · rw [hr]; exact h.tmp
  · rw [hr]; exact h.saved
  · rw [hx _ (by simp)]; exact h.span
  · intro i; rw [hp]; exact h.parameters i
  · rw [hx _ (by simp)]; exact h.width
  · rw [hx _ (by simp)]; exact h.core
  · rw [hx _ (by simp)]; exact h.word

theorem Ready.update {plan : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : plan.Ready r S) (i : Fin T) (hi : i ∉ plan.support) (xs : List (Fin (A+4))) :
    plan.Ready r {S with R := Function.update S.R i xs} := by
  apply h.of_frame (F := {S with R := Function.update S.R i xs}) _ rfl
  intro j hj
  change Function.update S.R i xs j = S.R j
  have hji : j ≠ i := by intro he; exact hi (he ▸ hj)
  exact Function.update_of_ne hji _ _

theorem masterCost_congr (plan : SupplierInputPlan T) (S F : Stacks T A)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) : plan.masterCost F = plan.masterCost S := by
  unfold masterCost masterHeaderCopies copyUnaryHeadersCost
  simp only [List.map_ofFn,Function.comp_def,hR _ (plan.masters_mem _)]

theorem headerCost_congr (plan : SupplierInputPlan T) (S F : Stacks T A)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) : plan.headerCost F = plan.headerCost S := by
  unfold headerCost descriptorHeaderCopies copyUnaryHeadersCost
  simp only [List.map_ofFn,Function.comp_def,PublicationInputPlan.headers,hR _ (plan.retained_mem _)]

theorem timeCost_congr (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S F : Stacks T A)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) : plan.timeCost r F = plan.timeCost r S := by
  simp only [timeCost,plan.masterCost_congr S F hR,plan.headerCost_congr S F hR]

theorem stock_congr (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S F : Stacks T A)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) : plan.stock r F = plan.stock r S := by
  simp only [stock,plan.masterCost_congr S F hR,plan.headerCost_congr S F hR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
