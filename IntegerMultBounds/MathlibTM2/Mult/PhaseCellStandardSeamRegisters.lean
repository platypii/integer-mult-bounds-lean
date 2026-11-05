module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringSeamProgram

/-! Fixed seam wiring inside the existing 117-register bank. Registers 0--14
are publication controls; 15--29 cover replica, widening and setup roles. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def standardRestoringSeamProgram : Pr P 117 Q A U :=
  restoringSeamPublication standardSeamPublicationPlan
    15 16 17 18 19 20 21 22 23 24 17 26 27 28 29

/-- All static hypotheses of the restoring stage, checked once for the fixed
wiring rather than once per boundary core or replica. -/
theorem standardSeamRegisters :
    (standardSeamPublicationPlan.support++[(95:Fin 117),96,15,16]).Nodup ∧
    ([(17:Fin 117),18,19,95,20,21,22,23]).Nodup ∧
    (standardSeamPublicationPlan.support++[(24:Fin 117),17,26,27,28]).Nodup ∧
    ([(26:Fin 117),standardSeamPublicationPlan.advances,29,95,96]).Nodup ∧
    (∀ i ∈ [(29:Fin 117),26,17,18,19,95,96,15,16,20,21,22,23],
      i ∉ [standardSeamPublicationPlan.count,standardSeamPublicationPlan.window,
        standardSeamPublicationPlan.wordWidth,standardSeamPublicationPlan.advances]) := by
  decide +kernel

/-- Injective placement preserves all finite register separations. -/
theorem standardSeamRegisters_widen {T : ℕ} (rg : Fin 117 → Fin T)
    (hinj : Function.Injective rg) :
    [rg 17,rg 18,rg 19,rg 95,rg 20,rg 21,rg 22,rg 23].Nodup := by
  simpa only [List.map_cons,List.map_nil] using standardSeamRegisters.2.1.map hinj

theorem standardSeamRegisters_mapped {T : ℕ} (rg : Fin 117 → Fin T)
    (hinj : Function.Injective rg) :
    let plan := standardSeamPublicationPlan.map rg hinj
    (plan.support++[rg 95,rg 96,rg 15,rg 16]).Nodup ∧
    [rg 17,rg 18,rg 19,rg 95,rg 20,rg 21,rg 22,rg 23].Nodup ∧
    (plan.support++[rg 24,rg 17,rg 26,rg 27,rg 28]).Nodup ∧
    [rg 26,plan.advances,rg 29,rg 95,rg 96].Nodup ∧
    (∀ i ∈ [rg 29,rg 26,rg 17,rg 18,rg 19,rg 95,rg 96,rg 15,rg 16,rg 20,rg 21,rg 22,rg 23],
      i ∉ [plan.count,plan.window,plan.wordWidth,plan.advances]) := by
  dsimp only
  refine ⟨?_,standardSeamRegisters_widen rg hinj,?_,?_,?_⟩
  · simpa [PreparedPublicationPlan.map,PreparedPublicationPlan.support,standardSeamPublicationPlan] using
      standardSeamRegisters.1.map hinj
  · simpa [PreparedPublicationPlan.map,PreparedPublicationPlan.support,standardSeamPublicationPlan] using
      standardSeamRegisters.2.2.1.map hinj
  · simpa [PreparedPublicationPlan.map,standardSeamPublicationPlan] using
      standardSeamRegisters.2.2.2.1.map hinj
  · change ∀ i ∈ ([(29:Fin 117),26,17,18,19,95,96,15,16,20,21,22,23].map rg),
      i ∉ ([standardSeamPublicationPlan.count,standardSeamPublicationPlan.window,
        standardSeamPublicationPlan.wordWidth,standardSeamPublicationPlan.advances].map rg)
    intro i hi hm
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
    have hkj : k = j := hinj he
    subst k
    exact standardSeamRegisters.2.2.2.2 j hj hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
