module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeOperandFrames
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Generate the reservoir exchange metadata from binary dimension and widths,
then erase every generated operand. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirOperandTargets : List (Fin 22) := [3,4,5,6,7,8,9,15,16,17,21]

def reservoirMetadataProgram (rg : Fin 22 → Fin T) (k : Fin 3) (inverse : Bool) : Pr P T Q A U :=
  .seq (reservoirExchangeOperandsProgram rg)
    (.seq (coordinateExchangeFrameSchedule (fun stage => rg ∘ reservoirExchangeFrameSlot k stage)
      (reservoirCoordinateOrder inverse)) (metadataClean (reservoirOperandTargets.map rg)))

theorem reservoirExchangeOperandBank_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ)
    (hblank : ∀ j ∈ reservoirOperandTargets, R (rg j) = []) :
    metadataCleared (reservoirExchangeOperandBank R rg L n H w)
      (reservoirOperandTargets.map rg) = R := by
  funext x
  by_cases hx : ∃ j, x = rg j
  · obtain ⟨j, rfl⟩ := hx
    by_cases hj : j ∈ reservoirOperandTargets
    · rw [metadataCleared_at _ _ _ (List.mem_map.mpr ⟨j, hj, rfl⟩)]
      exact (hblank j hj).symm
    · rw [metadataCleared_keep _ _ _ (by intro hm; obtain ⟨a, ha, he⟩ := List.mem_map.mp hm; exact hj ((hrg he) ▸ ha))]
      rw [reservoirExchangeOperandBank_read R rg hrg]
      fin_cases j <;> simp_all [reservoirOperandTargets]
  · have hne (j : Fin 22) : x ≠ rg j := fun he => hx ⟨j, he⟩
    rw [metadataCleared_keep _ _ _ (by intro hm; obtain ⟨a, _, he⟩ := List.mem_map.mp hm; exact hx ⟨a, he.symm⟩)]
    simp [reservoirExchangeOperandBank, reservoirExchangeOperandJobs, hne]

theorem reservoirMetadata_generate_exec (body : P → Pr P T Q A U)
    (rg : Fin 22 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hfit : 9 * H ≤ n) (hw : w ≤ H) (k : Fin 3) (inverse : Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirMetadataProgram rg k inverse) (mk v S) (236 * L + 265)
        (mk v' { S with R := (Function.update S.R (rg 18)
          (middleLookupMetadata n H hfit w hw k L inverse ++ S.R (rg 18))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirExchangeOperands_exec body rg hrg L n H w hn hfit hw v S
    hdimension hreservoir hspan hblank
  let B : Stacks T A := { S with R := reservoirExchangeOperandBank S.R rg L n H w }
  have ready := reservoirExchangeOperandFrames_ready S.R rg hrg L n H w hfit hw hspan k
  obtain ⟨v₂, hu₂, he₂⟩ := middleLookupMetadata_generate_exec body n H hfit w hw k L hn inverse
    (fun stage => rg ∘ reservoirExchangeFrameSlot k stage)
    (fun stage => hrg.comp (reservoirExchangeFrameSlot_injective k stage)) (rg 18)
    (fun stage => congrArg rg (reservoirExchangeFrameSlot_destination k stage)) v₁ B
    (fun stage => (ready stage).1) (fun stage => (ready stage).2.1) (fun stage => (ready stage).2.2)
    (fun stage i hi => reservoirExchangeOperandFrames_blank S.R rg hrg L n H w
      (by intro j hj; apply hblank <;> rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide) k stage i hi)
  let word := middleLookupMetadata (A := A) n H hfit w hw k L inverse ++ S.R (rg 18)
  have hdst : B.R (rg 18) = S.R (rg 18) := reservoirExchangeOperandBank_read S.R rg hrg L n H w 18
  rw [hdst] at he₂
  let C : Stacks T A := { B with R := Function.update B.R (rg 18) word }
  have hkeys : (reservoirOperandTargets.map rg).Nodup :=
    List.Nodup.map hrg (by decide +kernel)
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body _ hkeys v₂ C
  have hcost : metadataCleanCost C.R (reservoirOperandTargets.map rg) = 22 * L + 23 := by
    have hlength : ∀ x ∈ reservoirOperandTargets.map rg, (C.R x).length = L := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hj18 : j ≠ 18 := by intro he; subst j; simp [reservoirOperandTargets] at hj
      change (Function.update B.R (rg 18) word (rg j)).length = L
      rw [Function.update_of_ne (hrg.ne hj18)]
      change (reservoirExchangeOperandBank S.R rg L n H w (rg j)).length = L
      rw [reservoirExchangeOperandBank_read S.R rg hrg]
      simp only [reservoirOperandTargets, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact length_binSyms L _
    have cost_eq (keys : List (Fin T)) (hk : ∀ x ∈ keys, (C.R x).length = L) :
        metadataCleanCost C.R keys = keys.length * (2 * L + 2) + 1 := by
      induction keys with
      | nil => simp [metadataCleanCost]
      | cons x xs ih =>
        rw [metadataCleanCost, hk x (by simp), ih (by intro y hy; exact hk y (by simp [hy]))]
        simp only [List.length_cons]
        ring
    rw [cost_eq _ hlength]
    simp [reservoirOperandTargets]
    ring
  have hfinal : metadataCleared C.R (reservoirOperandTargets.map rg) = Function.update S.R (rg 18) word := by
    rw [show C.R = Function.update B.R (rg 18) word from rfl,
      metadataCleared_update _ _ _ _ (by simp [reservoirOperandTargets, hrg.eq_iff])]
    rw [reservoirExchangeOperandBank_clean S.R rg hrg L n H w]
    intro j hj
    simp only [reservoirOperandTargets, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply hblank <;> decide
  rw [hcost, hfinal] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁),
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
