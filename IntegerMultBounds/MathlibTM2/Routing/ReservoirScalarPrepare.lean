module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirProductionScalars
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirScalarExport

/-! Generate and export all six reservoir converter scalars, then erase the
production bank. Only converter input fields change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirProductionSlot : Fin 22 → Fin 28 := Fin.castLE (by decide)

theorem reservoirProductionSlot_injective : Function.Injective reservoirProductionSlot := by
  decide +kernel

def reservoirProductionPrivate (rg : Fin 22 → Fin T) : List (Fin T) :=
  rg 14 :: reservoirOperandTargets.map rg

def reservoirScalarPrepareProgram (rg : Fin 28 → Fin T) : Pr P T Q A U :=
  .seq (reservoirProductionScalarsProgram (rg ∘ reservoirProductionSlot))
    (.seq (reservoirScalarExportProgram rg) (metadataClean (reservoirProductionPrivate (rg ∘ reservoirProductionSlot))))

def reservoirProductionBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T)
    (L n H w : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (reservoirExchangeOperandBank R (rg ∘ reservoirProductionSlot) L n H w)
    (rg 14) (binSyms L (n - 3 * w))

theorem reservoirProductionBank_read (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ) (j : Fin 28) :
    reservoirProductionBank R rg L n H w (rg j) =
      if j = 14 then binSyms L (n - 3 * w)
      else if j.val < 22 then
        reservoirExchangeOperandBank R (rg ∘ reservoirProductionSlot) L n H w (rg j)
      else R (rg j) := by
  by_cases hj : j = 14
  · subst j; simp [reservoirProductionBank]
  · rw [reservoirProductionBank, Function.update_of_ne (hrg.ne hj), if_neg hj]
    split
    · rfl
    · have hne (a : Fin 22) : rg j ≠ rg (reservoirProductionSlot a) := by
        apply hrg.ne
        intro he
        have hv := congrArg Fin.val he
        change j.val = a.val at hv
        omega
      simp only [reservoirExchangeOperandBank, reservoirExchangeOperandJobs, List.foldl_cons,
        List.foldl_nil, Function.comp_apply]
      simp only [Function.update_of_ne (hne _)]

theorem reservoirScalarOutputs_clean (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ) :
    metadataCleared (reservoirScalarOutputs R rg L n H w)
      (reservoirProductionPrivate (rg ∘ reservoirProductionSlot)) =
    reservoirScalarOutputs (metadataCleared R (reservoirProductionPrivate (rg ∘ reservoirProductionSlot))) rg L n H w := by
  simp only [reservoirScalarOutputs]
  repeat rw [metadataCleared_update _ _ _ _ (by
    simp [reservoirProductionPrivate, reservoirOperandTargets, reservoirProductionSlot, hrg.eq_iff])]

theorem reservoirScalarPrepare_cleanCost_le
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ) :
    metadataCleanCost (reservoirScalarOutputs (reservoirProductionBank R rg L n H w) rg L n H w)
      (reservoirProductionPrivate (rg ∘ reservoirProductionSlot)) ≤ 24 * L + 25 := by
  let small := rg ∘ reservoirProductionSlot
  have hs : Function.Injective small := hrg.comp reservoirProductionSlot_injective
  have hlen : ∀ x ∈ reservoirProductionPrivate small,
      (reservoirScalarOutputs (reservoirProductionBank R rg L n H w) rg L n H w x).length ≤ L := by
    intro x hx
    change x ∈ ((14 : Fin 22) :: reservoirOperandTargets).map small at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hne (a : Fin 28) (ha : 22 ≤ a.val) : small j ≠ rg a := by
      apply hrg.ne
      intro he
      have hv := congrArg Fin.val he
      change j.val = a.val at hv
      omega
    simp only [reservoirScalarOutputs, Function.update_of_ne (hne 22 (by decide)),
      Function.update_of_ne (hne 23 (by decide)), Function.update_of_ne (hne 24 (by decide)),
      Function.update_of_ne (hne 25 (by decide)), Function.update_of_ne (hne 26 (by decide)),
      Function.update_of_ne (hne 27 (by decide))]
    simp only [reservoirOperandTargets, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (simp [reservoirProductionBank, small, reservoirProductionSlot]; done)
      | (rw [reservoirProductionBank, Function.update_of_ne (by
            apply hrg.ne; decide)]
         change (reservoirExchangeOperandBank R small L n H w (small _)).length ≤ L
         rw [reservoirExchangeOperandBank_read R small hs]
         exact (length_binSyms L _).le)
  have hc := metadataCleanCost_le _ (reservoirProductionPrivate small) L hlen
  have hlength : (reservoirProductionPrivate small).length = 12 := rfl
  rw [hlength] at hc
  convert hc using 1
  ring

theorem reservoirScalarPrepare_exec (body : P → Pr P T Q A U)
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n H w : ℕ)
    (hn : n < 2 ^ L) (hfit : 9 * H ≤ n) (hw : w ≤ H)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hreservoir : S.R (rg 1) = binSyms L H)
    (hspan : S.R (rg 2) = binSyms L w)
    (hblank : ∀ j : Fin 28, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 150 * L + 170 ∧
      Exec body (reservoirScalarPrepareProgram rg) (mk v S) m
        (mk v' { S with R := reservoirScalarOutputs S.R rg L n H w }) := by
  let small := rg ∘ reservoirProductionSlot
  have hs : Function.Injective small := hrg.comp reservoirProductionSlot_injective
  have hsmallBlank : ∀ j : Fin 22, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → S.R (small j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
    · exact fun he => hj13 (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
    · exact fun he => hj18 (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
  obtain ⟨v₁, hu₁, he₁⟩ := reservoirProductionScalars_exec body small hs L n H w hn hfit hw v S
    hdimension hreservoir hspan hsmallBlank
  let B : Stacks T A := { S with R := reservoirProductionBank S.R rg L n H w }
  have read (j : Fin 22) (hj : j ≠ 14) : B.R (small j) =
      reservoirExchangeOperandBank S.R small L n H w (small j) := by
    apply Function.update_of_ne
    apply hrg.ne
    exact fun he => hj (Fin.ext (congrArg (fun a : Fin 28 => a.val) he))
  have hzero : B.R (rg 6) = binSyms L 0 :=
    (read 6 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 6)
  have hspanB : B.R (rg 2) = binSyms L w :=
    ((read 2 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 2)).trans hspan
  have hmiddle : B.R (rg 14) = binSyms L (n - 3 * w) := by simp [B, reservoirProductionBank]
  have htriple : B.R (rg 8) = binSyms L (3 * H) :=
    (read 8 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 8)
  have hsextuple : B.R (rg 9) = binSyms L (6 * H) :=
    (read 9 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 9)
  have hblankB : ∀ j : Fin 28, j = 10 ∨ j = 11 ∨ j = 12 ∨ 22 ≤ j.val → B.R (rg j) = [] := by
    intro j hj
    rcases hj with rfl | rfl | rfl | hj
    · exact ((read 10 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 10)).trans
        (hblank 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact ((read 11 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 11)).trans
        (hblank 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact ((read 12 (by decide)).trans (reservoirExchangeOperandBank_read S.R small hs L n H w 12)).trans
        (hblank 12 (by decide) (by decide) (by decide) (by decide) (by decide))
    · change reservoirProductionBank S.R rg L n H w (rg j) = []
      rw [reservoirProductionBank_read S.R rg hrg]
      rw [if_neg (by intro he; subst j; norm_num at hj), if_neg (Nat.not_lt.mpr hj)]
      apply hblank <;> intro he <;> subst j <;> norm_num at hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := reservoirScalarExport_exec body rg hrg L n H w v₁ B
    hzero hspanB hmiddle htriple hsextuple hblankB
  let C : Stacks T A := { B with R := reservoirScalarOutputs B.R rg L n H w }
  have hkeys : (reservoirProductionPrivate small).Nodup := by
    simp [reservoirProductionPrivate, reservoirOperandTargets, List.nodup_cons, hs.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body _ hkeys v₂ C
  have hrestore : metadataCleared B.R (reservoirProductionPrivate small) = S.R := by
    apply reservoirProductionScalars_clean S.R small hs L n H w
    intro j hj
    simp only [reservoirOperandTargets, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply hsmallBlank <;> decide
  have hfinal : metadataCleared C.R (reservoirProductionPrivate small) = reservoirScalarOutputs S.R rg L n H w := by
    rw [show C.R = reservoirScalarOutputs B.R rg L n H w from rfl,
      reservoirScalarOutputs_clean B.R rg hrg, hrestore]
  rw [hfinal] at he₃
  refine ⟨v₃, (90 * L + 102) + (m₂ + metadataCleanCost C.R (reservoirProductionPrivate small)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hc := reservoirScalarPrepare_cleanCost_le S.R rg hrg L n H w
  change metadataCleanCost C.R (reservoirProductionPrivate small) ≤ 24 * L + 25 at hc
  omega

end IntegerMultBounds.MathlibTM2.Routing
