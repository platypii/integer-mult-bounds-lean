module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBankPlacement
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBankClean

/-! Execute reservoir class/local conversion with generated scalar and metadata
inputs. The original matching table is preserved; only the local table changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {Q A : ℕ} {P U : Type}

def reservoirPreparedClassTableProgram (k : Fin 3) : Pr P 78 Q A U :=
  .seq (reservoirBankPrepareProgram reservoirBankPhysicalSlot k)
    (.seq (embProg reservoirConverterSlot Empty.elim (reservoirClassLocalTableProgram (P := Empty) k))
      (metadataClean (reservoirBankTargets reservoirBankPhysicalSlot)))

theorem reservoirPreparedClassTable_exec (body : P → Pr P 78 Q A U)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ)
    (hn : n < 2 ^ L) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (v : HS 78 Q A U) (S : Stacks 78 A)
    (hdimension : S.R 57 = binSyms L n) (hreservoir : S.R 58 = binSyms L H)
    (hspan : S.R 59 = binSyms L w)
    (htable : S.R 52 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate)))
    (hblank : ∀ j : Fin 78, j ≠ 57 → j ≠ 58 → j ≠ 59 → j ≠ 70 → j ≠ 52 → S.R j = []) :
    ∃ (v' : HS 78 Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ reservoirClassLocalTableCost n w L + 682 * L + 765 ∧
      Exec body (reservoirPreparedClassTableProgram k) (mk v S) m
        (mk v' { S with R := (Function.update S.R 34 (matchingEntryWords L
          (matchingTableEntries (n - 3 * w)
            (matchingMateCoordinate (reservoirClassLocalMatching n H hfit w hw k mate hinv))))) }) := by
  have hsep : ∀ j : Fin 29, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → j ≠ 28 →
      reservoirBankPhysicalSlot j ≠ 57 ∧ reservoirBankPhysicalSlot j ≠ 58 ∧
      reservoirBankPhysicalSlot j ≠ 59 ∧ reservoirBankPhysicalSlot j ≠ 70 ∧
      reservoirBankPhysicalSlot j ≠ 52 := by decide +kernel
  have hscope : ∀ j : Fin 29, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 13 → j ≠ 18 → j ≠ 28 →
      S.R (reservoirBankPhysicalSlot j) = [] := by
    intro j hj0 hj1 hj2 hj13 hj18 hj28
    obtain ⟨h0,h1,h2,h13,h52⟩ := hsep j hj0 hj1 hj2 hj13 hj18 hj28
    exact hblank _ h0 h1 h2 h13 h52
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirBankPrepare_exec body reservoirBankPhysicalSlot
    reservoirBankPhysicalSlot_injective L n H w hn hfit hw k v S hdimension hreservoir hspan hscope
  let C : Stacks 78 A := { S with R := reservoirBankPrepared S.R reservoirBankPhysicalSlot n H hfit w hw k L }
  have hconverterBlank : ∀ j : Fin 78, j.val < 57 → j ≠ 52 → S.R j = [] := by
    intro j hj hj52
    apply hblank <;> first | exact hj52 | (intro he; subst j; norm_num at hj)
  have hready : (embStk reservoirConverterSlot C).R = reservoirClassLocalBank n H hfit w hw k L mate :=
    reservoirBankPrepared_classLocal_table S.R n H hfit w hw k L mate hconverterBlank htable
  let smallBody : Empty → Pr Empty 57 Q A U := Empty.elim
  obtain ⟨u, m₂, hu, hm₂, hex⟩ := reservoirClassLocalTable_exec n H hfit w hw k L smallBody hn mate hinv
    (embDn reservoirConverterSlot v₁) (embStk reservoirConverterSlot C) hready
  let word := matchingEntryWords (A := A) L (matchingTableEntries (n - 3 * w)
    (matchingMateCoordinate (reservoirClassLocalMatching n H hfit w hw k mate hinv)))
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream reservoirConverterSlot reservoirConverterSlot_injective
    Empty.elim smallBody body (by intro q; exact q.elim) (reservoirClassLocalTableProgram k)
    v₁ C u m₂ 34 word hex
  let D : Stacks 78 A := { C with R := Function.update C.R 34 word }
  have htargets : 34 ∉ reservoirBankTargets reservoirBankPhysicalSlot := by decide +kernel
  have htargetsBlank : ∀ x ∈ reservoirBankTargets reservoirBankPhysicalSlot, S.R x = [] := by
    intro x hx
    simp only [reservoirBankTargets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (reservoirBankTargets reservoirBankPhysicalSlot)
    (by decide +kernel) v₂ D
  have hcost : metadataCleanCost D.R (reservoirBankTargets reservoirBankPhysicalSlot) = 60 * L + 65 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro x hx
      apply Function.update_of_ne
      intro he
      exact htargets (he ▸ hx))]
    exact reservoirBankPrepared_cleanCost S.R reservoirBankPhysicalSlot reservoirBankPhysicalSlot_injective
      n H hfit w hw k L (htargetsBlank _ (by simp [reservoirBankTargets]))
      (htargetsBlank _ (by simp [reservoirBankTargets]))
  have hfinal : metadataCleared D.R (reservoirBankTargets reservoirBankPhysicalSlot) = Function.update S.R 34 word := by
    rw [show D.R = Function.update C.R 34 word from rfl, metadataCleared_update _ _ _ _ htargets]
    rw [reservoirBankPrepared_clean S.R reservoirBankPhysicalSlot n H hfit w hw k L htargetsBlank]
  rw [hcost, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (60 * L + 65)), hu₃.trans (hu₂.trans (hu.trans hu₁)),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
