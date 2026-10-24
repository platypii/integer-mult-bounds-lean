module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingTable
public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroScope

/-! Generate and erase the table cursor from a preserved source width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

def permutationMatchingTableInputProgram (second : Bool) (rg : Fin 10 → Fin T) (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T) : Pr P T Q A U :=
  binaryZeroScope src (rg 2) (rg 3)
    (permutationMatchingTableClosedProgram second rg out base steps count saved savedQuery savedIndex frame accum fuel archive)

theorem permutationMatchingTableInput_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (hscope : [src, rg 2, rg 3, frame].Nodup)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum, fuel, archive].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (hfuelOff : ∀ j, fuel ≠ rg j) (harchiveOff : ∀ j, archive ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N))
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : (S.R src).length = L) (hquery : S.R (rg 2) = [])
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hfuel : (S.R fuel).length = N)
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 20 * L + 26 ∧
      Exec body (permutationMatchingTableInputProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive)
        (mk v S) m (mk v' { S with R := (Function.update S.R frame (permutationMatchingTablePrefix second L f N)) }) := by
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L 0) }
  have hkeep (j : Fin 10) (hj : j ≠ 2) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  have hcall : ∀ u : HS T Q A U,
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧
        (m : ℝ) ≤ (N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 14 * L + 20 : ℕ) ∧
        Exec body (permutationMatchingTableClosedProgram second rg out base steps count saved savedQuery savedIndex frame accum fuel archive)
          (mk u C) m (mk u' { C with R := Function.update C.R frame (permutationMatchingTablePrefix second L f N) }) := by
    intro u
    obtain ⟨u', m, hu, hm, he⟩ := permutationMatchingTableClosed_exec body second rg hrg
      out base steps count saved savedQuery savedIndex frame accum fuel archive hreg
      hbase hsteps hout hcountOff hsavedOff hsavedQueryOff hindexOff hframeOff haccumOff hfuelOff harchiveOff
      L hN f u C (by simp [C])
      (fun j hj => (hkeep j (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (hblank j hj))
      ((hkeep 7 (by decide)).trans htable)
      (by simpa [C, hcountOff 2] using hcount) (by simpa [C, hfuelOff 2] using hfuel)
      (by simpa [C, hbase 2] using hbaseBlank) (by simpa [C, hsteps 2] using hstepCount)
      ((hkeep 8 (by decide)).trans htableSaved)
      (by simpa [C, hout 2] using houtput) (by simpa [C, hsavedOff 2] using hsaved)
      (by simpa [C, hsavedQueryOff 2] using hsavedQuery) (by simpa [C, hindexOff 2] using hindex)
      (by simpa [C, hframeOff 2] using hframe) (by simpa [C, haccumOff 2] using haccum)
      (by simpa [C, harchiveOff 2] using harchive)
    exact ⟨u', m, hu, Nat.cast_le.mpr hm, he⟩
  obtain ⟨v', m, hu, hm, he⟩ := binaryZeroScope_exec body src (rg 2) (rg 3) frame hscope L _ _ v S _
    hsource hquery (hblank 3 (by simp)) hcall
  have hm' : m ≤ (N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 14 * L + 20) + (6 * L + 6) := by
    exact_mod_cast hm
  exact ⟨v', m, hu, by linarith only [hm'], he⟩

end IntegerMultBounds.MathlibTM2.Routing
