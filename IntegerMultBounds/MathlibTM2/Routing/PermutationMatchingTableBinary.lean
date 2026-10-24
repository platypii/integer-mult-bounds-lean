module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingTableInput
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCounterPairScope

/-! Complete matching-table generation from a binary dimension and compact
permutation table. Every counter and cursor starts and ends blank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationMatchingTableBinaryCost (N L : ℕ) : ℕ :=
  N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 119) + 42 * L + 42

def permutationMatchingTableBinaryProgram (second : Bool) (rg : Fin 10 → Fin T) (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T) : Pr P T Q A U :=
  binaryCounterPairScope src count fuel (rg 3) (rg 4) (rg 5)
    (permutationMatchingTableInputProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive)

theorem permutationMatchingTableBinary_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (hscope : [src, rg 2, rg 3, frame].Nodup)
    (hpair : [src, count, fuel, rg 3, rg 4, rg 5, frame].Nodup)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum, fuel, archive].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (hfuelOff : ∀ j, fuel ≠ rg j) (harchiveOff : ∀ j, archive ≠ rg j)
    (L : ℕ) (hN : N < 2 ^ L) (f : Equiv.Perm (Fin N))
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : S.R src = binSyms L N) (hquery : S.R (rg 2) = [])
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : S.R count = []) (hfuel : S.R fuel = [])
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost N L ∧
      Exec body (permutationMatchingTableBinaryProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive)
        (mk v S) m (mk v' { S with R := (Function.update S.R frame (permutationMatchingTablePrefix second L f N)) }) := by
  have hregs := hreg
  regs_ne hregs
  have hpairs := hpair
  regs_ne hpairs
  let C : Stacks T A := { S with R := (Function.update
    (Function.update S.R count (List.replicate N tick)) fuel (List.replicate N tick)) }
  have external (r : Fin T) (hc : r ≠ count) (hf : r ≠ fuel) : C.R r = S.R r := by simp [C, hc, hf]
  have core (j : Fin 10) : C.R (rg j) = S.R (rg j) := external _ (hcountOff j).symm (hfuelOff j).symm
  have hcall : ∀ u : HS T Q A U,
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧
        (m : ℝ) ≤ (N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 20 * L + 26 : ℕ) ∧
        Exec body (permutationMatchingTableInputProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive)
          (mk u C) m (mk u' { C with R := Function.update C.R frame (permutationMatchingTablePrefix second L f N) }) := by
    intro u
    obtain ⟨u', m, hu, hm, he⟩ := permutationMatchingTableInput_exec body second rg hrg src
      out base steps count saved savedQuery savedIndex frame accum fuel archive hscope hreg
      hbase hsteps hout hcountOff hsavedOff hsavedQueryOff hindexOff hframeOff haccumOff hfuelOff harchiveOff
      L (Nat.le_of_lt hN) f u C
      (by rw [external src ‹src ≠ count› ‹src ≠ fuel›, hsource]; exact length_binSyms _ _)
      ((core 2).trans hquery) (fun j hj => (core j).trans (hblank j hj)) ((core 7).trans htable)
      (by simp [C, ‹count ≠ fuel›]) (by simp [C])
      ((external base ‹base ≠ count› ‹base ≠ fuel›).trans hbaseBlank)
      ((external steps ‹steps ≠ count› ‹steps ≠ fuel›).trans hstepCount)
      ((core 8).trans htableSaved) ((external out ‹out ≠ count› ‹out ≠ fuel›).trans houtput)
      ((external saved ‹count ≠ saved›.symm ‹saved ≠ fuel›).trans hsaved)
      ((external savedQuery ‹count ≠ savedQuery›.symm ‹savedQuery ≠ fuel›).trans hsavedQuery)
      ((external savedIndex ‹count ≠ savedIndex›.symm ‹savedIndex ≠ fuel›).trans hindex)
      ((external frame ‹count ≠ frame›.symm ‹frame ≠ fuel›).trans hframe)
      ((external accum ‹count ≠ accum›.symm ‹accum ≠ fuel›).trans haccum)
      ((external archive ‹count ≠ archive›.symm ‹fuel ≠ archive›.symm).trans harchive)
    exact ⟨u', m, hu, Nat.cast_le.mpr hm, he⟩
  obtain ⟨v', m, hu, hm, he⟩ := binaryCounterPairScope_exec body src count fuel (rg 3) (rg 4) (rg 5) frame hpair
    L N hN _ _ v S _ hsource hcount hfuel (hblank 3 (by simp)) (hblank 4 (by simp)) (hblank 5 (by simp)) hcall
  have hm' : m ≤ ((N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 20 * L + 26) +
      (8 * N + 11 * L + 8)) + (8 * N + 11 * L + 8) := by exact_mod_cast hm
  exact ⟨v', m, hu, by
    unfold permutationMatchingTableBinaryCost
    nlinarith only [hm'], he⟩

end IntegerMultBounds.MathlibTM2.Routing
