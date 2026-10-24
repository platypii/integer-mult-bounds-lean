module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingEntry
public import IntegerMultBounds.MathlibTM2.Routing.PermutationTableIterate
public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryReset

/-! Uniform counted generation of a complete canonical matching table from
one compact permutation table. Entries are rewound into ascending key order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

private theorem matchingEntryWords_append (L : ℕ) (xs ys : List (ℕ × ℕ)) :
    matchingEntryWords (A := A) L (xs ++ ys) = matchingEntryWords L xs ++ matchingEntryWords L ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, matchingEntryWords, ih, List.append_assoc]

def permutationMatchingTablePrefix (second : Bool) (L : ℕ) (f : Equiv.Perm (Fin N)) (n : ℕ) : List (Fin (A + 4)) :=
  matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate (permutationMatchingCoordinate second f)))

private theorem permutationMatchingTablePrefix_succ (second : Bool) (L : ℕ) (f : Equiv.Perm (Fin N))
    (j : ℕ) (hj : j < N) :
    permutationMatchingTablePrefix (A := A) second L f (j + 1) =
      permutationMatchingTablePrefix second L f j ++
        matchingEntryWord L j (permutationMatchingCoordinate second f ⟨j, hj⟩).val := by
  simp [permutationMatchingTablePrefix, matchingTableEntries, List.range_succ, List.map_append,
    matchingEntryWords_append, matchingEntryWords, matchingMateCoordinate, hj]

def permutationMatchingTableProgram (second : Bool) (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T) : Pr P T Q A U :=
  .seq (eachSym fuel archive
    (permutationMatchingEntryAdvanceProgram second rg out base steps count saved savedQuery savedIndex frame accum))
    (.seq (moveR archive fuel id) (moveR accum frame id))

theorem permutationMatchingTable_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum, fuel, archive].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (hfuelOff : ∀ j, fuel ≠ rg j) (harchiveOff : ∀ j, archive ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N))
    (v : HS T Q A U) (S : Stacks T A)
    (hquery : S.R (rg 2) = binSyms L 0)
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hfuel : (S.R fuel).length = N)
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 6 ∧
      Exec body (permutationMatchingTableProgram second rg out base steps count saved savedQuery savedIndex frame accum fuel archive)
        (mk v S) m (mk v' { S with R := (Function.update (Function.update S.R (rg 2) (binSyms L N)) frame
          (permutationMatchingTablePrefix second L f N)) }) := by
  have hregs := hreg
  regs_ne hregs
  have hentryRegs : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum].Nodup := by
    simp_all [List.nodup_cons]
  let tableWord := permutationMatchingTablePrefix (A := A) second L f
  let Ψ : ℕ → Regs T A := fun j => Function.update
    (Function.update S.R (rg 2) (binSyms L j)) accum (tableWord j).reverse
  let C := N * (3 * N * (30 * L + 39) + 84 * L + 125) + 70 * L + 94
  have hp : PricedSymSpec body
      (permutationMatchingEntryAdvanceProgram second rg out base steps count saved savedQuery savedIndex frame accum)
      fuel archive (S.R fuel) Ψ (fun _ => C) := by
    intro j hj u B _ hB
    have hjN : j < N := by simpa only [hfuel] using hj
    let q : Fin N := ⟨j, hjN⟩
    have keep (r : Fin T) (hf : r ≠ fuel) (ha : r ≠ archive) (hq : r ≠ rg 2) (hc : r ≠ accum) : B.R r = S.R r := by
      rw [hB r hf ha]
      simp only [Ψ, Function.update_of_ne hc, Function.update_of_ne hq]
    have core (i : Fin 10) (hi : i ≠ 2) : B.R (rg i) = S.R (rg i) :=
      keep _ (hfuelOff i).symm (harchiveOff i).symm (hrg.ne hi) (haccumOff i).symm
    have ready : MatchingLookupReady rg L q B := by
      constructor
      · simpa only [Ψ, Function.update_of_ne (haccumOff 2).symm, Function.update_self] using
          hB _ (hfuelOff 2).symm (harchiveOff 2).symm
      · intro i hi
        exact (core i (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (hblank i hi)
    obtain ⟨u', m, hu, hm, he⟩ := permutationMatchingEntryAdvance_exec body second rg hrg
      out base steps count saved savedQuery savedIndex frame accum hentryRegs hbase hsteps hout hcountOff hsavedOff
      hsavedQueryOff hindexOff hframeOff haccumOff L hN f q u B ready ((core 7 (by decide)).trans htable)
      (by rw [keep count ‹count ≠ fuel› ‹count ≠ archive› (hcountOff 2) ‹count ≠ accum›]; exact hcount)
      ((keep base ‹base ≠ fuel› ‹base ≠ archive› (hbase 2) ‹base ≠ accum›).trans hbaseBlank)
      ((keep steps ‹steps ≠ fuel› ‹steps ≠ archive› (hsteps 2) ‹steps ≠ accum›).trans hstepCount)
      ((core 8 (by decide)).trans htableSaved)
      ((keep out ‹out ≠ fuel› ‹out ≠ archive› (hout 2) ‹out ≠ accum›).trans houtput)
      ((keep saved ‹saved ≠ fuel› ‹saved ≠ archive› (hsavedOff 2) ‹saved ≠ accum›).trans hsaved)
      ((keep savedQuery ‹savedQuery ≠ fuel› ‹savedQuery ≠ archive› (hsavedQueryOff 2) ‹savedQuery ≠ accum›).trans hsavedQuery)
      ((keep savedIndex ‹savedIndex ≠ fuel› ‹savedIndex ≠ archive› (hindexOff 2) ‹savedIndex ≠ accum›).trans hindex)
      ((keep frame ‹frame ≠ fuel› ‹frame ≠ archive› (hframeOff 2) ‹frame ≠ accum›).trans hframe)
    let R' := Function.update (Function.update B.R accum
      ((matchingEntryWord L j (permutationMatchingCoordinate second f q).val).reverse ++ B.R accum)) (rg 2) (binSyms L (j + 1))
    refine ⟨u', R', m, hu, hm, he, ?_, ?_, ?_⟩
    · simp [R', hfuelOff, ‹accum ≠ fuel›.symm]
    · simp [R', harchiveOff, ‹accum ≠ archive›.symm]
    · intro r hrf hra
      by_cases hrq : r = rg 2
      · subst r; simp [R', Ψ, (haccumOff 2).symm]
      · by_cases hrc : r = accum
        · subst r
          simp only [R', Ψ, Function.update_of_ne (haccumOff 2), Function.update_self]
          rw [hB accum ‹accum ≠ fuel› ‹accum ≠ archive›]
          simp only [Ψ, Function.update_self]
          rw [show tableWord (j + 1) = tableWord j ++ matchingEntryWord L j (permutationMatchingCoordinate second f q).val
            from permutationMatchingTablePrefix_succ second L f j hjN, List.reverse_append]
        · simpa only [R', Ψ, Function.update_of_ne hrq, Function.update_of_ne hrc] using hB r hrf hra
  have hstart : ∀ r, r ≠ fuel → r ≠ archive → S.R r = Ψ 0 r := by
    intro r _ _
    by_cases hrq : r = rg 2
    · subst r; simpa only [Ψ, Function.update_of_ne (haccumOff 2).symm, Function.update_self] using hquery
    · by_cases hrc : r = accum
      · subst r; simpa [Ψ, tableWord, permutationMatchingTablePrefix, matchingTableEntries, matchingEntryWords] using haccum
      · simp [Ψ, hrq, hrc]
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hf, ha, hfinal⟩ := eachSym_priced_exec body ‹fuel ≠ archive› v S hp hstart
  let D : Stacks T A := { S with R := R₁ }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body archive fuel ‹fuel ≠ archive›.symm id v₁ D
  have hdlen : (D.R archive).length = N := by simp [D, ha, harchive, hfuel]
  have hrewind : movedR D.R archive fuel id (D.R archive) = Ψ N := by
    funext r
    by_cases hrf : r = fuel
    · subst r; simp [movedR, D, ha, hf, harchive, Ψ, hfuelOff, ‹accum ≠ fuel›.symm]
    · by_cases hra : r = archive
      · subst r; simp [movedR, hrf, harchive, Ψ, harchiveOff, ‹accum ≠ archive›.symm]
      · simpa only [movedR, Function.update_of_ne hrf, Function.update_of_ne hra, hfuel] using hfinal r hrf hra
  rw [hdlen, hrewind] at he₂
  let E : Stacks T A := { S with R := Ψ N }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body accum frame ‹frame ≠ accum›.symm id v₂ E
  have helen : (E.R accum).length = N * (2 * L + 2) := by
    simp [E, Ψ, tableWord, permutationMatchingTablePrefix, matchingEntryWords_length, matchingTableEntries]
  have hefinal : movedR E.R accum frame id (E.R accum) =
      Function.update (Function.update S.R (rg 2) (binSyms L N)) frame (tableWord N) := by
    funext r
    by_cases hrq : r = rg 2 <;> by_cases hrc : r = accum <;> by_cases hrf : r = frame <;>
      simp [E, Ψ, movedR, hrq, hrc, hrf, hframe, haccum,
        hframeOff 2, haccumOff 2, (hframeOff 2).symm, (haccumOff 2).symm,
        ‹frame ≠ accum›, ‹frame ≠ accum›.symm]
  rw [helen, hefinal] at he₃
  rw [symLoopPrice_constant, hfuel] at hm₁
  refine ⟨v₃, m₁ + ((2 * N + 2) + (2 * (N * (2 * L + 2)) + 2)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  dsimp only [C] at hm₁
  nlinarith only [hm₁]

def permutationMatchingTableClosedProgram (second : Bool) (rg : Fin 10 → Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T) : Pr P T Q A U :=
  .seq (permutationMatchingTableProgram second rg out base steps count saved savedQuery savedIndex frame accum fuel archive)
    (binaryResetProgram (rg 2) savedIndex (rg 3) (rg 4))

/-- The complete table is the only register change; the enumeration cursor
also restores to its original binary zero. -/
theorem permutationMatchingTableClosed_exec (body : P → Pr P T Q A U)
    (second : Bool) (rg : Fin 10 → Fin T) (hrg : Function.Injective rg)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (hreg : [out, base, steps, count, saved, savedQuery, savedIndex, frame, accum, fuel, archive].Nodup)
    (hbase : ∀ j, base ≠ rg j) (hsteps : ∀ j, steps ≠ rg j) (hout : ∀ j, out ≠ rg j)
    (hcountOff : ∀ j, count ≠ rg j) (hsavedOff : ∀ j, saved ≠ rg j)
    (hsavedQueryOff : ∀ j, savedQuery ≠ rg j) (hindexOff : ∀ j, savedIndex ≠ rg j)
    (hframeOff : ∀ j, frame ≠ rg j) (haccumOff : ∀ j, accum ≠ rg j)
    (hfuelOff : ∀ j, fuel ≠ rg j) (harchiveOff : ∀ j, archive ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Equiv.Perm (Fin N))
    (v : HS T Q A U) (S : Stacks T A)
    (hquery : S.R (rg 2) = binSyms L 0)
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (hcount : (S.R count).length = N) (hfuel : (S.R fuel).length = N)
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (N * (3 * N * (30 * L + 39) + 84 * L + 125) + 74 * L + 103) + 14 * L + 20 ∧
      Exec body (permutationMatchingTableClosedProgram second rg out base steps count saved savedQuery savedIndex frame accum fuel archive)
        (mk v S) m (mk v' { S with R := (Function.update S.R frame (permutationMatchingTablePrefix second L f N)) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationMatchingTable_exec body second rg hrg
    out base steps count saved savedQuery savedIndex frame accum fuel archive hreg
    hbase hsteps hout hcountOff hsavedOff hsavedQueryOff hindexOff hframeOff haccumOff hfuelOff harchiveOff
    L hN f v S hquery hblank htable hcount hfuel hbaseBlank hstepCount htableSaved houtput hsaved
    hsavedQuery hindex hframe haccum harchive
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 2) (binSyms L N)) frame
    (permutationMatchingTablePrefix second L f N)) }
  obtain ⟨v₂, hu₂, he₂⟩ := binaryReset_exec body (rg 2) savedIndex (rg 3) (rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff, hindexOff, ne_comm]) L N v₁ C
    (by simp [C, (hframeOff 2).symm])
    (by simpa [C, ‹savedIndex ≠ frame›, hindexOff 2] using hindex)
    (by simpa [C, (hframeOff 3).symm, hrg.eq_iff] using hblank 3 (by simp))
    (by simpa [C, (hframeOff 4).symm, hrg.eq_iff] using hblank 4 (by simp))
  have hfinal : ({ C with R := Function.update C.R (rg 2) (binSyms L 0) } : Stacks T A) =
      { S with R := Function.update S.R frame (permutationMatchingTablePrefix second L f N) } := by
    congr 1
    funext r
    by_cases hq : r = rg 2 <;> by_cases hf : r = frame <;>
      simp [C, hq, hf, hquery, hframeOff 2, (hframeOff 2).symm]
  rw [hfinal] at he₂
  exact ⟨v₂, m₁ + (14 * L + 14), hu₂.trans hu₁, by linarith only [hm₁], Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
