module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingTableBinary
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirPreparedClassTable

/-! Generate an original canonical matching table, execute reservoir-class/local
conversion, and erase the generated original table. Scalar and exchange metadata setup are generated from compact binary inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {P U : Type}

theorem permutationMatchingCoordinate_involutive {n : ℕ} (second : Bool) (f : Equiv.Perm (Fin n)) :
    Function.Involutive (permutationMatchingCoordinate second f) := by
  cases second with
  | false => exact (permutation_two_matchings f).1
  | true => exact (permutation_two_matchings f).2.1

def permutationReservoirTableProgram (second : Bool) (rg : Fin 10 → Fin T) (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (producer : Fin 78 → Fin T) (k : Fin 3) : Pr P T Q A U :=
  .seq (permutationMatchingTableBinaryProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive)
    (.seq (embProg producer Empty.elim (reservoirPreparedClassTableProgram (P := Empty) k)) (bclear frame))

theorem permutationReservoirTable_exec (body : P → Pr P T Q A U) (n : ℕ)
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
    (L : ℕ) (hN : n < 2 ^ L) (f : Equiv.Perm (Fin n))
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : S.R src = binSyms L n) (hquery : S.R (rg 2) = [])
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate f)))
    (hcount : S.R count = []) (hfuel : S.R fuel = [])
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = [])
    (producer : Fin 78 → Fin T) (hp : Function.Injective producer) (hjoin : frame = producer 52)
    (H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (hdimension : S.R (producer 57) = binSyms L n)
    (hreservoir : S.R (producer 58) = binSyms L H)
    (hspan : S.R (producer 59) = binSyms L w)
    (hproduction : ∀ j : Fin 78, j ≠ 57 → j ≠ 58 → j ≠ 59 → j ≠ 70 → j ≠ 52 → S.R (producer j) = []) :
    let localMate := reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f)
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ permutationMatchingTableBinaryCost n L + reservoirClassLocalTableCost n w L + 682 * L + 765 + 2 * (n * (2 * L + 2)) + 2 ∧
      Exec body (permutationReservoirTableProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive producer k)
        (mk v S) m (mk v' { S with R := (Function.update S.R (producer 34)
          (matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate localMate)))) }) := by
  dsimp only
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationMatchingTableBinary_exec body second rg hrg src
    out base steps count saved savedQuery savedIndex frame accum fuel archive hscope hpair hreg
    hbase hsteps hout hcountOff hsavedOff hsavedQueryOff hindexOff hframeOff haccumOff hfuelOff harchiveOff
    L hN f v S hsource hquery hblank htable hcount hfuel hbaseBlank hstepCount htableSaved houtput hsaved
    hsavedQuery hindex hframe haccum harchive
  let C : Stacks T A := { S with R := Function.update S.R frame (permutationMatchingTablePrefix second L f n) }
  have keep (j : Fin 78) (hj : j ≠ 52) : C.R (producer j) = S.R (producer j) := by
    apply Function.update_of_ne
    rw [hjoin]
    exact hp.ne hj
  have htableReady : C.R (producer 52) = matchingEntryWords L
      (matchingTableEntries n (matchingMateCoordinate (permutationMatchingCoordinate second f))) := by
    rw [← hjoin]
    simp [C, permutationMatchingTablePrefix]
  let smallBody : Empty → Pr Empty 78 Q A U := Empty.elim
  obtain ⟨u, m₂, hu, hm₂, hex⟩ := reservoirPreparedClassTable_exec smallBody n H hfit w hw k L hN
    (permutationMatchingCoordinate second f) (permutationMatchingCoordinate_involutive second f)
    (embDn producer v₁) (embStk producer C)
    ((keep 57 (by decide)).trans hdimension) ((keep 58 (by decide)).trans hreservoir)
    ((keep 59 (by decide)).trans hspan) htableReady
    (fun j h57 h58 h59 h70 h52 => (keep j h52).trans (hproduction j h57 h58 h59 h70 h52))
  let localWord := matchingEntryWords (A := A) L (matchingTableEntries (n - 3 * w)
    (matchingMateCoordinate (reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f))))
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream producer hp Empty.elim smallBody body
    (by intro q; exact q.elim) (reservoirPreparedClassTableProgram k) v₁ C u m₂ 34 localWord hex
  let D : Stacks T A := { C with R := Function.update C.R (producer 34) localWord }
  have hne : producer 34 ≠ frame := by rw [hjoin]; exact hp.ne (by decide)
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) frame v₂ D
  have hlen : (D.R frame).length = n * (2 * L + 2) := by
    simp [D, C, hne.symm, permutationMatchingTablePrefix, matchingEntryWords_length, matchingTableEntries]
  have hfinal : ({ D with R := Function.update D.R frame [] } : Stacks T A) =
      { S with R := Function.update S.R (producer 34) localWord } := by
    congr 1
    funext r
    by_cases hf : r = frame
    · subst r; simp [hne.symm, hframe]
    · by_cases hd : r = producer 34 <;> simp [D, C, hf, hd, hne]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (n * (2 * L + 2)) + 2)), hu₃.trans (hu₂.trans (hu.trans hu₁)),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
