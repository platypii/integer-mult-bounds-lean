module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationReservoirTable
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileCompactControls
public import IntegerMultBounds.MathlibTM2.Routing.RouterMatchingTable

/-! Execute original matching generation, reservoir localization and profile
production from compact reservoir inputs, erasing both intermediate tables and
generated converter inputs. The prefix count is generated, compact stride/residue inputs are installed and
erased, and only pure frame readiness remains explicit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def permutationReservoirLocalWord (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H)
    (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n)) (L : ℕ) : List (Fin (A + 4)) :=
  matchingEntryWords L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate
    (reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
      (permutationMatchingCoordinate_involutive second f))))

def permutationReservoirSource (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H)
    (k : Fin 3) (second : Bool) (f : Equiv.Perm (Fin n)) (p : Par) (hsize : p.wy = n - 3 * w) : Fin p.wy → Fin p.wy :=
  fun q => Fin.cast hsize.symm (reservoirClassLocalMatching n H hfit w hw k (permutationMatchingCoordinate second f)
    (permutationMatchingCoordinate_involutive second f) (Fin.cast hsize q))

def permutationReservoirProfileProgram (second : Bool) (rg : Fin 10 → Fin T) (src : Fin T)
    (out base steps count saved savedQuery savedIndex frame accum fuel archive : Fin T)
    (producer : Fin 78 → Fin T) (k : Fin 3)
    (extract : Fin 8 → Fin T) (gather : Fin 18 → Fin T) (generate : Fin 11 → Fin T)
    (reverse : Bool) (dst : Fin T) (countRg : Fin 13 → Fin T) (control : Fin 11 → Fin T) : Pr P T Q A U :=
  .seq (permutationReservoirTableProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive producer k)
    (.seq (matchingControlScope control (matchingPrefixCountScope countRg
      (matchingFullProfileProductionProgram extract gather generate reverse dst))) (bclear (producer 34)))

theorem permutationReservoirProfile_exec (body : P → Pr P T Q A U) (n : ℕ)
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
    (Li Lk Ln Le M Ls : ℕ) (hN : n < 2 ^ (Li + Lk)) (f : Equiv.Perm (Fin n))
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : S.R src = binSyms (Li + Lk) n) (hquery : S.R (rg 2) = [])
    (hblank : ∀ j : Fin 10, j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 9 → S.R (rg j) = [])
    (htable : S.R (rg 7) = matchingEntryWords (Li + Lk) (matchingTableEntries n (matchingMateCoordinate f)))
    (hcount : S.R count = []) (hfuel : S.R fuel = [])
    (hbaseBlank : S.R base = []) (hstepCount : S.R steps = [])
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = []) (hsaved : S.R saved = [])
    (hsavedQuery : S.R savedQuery = []) (hindex : S.R savedIndex = []) (hframe : S.R frame = [])
    (haccum : S.R accum = []) (harchive : S.R archive = [])
    (producer : Fin 78 → Fin T) (hp : Function.Injective producer) (hjoin : frame = producer 52)
    (H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (hdimension : S.R (producer 57) = binSyms (Li + Lk) n)
    (hreservoir : S.R (producer 58) = binSyms (Li + Lk) H)
    (hspan : S.R (producer 59) = binSyms (Li + Lk) w)
    (hproduction : ∀ j : Fin 78, j ≠ 57 → j ≠ 58 → j ≠ 59 → j ≠ 70 → j ≠ 52 → S.R (producer j) = [])
    (p : Par) (hsize : p.wy = n - 3 * w) (dst : Fin T) (hdst : dst ≠ producer 34)
    (control : Fin 11 → Fin T) (hcontrol : Function.Injective control)
    (hcontrolOff : ∀ j, control j ≠ producer 34)
    (hcontrolStride : S.R (control 0) = binSyms Ls p.K)
    (hcontrolResidue : S.R (control 1) = binSyms Ls p.ρ)
    (hcontrolWidth : S.R (control 7) = binSyms M Lk)
    (hcontrolWidthFit : Lk < 2 ^ M) (hcontrolStrideFit : p.K < 2 ^ Ls)
    (hcontrolBlank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (control j) = [])
    (hcontrolDst : dst ≠ control 2 ∧ dst ≠ control 3)
    (setup : MatchingProductionFrame p (permutationReservoirSource n H hfit w hw k second f p hsize) Li Lk (Ln + Ls + Le) dst
      { S with R := matchingControlBank (Function.update S.R (producer 34)
        (permutationReservoirLocalWord n H hfit w hw k second f (Li + Lk))) control Lk p.K p.ρ })
    (hprofileJoin : setup.extract 5 = producer 34)
    (hstrideJoin : setup.gather 1 = control 2) (hresidueJoin : setup.gather 11 = control 3)
    (countRg : Fin 13 → Fin T) (hcountRg : Function.Injective countRg)
    (hcountTable : ∀ j, countRg j ≠ producer 34)
    (hcountControl : ∀ j, countRg j ≠ control 2 ∧ countRg j ≠ control 3)
    (hcountJoin : setup.extract 0 = countRg 4) (hcountDst : dst ≠ countRg 4)
    (hcountGather : ∀ j, setup.extract 0 ≠ setup.gather j)
    (hcountGenerate : ∀ j, setup.extract 0 ≠ setup.generate j)
    (hrowsFit : p.n < 2 ^ Ln) (hentryFit : 2 * (Li + Lk) + 2 < 2 ^ Le)
    (hrowsBinary : S.R (countRg 0) = binSyms Ln p.n)
    (hstrideBinary : S.R (countRg 1) = binSyms Ls p.K)
    (hwidthBinary : S.R (countRg 11) = binSyms Le (Li + Lk))
    (hcountBlank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 10 → j ≠ 11 → S.R (countRg j) = []) :
    let mate := permutationReservoirSource n H hfit w hw k second f p hsize
    let output := sourceCoordinateInputWords Li Lk
      (profileCoordinateInputs p setup.hK (matchingDirectionTargets mate setup.reverse) mate) ++ S.R dst
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (permutationMatchingTableBinaryCost n (Li + Lk) + reservoirClassLocalTableCost n w (Li + Lk) + 682 * (Li + Lk) + 765 +
        2 * (n * (2 * (Li + Lk) + 2)) + 2) + matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Ls + Le) +
        2 * ((n - 3 * w) * (2 * (Li + Lk) + 2)) + 2 +
        matchingPrefixCountCost Ln Ls Le + 24 * Le + 29 + 2 * (Ln + Ls + Le) + 2 + 4 * M * (4 * Lk + 11) + 24 * Ls + 56 * Lk + 90 ∧
      Exec body (permutationReservoirProfileProgram second rg src out base steps count saved savedQuery savedIndex frame accum fuel archive
        producer k setup.extract setup.gather setup.generate setup.reverse dst countRg control) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := permutationReservoirTable_exec body n second rg hrg src
    out base steps count saved savedQuery savedIndex frame accum fuel archive hscope hpair hreg
    hbase hsteps hout hcountOff hsavedOff hsavedQueryOff hindexOff hframeOff haccumOff hfuelOff harchiveOff
    (Li + Lk) hN f v S hsource hquery hblank htable hcount hfuel hbaseBlank hstepCount htableSaved houtput hsaved
    hsavedQuery hindex hframe haccum harchive producer hp hjoin H hfit w hw k hdimension hreservoir hspan hproduction
  let mate := permutationReservoirSource n H hfit w hw k second f p hsize
  let C : Stacks T A := { S with R := (Function.update S.R (producer 34)
    (permutationReservoirLocalWord n H hfit w hw k second f (Li + Lk))) }
  let E : Stacks T A := { C with R := matchingControlBank C.R control Lk p.K p.ρ }
  have hgenerated : E.R (setup.extract 5) = matchingEntryWords (Li + Lk)
      (matchingTableEntries p.wy (matchingMateCoordinate mate)) := by
    rw [hprofileJoin]
    simp only [E, matchingControlBank, Function.update_of_ne (hcontrolOff 2).symm,
      Function.update_of_ne (hcontrolOff 3).symm, C, Function.update_self, permutationReservoirLocalWord, mate]
    unfold permutationReservoirSource
    rw [matchingMateCoordinate_cast hsize, hsize]
  let ready : MatchingProductionFrame p mate Li Lk (Ln + Ls + Le) dst E := { setup with hinput := hgenerated }
  have countKeep (j : Fin 13) : C.R (countRg j) = S.R (countRg j) :=
    Function.update_of_ne (hcountTable j) _ _
  have controlKeep (j : Fin 11) : C.R (control j) = S.R (control j) :=
    Function.update_of_ne (hcontrolOff j) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingProfileCompactControls_exec body p mate Li Lk Ln Le M Ls
    v₁ C dst control hcontrol ((controlKeep 0).trans hcontrolStride) ((controlKeep 1).trans hcontrolResidue)
    ((controlKeep 7).trans hcontrolWidth) hcontrolWidthFit hcontrolStrideFit
    (fun j hj0 hj1 hj7 => (controlKeep j).trans (hcontrolBlank j hj0 hj1 hj7)) hcontrolDst ready
    hstrideJoin hresidueJoin countRg hcountRg hcountControl hcountJoin hcountDst hcountGather hcountGenerate
    hrowsFit hentryFit ((countKeep 0).trans hrowsBinary) ((countKeep 1).trans hstrideBinary)
    ((countKeep 11).trans hwidthBinary)
    (fun j hj0 hj1 hj10 hj11 => (countKeep j).trans (hcountBlank j hj0 hj1 hj10 hj11))
  have hdstC : C.R dst = S.R dst := Function.update_of_ne hdst _ _
  change Exec body _ (mk v₁ C) m₂ (mk v₂ { C with R := (Function.update C.R dst
    (sourceCoordinateInputWords Li Lk (profileCoordinateInputs p setup.hK (matchingDirectionTargets mate setup.reverse) mate) ++ C.R dst)) }) at he₂
  rw [hdstC] at he₂
  let output := sourceCoordinateInputWords (A := A) Li Lk
    (profileCoordinateInputs p setup.hK (matchingDirectionTargets mate setup.reverse) mate) ++ S.R dst
  let D : Stacks T A := { C with R := Function.update C.R dst output }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (producer 34) v₂ D
  have hlocalBlank : S.R (producer 34) = [] :=
    hproduction 34 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlen : (D.R (producer 34)).length = (n - 3 * w) * (2 * (Li + Lk) + 2) := by
    simp [D, C, hdst.symm, permutationReservoirLocalWord, matchingEntryWords_length, matchingTableEntries]
  have hfinal : ({ D with R := Function.update D.R (producer 34) [] } : Stacks T A) =
      { S with R := Function.update S.R dst output } := by
    congr 1
    funext r
    by_cases ht : r = producer 34
    · subst r; simp [hdst.symm, hlocalBlank]
    · by_cases hd : r = dst <;> simp [D, C, ht, hd, hdst]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * ((n - 3 * w) * (2 * (Li + Lk) + 2)) + 2)), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end
end IntegerMultBounds.MathlibTM2.Routing
