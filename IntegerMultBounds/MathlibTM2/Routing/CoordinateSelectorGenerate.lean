module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateCoverage
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedSelectorRuns
public import IntegerMultBounds.MathlibTM2.Routing.CompactDescriptorJob

/-! Generate compact gaps from absolute coordinates, expand them into dense
selector frames, and erase the intermediate compact stream. Only dense output
changes; original coordinates, cursor and all workspace are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W : ℕ} {P U : Type}

def coordinateSelectorProgram (coord : SparseCoordinateReg → Fin T) (saved : Fin T)
    (zero : BinaryZeroReg → Fin T) (rg : SelectorRunReg → Fin T) : Pr P T Q A U :=
  .seq (sparseCoordinateGenerateProgram coord saved)
    (.seq (generatedSelectorRunsProgram zero rg) (bclear (coord .dst)))

theorem sparseCoordinateFrames_length (L Ls : ℕ) (entries : List (ℕ × ℕ)) :
    (sparseCoordinateFrames (A := A) L Ls entries).length = entries.length * (L + Ls + 2) := by
  induction entries with
  | nil => simp [sparseCoordinateFrames]
  | cons pair rest ih =>
    cases pair
    simp only [sparseCoordinateFrames, List.length_append, List.length_cons, length_binSyms, ih, Nat.add_mul, Nat.one_mul]
    omega

def coordinateSelectorCost (Lw L Ls cursor : ℕ) (entries : List (ℕ × Fin (W + 1))) : ℕ :=
  let rs := (sparseCoordinateRuns cursor entries).reverse
  (entries.length * (32 * L + 12 * Ls + 54) +
    2 * (entries.length * (L + Ls + 2)) + 16 * L + 20) +
    ((Lw * (4 * Ls + 11) + 8 * Ls + 13) + selectorRunLoopCost L Ls rs +
      2 * (selectorRunFrames (A := 0) L Ls rs).length + 3 + (2 * (Ls + 1) + 2)) +
    (2 * (selectorRunFrames (A := 0) L Ls rs).length + 2)

/-- Generation and cleanup are linear in entries and total skipped coordinates. -/
theorem coordinateSelectorCost_eq (Lw L Ls cursor : ℕ)
    (entries : List (ℕ × Fin (W + 1))) :
    coordinateSelectorCost Lw L Ls cursor entries =
      entries.length * (55 * L + 30 * Ls + 105) +
        ((sparseCoordinateRuns cursor entries).map (fun run => run.gap)).sum *
          (4 * L + 6 * Ls + 21) +
        Lw * (4 * Ls + 11) + 16 * L + 10 * Ls + 43 := by
  simp only [coordinateSelectorCost, selectorRunLoopCost_eq,
    CompactDescriptorJob.selectorRunFrames_length, List.length_reverse,
    sparseCoordinateRuns_length, List.map_reverse, List.sum_reverse]
  ring

theorem coordinateSelectorCost_le (Lw L Ls cursor extent : ℕ)
    (entries : List (ℕ × Fin (W + 1)))
    (hr : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (hend : sparseCoordinateEnd cursor (sparseCoordinateValues entries) - cursor ≤ extent) :
    coordinateSelectorCost Lw L Ls cursor entries ≤
      entries.length * (55 * L + 30 * Ls + 105) + extent * (4 * L + 6 * Ls + 21) +
        Lw * (4 * Ls + 11) + 16 * L + 10 * Ls + 43 := by
  have hsum := sparseCoordinateRuns_gap_sum L cursor entries hr
  have hgap : ((sparseCoordinateRuns cursor entries).map (fun run => run.gap)).sum ≤
      extent := by omega
  have hprice := Nat.mul_le_mul_right (4 * L + 6 * Ls + 21) hgap
  rw [coordinateSelectorCost_eq]
  omega

theorem coordinateSelector_exec (body : P → Pr P T Q A U)
    (coord : SparseCoordinateReg → Fin T) (hcoord : Function.Injective coord)
    (saved : Fin T) (hsavedSep : ∀ r, saved ≠ coord r)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (rg : SelectorRunReg → Fin T) (hrg : Function.Injective rg)
    (hjoin : rg .src = coord .dst) (hblockReg : zero .dst = rg .block)
    (hzeroSep : ∀ r, zero r ≠ coord .dst)
    (hrunSep : ∀ r, r ≠ .src → rg r ≠ coord .dst)
    (Lw L Ls cursor : ℕ) (hLs : Ls < 2 ^ Lw)
    (entries : List (ℕ × Fin (W + 1)))
    (hready : SparseCoordinatesReady L cursor (sparseCoordinateValues entries))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (coord .src) = sparseCoordinateFrames L Ls (sparseCoordinateValues entries))
    (harchive : S.R (coord .archive) = []) (hcursor : S.R (coord .cursor) = binSyms L cursor)
    (hone : S.R (coord .one) = binSyms L 1) (hsaved : S.R saved = []) (hcompact : S.R (coord .dst) = [])
    (hcoordBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .cursor → r ≠ .one → r ≠ .dst → S.R (coord r) = [])
    (hwidth : S.R (zero .width) = binSyms Lw Ls) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hrArchive : S.R (rg .archive) = []) (hrBlock : S.R (rg .block) = [])
    (hrBlank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ coordinateSelectorCost Lw L Ls cursor entries ∧
      Exec body (coordinateSelectorProgram coord saved zero rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (descriptorSelectorFrames Ls (SparseSelectorRun.expand (sparseCoordinateRuns cursor entries)) ++ S.R (rg .dst)) }) := by
  unfold coordinateSelectorCost
  let rs := (sparseCoordinateRuns cursor entries).reverse
  obtain ⟨v₁, hu₁, he₁⟩ := sparseCoordinateGenerate_exec body coord hcoord saved hsavedSep L Ls cursor
    (sparseCoordinateValues entries) hready v S hsrc harchive hcursor hone hsaved hcoordBlank
  rw [hcompact, List.append_nil, sparseCoordinateOutput_runs] at he₁
  let compact := selectorRunFrames (A := A) L Ls rs
  let S₁ : Stacks T A := { S with R := Function.update S.R (coord .dst) compact }
  have hk (j : Fin T) (hj : j ≠ coord .dst) : S₁.R j = S.R j := Function.update_of_ne hj _ _
  have hfit : ∀ run ∈ rs, run.gap < 2 ^ L := by
    intro run hr
    exact sparseCoordinateRuns_fit L cursor entries hready run (by simpa [rs] using hr)
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := generatedSelectorRuns_exec body zero hzero rg hrg hblockReg Lw L Ls hLs rs hfit v₁ S₁
    ((hk _ (hzeroSep .width)).trans hwidth) ((hk _ (hzeroSep .unary)).trans hunary)
    (fun i => (hk _ (hzeroSep (.scratch i))).trans (hscratch i))
    (by simp [S₁, hjoin, compact])
    ((hk _ (hrunSep .archive (by decide))).trans hrArchive)
    ((hk _ (hrunSep .block (by decide))).trans hrBlock)
    (by intro r hs ha hb hd; rw [hk _ (hrunSep r hs)]; exact hrBlank r hs ha hb hd)
  have hd : S₁.R (rg .dst) = S.R (rg .dst) := hk _ (hrunSep .dst (by decide))
  rw [hd] at he₂
  simp only [rs, List.reverse_reverse] at he₂
  let out := descriptorSelectorFrames (A := A) Ls (SparseSelectorRun.expand (sparseCoordinateRuns cursor entries)) ++ S.R (rg .dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (coord .dst) v₂ S₂
  have hc : S₂.R (coord .dst) = compact := by simp [S₂, S₁, Ne.symm (hrunSep .dst (by decide))]
  have hf : Function.update S₂.R (coord .dst) [] = Function.update S.R (rg .dst) out := by
    funext j
    by_cases hc : j = coord .dst
    · subst j; simp [Ne.symm (hrunSep .dst (by decide)), hcompact]
    · by_cases hd : j = rg .dst
      · subst j; simp [S₂, S₁, hc]
      · simp [S₂, S₁, hc, hd]
  rw [hf, hc] at he₃
  have hlen : (sparseCoordinateValues entries).length = entries.length := by simp [sparseCoordinateValues]
  rw [hlen] at he₁
  refine ⟨v₃, (entries.length * (32 * L + 12 * Ls + 54) + 2 * (sparseCoordinateFrames (A := A) L Ls (sparseCoordinateValues entries)).length + 16 * L + 20) +
    (n₂ + (2 * compact.length + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  dsimp only [compact, rs]
  dsimp only [rs] at ht₂
  simp only [CompactDescriptorJob.selectorRunFrames_length, sparseCoordinateFrames_length, sparseCoordinateValues, List.length_map] at *
  omega

end IntegerMultBounds.MathlibTM2.Routing
