module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.SparseTerminalCoordinateEmit
public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternComplete

/-! Profiles with strictly positive physical positions need a zero selector at
the mirrored terminal coordinate. Emit that frame first, then prepend the live
profile's generated coordinates, restoring every tape except the output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m N : ℕ} {P U : Type}

theorem sparseCoordinateClose_positive (pos : ℕ → ℕ) (src : Fin m → Option (Fin W))
    (hpos : ∀ j : Fin m, 0 < pos j.val ∧ pos j.val < N) :
    sparseCoordinateClose N (sparsePatternCoordinates (N := N) pos src) =
      sparsePatternCoordinates (N := N) pos src ++ [(N - 1, 0)] := by
  unfold sparseCoordinateClose
  split
  · rename_i ht
    obtain ⟨q, hq⟩ := ht
    simp only [sparsePatternCoordinates, List.mem_reverse, List.mem_ofFn] at hq
    obtain ⟨j, hj⟩ := hq
    have hx := congrArg Prod.fst hj
    have hp := hpos j
    simp only at hx
    omega
  · rfl

def affineProfileTerminalProgram (rg : AffineProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (sparseTerminalCoordinateProgram (rg .last) (rg .pos) (rg .one) (rg .selector)
    (rg .gap) (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap))
    (affineProfileGenerateProgram rg saved)

theorem affineProfileTerminal_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls index k o N : ℕ) (src : Fin m → Option (Fin W))
    (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk)) (hpositive : 0 < N)
    (hi : index + m ≤ 2 ^ Li)
    (hpos : ∀ j : Fin m, 0 < (index + j.val) * k + o ∧ (index + j.val) * k + o < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li index)
    (hstride : S.R (rg .stride) = binSyms Lk k) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (22 * (Li + Lk) + 12 * Ls + 37) +
        (m * (affineProfileCallCost Li Lk Ls + 2) + 2 * (m * (Ls + 3)) + 16 * Li + 20) ∧
      Exec body (affineProfileTerminalProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
            (sparseCoordinateClose N (sparsePatternCoordinates (N := N)
              (fun j => (index + j) * k + o) src))) ++ S.R (rg .dst)) }) := by
  have hb (r : AffineProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive) (hi : r ≠ .index)
      (hk : r ≠ .stride) (ho : r ≠ .offset) (hl : r ≠ .last) (h1 : r ≠ .one) (hd : r ≠ .dst) :=
    hblank r hs ha hi hk ho hl h1 hd
  obtain ⟨v₁, hu₁, he₁⟩ := sparseTerminalCoordinate_exec body
    (rg .last) (rg .pos) (rg .one) (rg .selector) (rg .gap) (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (Li + Lk) Ls N hN hpositive v S hlast (by apply hb <;> decide)
    (by rw [hone, length_binSyms])
    (by apply hb <;> decide) (by apply hb <;> decide) (by apply hb <;> decide)
    (by apply hb <;> decide) (by apply hb <;> decide)
  let terminal : List (Fin (A + 4)) := binSyms (Li + Lk) (N - 1) ++ separator :: (binSyms Ls 0 ++ [separator])
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .dst) (terminal ++ S.R (rg .dst)) }
  have hkeep (r : AffineProfileReg) (hd : r ≠ .dst) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, hrg.eq_iff, hd]
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := affineSourceProfileGenerate_exec body rg hrg saved hsep
    Li Lk Ls index k o N src hk hN hi (fun j => (hpos j).2) hW v₁ S₁
    ((hkeep .src (by decide)).trans hsrc) ((hkeep .archive (by decide)).trans harchive)
    ((hkeep .index (by decide)).trans hindex) ((hkeep .stride (by decide)).trans hstride)
    ((hkeep .offset (by decide)).trans hoffset) ((hkeep .last (by decide)).trans hlast)
    ((hkeep .one (by decide)).trans hone)
    (by simp [S₁, hsep, hsaved])
    (by intro r hs ha hi hk ho hl h1 hd; rw [hkeep r hd]; exact hblank r hs ha hi hk ho hl h1 hd)
  have hout : sparseCoordinateFrames (A := A) (Li + Lk) Ls (sparseCoordinateValues
      (sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => (index + j) * k + o) src))) =
      sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (index + j) * k + o) src)) ++ terminal := by
    rw [sparseCoordinateClose_positive _ src hpos]
    simp [sparseCoordinateValues, sparseCoordinateFrames_append, sparseCoordinateFrames, terminal]
  have hf : Function.update S₁.R (rg .dst)
      (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (index + j) * k + o) src)) ++ S₁.R (rg .dst)) =
      Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => (index + j) * k + o) src))) ++ S.R (rg .dst)) := by
    rw [hout]
    simp [S₁, List.append_assoc, Function.update_idem]
  rw [hf] at he₂
  refine ⟨v₂, (22 * (Li + Lk) + 12 * Ls + 37) + n₂, hu₂.trans hu₁, by omega, ?_⟩
  dsimp only [S₁, terminal] at he₂
  simp only [List.append_assoc, List.cons_append, List.nil_append] at he₂
  have he := Exec.seq he₁ he₂
  simpa only [affineProfileTerminalProgram] using he

end IntegerMultBounds.MathlibTM2.Routing
