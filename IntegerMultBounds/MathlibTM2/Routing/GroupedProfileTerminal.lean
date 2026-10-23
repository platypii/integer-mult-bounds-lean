module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedSourceProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileTerminal
public import IntegerMultBounds.MathlibTM2.Routing.SparseTerminalCoordinateEmit
public import IntegerMultBounds.MathlibTM2.Routing.SparsePatternComplete

/-! Profiles with strictly positive physical positions need a zero selector at
the mirrored terminal coordinate. Emit that frame first, then prepend the live grouped
profile's generated coordinates, restoring every tape except the output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m N : ℕ} {P U : Type}

def groupedProfileTerminalProgram (rg : GroupedProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (sparseTerminalCoordinateProgram (rg (.coordinate .last)) (rg (.coordinate (.arithmetic .dst))) (rg (.coordinate .one)) (rg (.coordinate .selector))
    (rg (.coordinate .gap)) (rg (.coordinate .dst)) (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))) (rg (.coordinate (.arithmetic .tz))) (rg (.coordinate .gap)))
    (groupedProfileGenerateProgram rg saved)

theorem groupedProfileTerminal_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls index g k b N : ℕ) (src : Fin m → Option (Fin W))
    (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk)) (hpositive : 0 < N)
    (hi : index + m ≤ 2 ^ Li)
    (hpos : ∀ j : Fin m, 0 < (index + j.val) / g * k + ((index + j.val) % g + b) ∧ (index + j.val) / g * k + ((index + j.val) % g + b) < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li index)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k) (hoffset : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (22 * (Li + Lk) + 12 * Ls + 37) +
        (m * (groupedProfileCallCost Li Lg Lk Ls + 2) + 2 * (m * (Ls + 3)) + 16 * Li + 20) ∧
      Exec body (groupedProfileTerminalProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg (.coordinate .dst)) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
            (sparseCoordinateClose N (sparsePatternCoordinates (N := N)
              (fun j => (index + j) / g * k + ((index + j) % g + b)) src))) ++ S.R (rg (.coordinate .dst))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := sparseTerminalCoordinate_exec body
    (rg (.coordinate .last)) (rg (.coordinate (.arithmetic .dst))) (rg (.coordinate .one)) (rg (.coordinate .selector)) (rg (.coordinate .gap)) (rg (.coordinate .dst)) (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))) (rg (.coordinate (.arithmetic .tz))) (rg (.coordinate .gap))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (Li + Lk) Ls N hN hpositive v S hlast (hblank _ (by simp [groupedProfileLive]))
    (by rw [hone, length_binSyms])
    (hblank _ (by simp [groupedProfileLive])) (hblank _ (by simp [groupedProfileLive])) (hblank _ (by simp [groupedProfileLive]))
    (hblank _ (by simp [groupedProfileLive])) (hblank _ (by simp [groupedProfileLive]))
  let terminal : List (Fin (A + 4)) := binSyms (Li + Lk) (N - 1) ++ separator :: (binSyms Ls 0 ++ [separator])
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg (.coordinate .dst)) (terminal ++ S.R (rg (.coordinate .dst))) }
  have hkeep (r : GroupedProfileReg) (hd : r ≠ (.coordinate .dst)) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, hrg.eq_iff, hd]
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := groupedSourceProfileGenerate_exec body rg hrg saved hsep
    Li Lg Lk Ls index g k b N src hg hgpositive hk hwidth hN hi (fun j => (hpos j).2) hW v₁ S₁
    ((hkeep .src (by decide)).trans hsrc) ((hkeep .archive (by decide)).trans harchive)
    ((hkeep (.coordinate (.arithmetic .index)) (by decide)).trans hindex)
    ((hkeep (.coordinate (.arithmetic .group)) (by decide)).trans hgroup) ((hkeep (.coordinate (.arithmetic .stride)) (by decide)).trans hstride)
    ((hkeep (.coordinate (.arithmetic .base)) (by decide)).trans hoffset) ((hkeep (.coordinate .last) (by decide)).trans hlast)
    ((hkeep (.coordinate .one) (by decide)).trans hone)
    (by simp [S₁, hsep, hsaved])
    (by
      intro r hr
      rw [hkeep r (by intro he; apply hr; simp [groupedProfileLive, he])]
      exact hblank r hr)
  have hout : sparseCoordinateFrames (A := A) (Li + Lk) Ls (sparseCoordinateValues
      (sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => (index + j) / g * k + ((index + j) % g + b)) src))) =
      sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (index + j) / g * k + ((index + j) % g + b)) src)) ++ terminal := by
    rw [sparseCoordinateClose_positive _ src hpos]
    simp [sparseCoordinateValues, sparseCoordinateFrames_append, sparseCoordinateFrames, terminal]
  have hf : Function.update S₁.R (rg (.coordinate .dst))
      (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparsePatternCoordinates (N := N) (fun j => (index + j) / g * k + ((index + j) % g + b)) src)) ++ S₁.R (rg (.coordinate .dst))) =
      Function.update S.R (rg (.coordinate .dst)) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => (index + j) / g * k + ((index + j) % g + b)) src))) ++ S.R (rg (.coordinate .dst))) := by
    rw [hout]
    simp [S₁, List.append_assoc, Function.update_idem]
  rw [hf] at he₂
  refine ⟨v₂, (22 * (Li + Lk) + 12 * Ls + 37) + n₂, hu₂.trans hu₁, by omega, ?_⟩
  dsimp only [S₁, terminal] at he₂
  simp only [List.append_assoc, List.cons_append, List.nil_append] at he₂
  have he := Exec.seq he₁ he₂
  simpa only [groupedProfileTerminalProgram] using he

end IntegerMultBounds.MathlibTM2.Routing
