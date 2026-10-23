module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedOptionalCoordinate
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileLoop

/-! One streamed grouped-profile iteration generates its position, emits the
activity-selected coordinate, erases loaded operands and advances the index.
Only profile input/archive, generated output and the index change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive GroupedProfileReg where
  | coordinate (r : GroupedCoordinateReg)
  | src | archive | activity | loadTmp
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def groupedProfileCoordinate (rg : GroupedProfileReg → Fin T) (r : GroupedCoordinateReg) := rg (.coordinate r)

def groupedProfileLive : List GroupedProfileReg :=
  [.src, .archive, .coordinate (.arithmetic .index), .coordinate (.arithmetic .group),
    .coordinate (.arithmetic .stride), .coordinate (.arithmetic .base), .coordinate .last, .coordinate .one, .coordinate .dst]

def groupedProfileCallProgram (rg : GroupedProfileReg → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg .src) (rg .archive) (rg .activity) (rg (.coordinate .wire)) (rg .loadTmp))
    (.seq (groupedOptionalCoordinateProgram (rg .activity) (groupedProfileCoordinate rg))
      (.seq (metadataClean [rg .activity, rg (.coordinate .wire)])
        (countIter (rg (.coordinate (.arithmetic .index))) (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .divTmp))))))

def groupedProfileCallBank (R : Fin T → List (Fin (A + 4))) (rg : GroupedProfileReg → Fin T)
    (Li _Lg Lk Ls i g k b N q : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R (rg .src) rest)
    (rg .archive) ((binSyms 1 enabled.toNat ++ separator :: (binSyms Ls q ++ [separator])).reverse ++ R (rg .archive)))
    (rg (.coordinate .dst)) (binSyms (Li + Lk) (N - 1 - (i / g * k + (i % g + b))) ++ separator ::
      (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: R (rg (.coordinate .dst)))))
    (rg (.coordinate (.arithmetic .index))) (binSyms Li (i + 1))

def groupedProfileCallCost (Li Lg Lk Ls : ℕ) :=
  binaryGroupedPositionCost Li Lg Lk + 18 * (Li + Lk) + 22 * Ls + 4 * Li + 67

theorem groupedProfileCall_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls i g k b N q : ℕ) (enabled : Bool)
    (hi : i < 2 ^ Li) (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hpos : i / g * k + (i % g + b) < N) (hq : q + 1 < 2 ^ Ls)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = binSyms 1 enabled.toNat ++ separator :: (binSyms Ls q ++ separator :: rest))
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li i)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k)
    (hbase : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1))
    (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ groupedProfileCallCost Li Lg Lk Ls ∧
      Exec body (groupedProfileCallProgram rg) (mk v S) steps
        (mk v' { S with R := groupedProfileCallBank S.R rg Li Lg Lk Ls i g k b N q enabled rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg .src) (rg .archive) (rg .activity) (rg (.coordinate .wire)) (rg .loadTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) 1 Ls enabled.toNat q rest v S hsrc
    (hblank _ (by simp [groupedProfileLive])) (hblank _ (by simp [groupedProfileLive])) (hblank _ (by simp [groupedProfileLive]))
  let S₁ : Stacks T A := { S with R := selectorRunLoaded S.R (rg .src) (rg .archive) (rg .activity) (rg (.coordinate .wire)) (binSyms 1 enabled.toNat) (binSyms Ls q) rest }
  have hkeep (r : GroupedProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive)
      (he : r ≠ .activity) (hw : r ≠ .coordinate .wire) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, selectorRunLoaded, hrg.eq_iff, hs, ha, he, hw]
  have hcr : Function.Injective (groupedProfileCoordinate rg) :=
    fun _ _ h => GroupedProfileReg.coordinate.inj (hrg h)
  have hbit : (binSyms 1 enabled.toNat : List (Fin (A + 4))) = [bitSymbol enabled] := by cases enabled <;> rfl
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := groupedOptionalCoordinate_exec body (rg .activity) (groupedProfileCoordinate rg) hcr
    (by simp [groupedProfileCoordinate, hrg.eq_iff]) Li Lg Lk Ls i g k b N q enabled []
    hi hg hgpositive hk hwidth hN hpos hq v₁ S₁
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hindex)
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hgroup)
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hstride)
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hbase)
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hlast)
    (by simp [groupedProfileCoordinate, S₁, selectorRunLoaded])
    ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hone)
    (by simp [S₁, selectorRunLoaded, hrg.eq_iff, hbit])
    (by
      intro r hi hg hk hb hl hw h1 hd
      change S₁.R (rg (.coordinate r)) = []
      rw [hkeep _ (by simp) (by simp) (by simp) (by simpa using hw)]
      apply hblank
      simp [groupedProfileLive, hi, hg, hk, hb, hl, h1, hd])
  dsimp only [groupedProfileCoordinate] at he₂
  rw [hkeep _ (by decide) (by decide) (by decide) (by decide)] at he₂
  let out := binSyms (Li + Lk) (N - 1 - (i / g * k + (i % g + b))) ++ separator ::
    (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: S.R (rg (.coordinate .dst)))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg (.coordinate .dst)) out }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body [rg .activity, rg (.coordinate .wire)] (by simp [hrg.eq_iff]) v₂ S₂
  have hc : metadataCleanCost S₂.R [rg .activity, rg (.coordinate .wire)] = 2 * Ls + 7 := by
    simp [metadataCleanCost, S₂, S₁, selectorRunLoaded, hrg.eq_iff]; omega
  rw [hc] at he₃
  let S₃ : Stacks T A := { S₂ with R := metadataCleared S₂.R [rg .activity, rg (.coordinate .wire)] }
  obtain ⟨v₄, hu₄, he₄⟩ := countIter_exec body (c := rg (.coordinate (.arithmetic .index))) (tmp := rg (.coordinate (.arithmetic .tx)))
    (by simp [hrg.eq_iff]) (rg (.coordinate (.arithmetic .divTmp))) (W := Li) (j := i) v₃ S₃
    (by simp [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, hrg.eq_iff, hindex])
    (by simp [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, hrg.eq_iff, hblank, groupedProfileLive])
  have hf : Function.update S₃.R (rg (.coordinate (.arithmetic .index))) (binSyms Li (i + 1)) =
      groupedProfileCallBank S.R rg Li Lg Lk Ls i g k b N q enabled rest := by
    funext j
    by_cases ha : j = rg .activity
    · subst j; simp [S₃, metadataCleared, groupedProfileCallBank, hrg.eq_iff, hblank, groupedProfileLive]
    · by_cases hw : j = rg (.coordinate .wire)
      · subst j; simp [S₃, metadataCleared, groupedProfileCallBank, hrg.eq_iff, hblank, groupedProfileLive]
      · by_cases hi : j = rg (.coordinate (.arithmetic .index)) <;> by_cases hd : j = rg (.coordinate .dst) <;>
          by_cases hs : j = rg .src <;> by_cases har : j = rg .archive <;>
          simp_all [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, groupedProfileCallBank, out, hrg.eq_iff]
  rw [hf] at he₄
  exact ⟨v₄, (4 * 1 + 4 * Ls + 12) + (n₂ + ((2 * Ls + 7) + (4 * Li + 5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by dsimp only [groupedProfileCallCost]; omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩

end IntegerMultBounds.MathlibTM2.Routing
