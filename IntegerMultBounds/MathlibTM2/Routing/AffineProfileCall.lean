module

public import IntegerMultBounds.MathlibTM2.Routing.AffineOptionalCoordinate
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! One profile iteration loads an activity/source pair, computes the slot from
an internal index, emits its mirrored coordinate, erases the loaded operands and
increments the index. The input is archived for later exact restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive AffineProfileReg where
  | src | archive | activity | wire | loadTmp | index | stride | product | offset
  | pos | muls | mult | last | one | selector | gap | dst | tx | ty | tz
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def affineProfileCallProgram (rg : AffineProfileReg → Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram (rg .src) (rg .archive) (rg .activity) (rg .wire) (rg .loadTmp))
    (.seq (affineOptionalCoordinateProgram (rg .activity) (rg .index) (rg .stride) (rg .product)
      (rg .offset) (rg .pos) (rg .muls) (rg .mult) (rg .last) (rg .wire) (rg .one)
      (rg .selector) (rg .gap) (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap))
      (.seq (metadataClean [rg .activity, rg .wire]) (countIter (rg .index) (rg .tx) (rg .gap))))

def affineProfileCallBank (R : Fin T → List (Fin (A + 4))) (rg : AffineProfileReg → Fin T)
    (Li Lk Ls i k o N q : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R (rg .src) rest)
    (rg .archive) ((binSyms 1 enabled.toNat ++ separator :: (binSyms Ls q ++ [separator])).reverse ++ R (rg .archive)))
    (rg .dst) (binSyms (Li + Lk) (N - 1 - (i * k + o)) ++ separator ::
      (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: R (rg .dst))))
    (rg .index) (binSyms Li (i + 1))

def affineProfileCallCost (Li Lk Ls : ℕ) :=
  Li * (12 * (Li + Lk) + 20) + 44 * (Li + Lk) + 22 * Ls + 4 * Li + 101

theorem affineProfileCall_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lk Ls i k o N q : ℕ) (enabled : Bool)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (hpos : i * k + o < N) (hq : q + 1 < 2 ^ Ls)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = binSyms 1 enabled.toNat ++ separator :: (binSyms Ls q ++ separator :: rest))
    (hindex : S.R (rg .index) = binSyms Li i) (hstride : S.R (rg .stride) = binSyms Lk k)
    (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ affineProfileCallCost Li Lk Ls ∧
      Exec body (affineProfileCallProgram rg) (mk v S) steps
        (mk v' { S with R := affineProfileCallBank S.R rg Li Lk Ls i k o N q enabled rest }) := by
  have hb (r : AffineProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive) (hi : r ≠ .index)
      (hk : r ≠ .stride) (ho : r ≠ .offset) (hl : r ≠ .last) (h1 : r ≠ .one) (hd : r ≠ .dst) :=
    hblank r hs ha hi hk ho hl h1 hd
  obtain ⟨v₁, hu₁, he₁⟩ := selectorRunLoad_exec body (rg .src) (rg .archive) (rg .activity) (rg .wire) (rg .loadTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) 1 Ls enabled.toNat q rest v S hsrc
    (by apply hb <;> decide) (by apply hb <;> decide) (by apply hb <;> decide)
  let S₁ : Stacks T A := { S with R := selectorRunLoaded S.R (rg .src) (rg .archive) (rg .activity) (rg .wire) (binSyms 1 enabled.toNat) (binSyms Ls q) rest }
  have hkeep (r : AffineProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive)
      (he : r ≠ .activity) (hw : r ≠ .wire) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, selectorRunLoaded, hrg.eq_iff, hs, ha, he, hw]
  have hblank₁ (r : AffineProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive) (he : r ≠ .activity)
      (hw : r ≠ .wire) (hi : r ≠ .index) (hk : r ≠ .stride) (ho : r ≠ .offset)
      (hl : r ≠ .last) (h1 : r ≠ .one) (hd : r ≠ .dst) : S₁.R (rg r) = [] :=
    (hkeep r hs ha he hw).trans (hb r hs ha hi hk ho hl h1 hd)
  have hbit : (binSyms 1 enabled.toNat : List (Fin (A + 4))) = [bitSymbol enabled] := by
    cases enabled <;> rfl
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := affineOptionalCoordinate_exec body
    (rg .activity) (rg .index) (rg .stride) (rg .product) (rg .offset) (rg .pos) (rg .muls) (rg .mult)
    (rg .last) (rg .wire) (rg .one) (rg .selector) (rg .gap) (rg .dst) (rg .tx) (rg .ty) (rg .tz) (rg .gap)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff])
    (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    enabled [] Li Lk Ls i k o N q hi hk hN hpos hq v₁ S₁
    ((hkeep .index (by decide) (by decide) (by decide) (by decide)).trans hindex)
    ((hkeep .stride (by decide) (by decide) (by decide) (by decide)).trans hstride)
    ((hkeep .offset (by decide) (by decide) (by decide) (by decide)).trans hoffset)
    ((hkeep .last (by decide) (by decide) (by decide) (by decide)).trans hlast)
    (by simp [S₁, selectorRunLoaded])
    ((hkeep .one (by decide) (by decide) (by decide) (by decide)).trans hone)
    (by simp [S₁, selectorRunLoaded, hrg.eq_iff, hbit])
    (by apply hblank₁ <;> decide) (by apply hblank₁ <;> decide)
    (by apply hblank₁ <;> decide) (by apply hblank₁ <;> decide)
    (by apply hblank₁ <;> decide) (by apply hblank₁ <;> decide)
    (by apply hblank₁ <;> decide) (by apply hblank₁ <;> decide) (by apply hblank₁ <;> decide)
  rw [hkeep .dst (by decide) (by decide) (by decide) (by decide)] at he₂
  let out := binSyms (Li + Lk) (N - 1 - (i * k + o)) ++ separator ::
    (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: S.R (rg .dst))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) out }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body [rg .activity, rg .wire]
    (by simp [hrg.eq_iff]) v₂ S₂
  have hc : metadataCleanCost S₂.R [rg .activity, rg .wire] = 2 * Ls + 7 := by
    simp [metadataCleanCost, S₂, S₁, selectorRunLoaded, hrg.eq_iff]; omega
  rw [hc] at he₃
  let S₃ : Stacks T A := { S₂ with R := metadataCleared S₂.R [rg .activity, rg .wire] }
  obtain ⟨v₄, hu₄, he₄⟩ := countIter_exec body (c := rg .index) (tmp := rg .tx)
    (by simp [hrg.eq_iff]) (rg .gap) (W := Li) (j := i) v₃ S₃
    (by simp [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, hrg.eq_iff, hindex])
    (by simpa [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, hrg.eq_iff] using
      hb .tx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hf : Function.update S₃.R (rg .index) (binSyms Li (i + 1)) =
      affineProfileCallBank S.R rg Li Lk Ls i k o N q enabled rest := by
    funext j
    by_cases ha : j = rg .activity
    · subst j; simp [S₃, metadataCleared, affineProfileCallBank, hrg.eq_iff, hblank]
    · by_cases hw : j = rg .wire
      · subst j; simp [S₃, metadataCleared, affineProfileCallBank, hrg.eq_iff, hblank]
      · by_cases hi : j = rg .index <;> by_cases hd : j = rg .dst <;>
          by_cases hs : j = rg .src <;> by_cases har : j = rg .archive <;>
          simp_all [S₃, metadataCleared, S₂, S₁, selectorRunLoaded, affineProfileCallBank, out, hrg.eq_iff]
  rw [hf] at he₄
  exact ⟨v₄, (4 * 1 + 4 * Ls + 12) + (n₂ + ((2 * Ls + 7) + (4 * Li + 5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by dsimp only [affineProfileCallCost]; omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩

end IntegerMultBounds.MathlibTM2.Routing
