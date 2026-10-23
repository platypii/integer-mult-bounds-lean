module

public import IntegerMultBounds.MathlibTM2.Routing.SharedSelectedSourceCall
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates

/-! Archive one raw source record and accumulate its emitted frame in reverse.
The temporary frame and loaded coordinate registers return to blank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sharedSelectedSourceReverseProgram (rg : Fin 4 → Fin 13 → Fin T)
    (src saved index localOffset tmp dst accum : Fin T) : Pr P T Q A U :=
  .seq (sharedSelectedSourceCallProgram rg src saved index localOffset tmp dst) (moveR dst accum id)

def sharedSelectedSourceReverseBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk i k b r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((gatedSelectedSourceRecord Li Lk i r lo hi enabled).reverse ++ R saved)) accum
    ((affineProfileFrames (Li + Lk) [(true, i * k + b + r)]).reverse ++ R accum)

theorem sharedSelectedSourceReverse_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (accum : Fin T) (hasrc : accum ≠ src) (hasaved : accum ≠ saved) (hadst : accum ≠ dst)
    (Li Lk i k b r : ℕ) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)))
    (houtput : S.R dst = [])
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (selectedSourceFrameCost Li Lk + 4) + (2 * Li + 2) + (2 * (Li + Lk) + 2) + 1 + (2 * (Li + Lk + 3) + 2) ∧
      Exec body (sharedSelectedSourceReverseProgram rg src saved index localOffset tmp dst accum) (mk v S) steps
        (mk v' { S with R := sharedSelectedSourceReverseBank S.R src saved accum Li Lk i k b r lo hi enabled rest }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := sharedSelectedSourceCall_exec body rg lo hi hrg
    src saved index localOffset tmp dst hreg hsrc hsaved hindexReg hlocalReg hsep hdsrc hdsaved
    Li Lk i k b r hiFit hk hfit enabled rest v S hraw hindex hlocal htmp hstride hbase hblank
  let G : Stacks T A := { S with R := sharedSelectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi enabled rest }
  let word := affineProfileFrames (A := A) (Li + Lk) [(true, i * k + b + r)]
  have hf : G.R dst = word := by simp [G, sharedSelectedSourceCallBank, word, houtput]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) dst accum hadst.symm id v₁ G
  have hbank : movedR G.R dst accum id (G.R dst) = sharedSelectedSourceReverseBank S.R src saved accum Li Lk i k b r lo hi enabled rest := by
    funext j
    by_cases hj : j = dst
    · subst j
      simp [movedR, sharedSelectedSourceReverseBank, hadst.symm, hdsrc, hdsaved, houtput]
    · by_cases ha : j = accum
      · subst j
        simp [movedR, G, sharedSelectedSourceCallBank, sharedSelectedSourceReverseBank, hasrc, hasaved, hadst, houtput]
      · simp [movedR, G, sharedSelectedSourceCallBank, sharedSelectedSourceReverseBank, Function.update_apply, hj, ha]
  have hlen : word.length = Li + Lk + 3 := by simp [word, affineProfileFrames]; omega
  rw [hbank, hf, hlen] at hx₂
  exact ⟨v₂, m₁ + (2 * (Li + Lk + 3) + 2), hu₂.trans hu₁, Nat.add_le_add_right hm₁ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
