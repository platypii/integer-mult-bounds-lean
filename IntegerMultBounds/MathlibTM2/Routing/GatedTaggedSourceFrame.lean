module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.SourceTagDispatch

/-! Raw two-bit source tags select a region-base register for source-address
arithmetic. Tag bits are archived; coordinate operands and scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def gatedTaggedSourceFrameProgram (rg : Fin 4 → Fin 13 → Fin T) (zr : BinaryZeroReg → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  sourceTagDispatchProgram src saved (fun tag => gatedSelectedSourceFrameProgram (rg tag) zr src saved dst)

theorem gatedTaggedSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved dst : Fin T) (hss : src ≠ saved)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (hz5 : ∀ j, zr j ≠ rg (sourceTagIndex lo hi) 5)
    (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (enabled : Bool) (Lw Li Lk i k b r : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (htag : S.R src = bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)
    (hindex : S.R (rg (sourceTagIndex lo hi) 0) = binSyms Li i)
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hlocal : S.R (rg (sourceTagIndex lo hi) 3) = binSyms (Li + Lk) r)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ gatedSelectedSourceFrameCost Lw Li Lk + 4 ∧
      Exec body (gatedTaggedSourceFrameProgram rg zr src saved dst) (mk v S) steps
        (mk v' { S with R := activityProfileFrameBank (sourceTagDispatchBank S.R src saved lo hi (bitSymbol enabled :: rest)) src saved dst (Li + Lk) (i * k + b + r) enabled rest }) := by
  let B : Stacks T A := { S with R := sourceTagDispatchBank S.R src saved lo hi (bitSymbol enabled :: rest) }
  let u := sourceTagDispatchState v hi
  have hkeep (j : Fin 13) : B.R (rg (sourceTagIndex lo hi) j) = S.R (rg (sourceTagIndex lo hi) j) := by
    simp [B, sourceTagDispatchBank, (hsrc j).symm, (hsaved j).symm]
  have hzkeep (j : BinaryZeroReg) : B.R (zr j) = S.R (zr j) := by
    simp [B, sourceTagDispatchBank, (hsrcZr j).symm, (hsavedZr j).symm]
  obtain ⟨v', m, hu, hm, hx⟩ := gatedSelectedSourceFrame_exec body (rg (sourceTagIndex lo hi)) hrg dst hsep
    zr hzr hdst src saved hss hsrc hsaved hdsrc hdsaved hz5 hsrcZr hsavedZr enabled rest
    Lw Li Lk i k b r hwidth hiFit hk hfit u B
    (by simp [B, sourceTagDispatchBank, hss])
    ((hkeep 0).trans hindex) ((hkeep 1).trans hstride) ((hkeep 2).trans hbase) ((hkeep 3).trans hlocal)
    (fun j h0 h1 h2 h3 => (hkeep j).trans (hblank j h0 h1 h2 h3))
    ((hzkeep .width).trans hwidthInput) ((hzkeep .unary).trans hunary)
    (fun j => (hzkeep (.scratch j)).trans (hzeroScratch j))
  exact ⟨v', m + 4, hu, by omega,
    sourceTagDispatch_exec body src saved hss _ lo hi (bitSymbol enabled :: rest) v S htag m v' _ hx⟩

end IntegerMultBounds.MathlibTM2.Routing
