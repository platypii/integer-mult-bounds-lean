module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceFrameLoad

/-! Read one raw source choice, emit its profile frame, and clear loaded
coordinates. The complete raw record is retained in the rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def gatedSelectedSourceRecord (Li Lk i r : ℕ) (lo hi enabled : Bool) : List (Fin (A + 4)) :=
  binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator :: [bitSymbol lo, bitSymbol hi, bitSymbol enabled])

def gatedSelectedSourceCallProgram (rg : Fin 4 → Fin 13 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (gatedSelectedSourceFrameLoadProgram rg zr src saved index localOffset tmp dst)
    (.seq (bclear index) (bclear localOffset))

def gatedSelectedSourceCallBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk i k b r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((gatedSelectedSourceRecord Li Lk i r lo hi enabled).reverse ++ R saved)) dst
    (affineProfileFrames (Li + Lk) [(enabled, if enabled then i * k + b + r else 0)] ++ R dst)

theorem gatedSelectedSourceCallBank_clean (R : Fin T → List (Fin (A + 4)))
    (src saved index localOffset dst : Fin T) (hreg : [src, saved, index, localOffset, dst].Nodup)
    (Li Lk i k b r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4)))
    (hindex : R index = []) (hlocal : R localOffset = []) :
    let B := selectorRunLoaded R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r)
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)
    let G := activityProfileFrameBank (sourceTagDispatchBank B src saved lo hi (bitSymbol enabled :: rest))
      src saved dst (Li + Lk) (i * k + b + r) enabled rest
    Function.update (Function.update G index []) localOffset [] =
      gatedSelectedSourceCallBank R src saved dst Li Lk i k b r lo hi enabled rest := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hd : j = dst <;>
    by_cases hiJ : j = index <;> by_cases hlJ : j = localOffset <;>
    simp_all [activityProfileFrameBank, sourceTagDispatchBank, selectorRunLoaded,
      gatedSelectedSourceCallBank, gatedSelectedSourceRecord, List.reverse_append, List.append_assoc]

theorem gatedSelectedSourceCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (hz5 : ∀ j, zr j ≠ rg (sourceTagIndex lo hi) 5)
    (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (hzIndex : ∀ j, zr j ≠ index) (hzLocal : ∀ j, zr j ≠ localOffset)
    (enabled : Bool) (Lw Li Lk i k b r : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (gatedSelectedSourceFrameCost Lw Li Lk + 4) + (2 * Li + 2) + (2 * (Li + Lk) + 2) ∧
      Exec body (gatedSelectedSourceCallProgram rg zr src saved index localOffset tmp dst) (mk v S) steps
        (mk v' { S with R := gatedSelectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi enabled rest }) := by
  have hn := hreg
  regs_ne hn
  have hdi : dst ≠ index := by rw [← hindexReg (sourceTagIndex lo hi)]; exact hsep 0
  have hdl : dst ≠ localOffset := by rw [← hlocalReg (sourceTagIndex lo hi)]; exact hsep 3
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := gatedSelectedSourceFrameLoad_exec body rg lo hi hrg
    src saved index localOffset tmp dst hreg hsrc hsaved hindexReg hlocalReg hsep hdsrc hdsaved
    zr hzr hdst hz5 hsrcZr hsavedZr hzIndex hzLocal enabled Lw Li Lk i k b r hwidth hiFit hk hfit
    rest v S hraw hindex hlocal htmp hstride hbase hblank hwidthInput hunary hzeroScratch
  let B := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r)
    (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)
  let G : Stacks T A := { S with R := activityProfileFrameBank (sourceTagDispatchBank B src saved lo hi (bitSymbol enabled :: rest)) src saved dst (Li + Lk) (i * k + b + r) enabled rest }
  have hiG : G.R index = binSyms Li i := by
    simp [G, B, activityProfileFrameBank, sourceTagDispatchBank, selectorRunLoaded, hdi.symm,
      ‹src ≠ index›.symm, ‹saved ≠ index›.symm, ‹index ≠ localOffset›]
  obtain ⟨v₂, hu₂, _, hx₂⟩ := bclear_exec body index v₁ G
  let H : Stacks T A := { G with R := Function.update G.R index [] }
  have hlH : H.R localOffset = binSyms (Li + Lk) r := by
    simp [H, G, B, activityProfileFrameBank, sourceTagDispatchBank, selectorRunLoaded, hdl.symm, ‹index ≠ localOffset›.symm,
      ‹src ≠ localOffset›.symm, ‹saved ≠ localOffset›.symm]
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body localOffset v₂ H
  have hf : Function.update H.R localOffset [] = gatedSelectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi enabled rest :=
    gatedSelectedSourceCallBank_clean S.R src saved index localOffset dst (by regs_nodup)
      Li Lk i k b r lo hi enabled rest hindex hlocal

  rw [hiG, length_binSyms] at hx₂
  rw [hf, hlH, length_binSyms] at hx₃
  exact ⟨v₃, m₁ + ((2 * Li + 2) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
