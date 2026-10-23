module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceFrameLoad

/-! Read one raw source choice, emit its profile frame, and clear loaded
coordinates. The complete raw record is retained in the rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def selectedSourceRecord (Li Lk i r : ℕ) (lo hi : Bool) : List (Fin (A + 4)) :=
  binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator :: [bitSymbol lo, bitSymbol hi])

def selectedSourceCallProgram (rg : Fin 4 → Fin 13 → Fin T)
    (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (selectedSourceFrameLoadProgram rg src saved index localOffset tmp dst)
    (.seq (bclear index) (bclear localOffset))

def selectedSourceCallBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk i k b r : ℕ) (lo hi : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((selectedSourceRecord Li Lk i r lo hi).reverse ++ R saved)) dst
    (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ R dst)

theorem selectedSourceCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (Li Lk i k b r : ℕ) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (selectedSourceFrameCost Li Lk + 4) + (2 * Li + 2) + (2 * (Li + Lk) + 2) ∧
      Exec body (selectedSourceCallProgram rg src saved index localOffset tmp dst) (mk v S) steps
        (mk v' { S with R := selectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi rest }) := by
  have hn := hreg
  regs_ne hn
  have hdi : dst ≠ index := by rw [← hindexReg (sourceTagIndex lo hi)]; exact hsep 0
  have hdl : dst ≠ localOffset := by rw [← hlocalReg (sourceTagIndex lo hi)]; exact hsep 3
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := selectedSourceFrameLoad_exec body rg lo hi hrg
    src saved index localOffset tmp dst hreg hsrc hsaved hindexReg hlocalReg hsep hdsrc hdsaved
    Li Lk i k b r hiFit hk hfit rest v S hraw hindex hlocal htmp hstride hbase hblank
  let B := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r)
    (bitSymbol lo :: bitSymbol hi :: rest)
  let G : Stacks T A := { S with R := Function.update (sourceTagDispatchBank B src saved lo hi rest) dst (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ S.R dst) }
  have hiG : G.R index = binSyms Li i := by
    simp [G, B, sourceTagDispatchBank, selectorRunLoaded, hdi.symm,
      ‹src ≠ index›.symm, ‹saved ≠ index›.symm, ‹index ≠ localOffset›]
  obtain ⟨v₂, hu₂, _, hx₂⟩ := bclear_exec body index v₁ G
  let H : Stacks T A := { G with R := Function.update G.R index [] }
  have hlH : H.R localOffset = binSyms (Li + Lk) r := by
    simp [H, G, B, sourceTagDispatchBank, selectorRunLoaded, hdl.symm, ‹index ≠ localOffset›.symm,
      ‹src ≠ localOffset›.symm, ‹saved ≠ localOffset›.symm]
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body localOffset v₂ H
  have hf : Function.update H.R localOffset [] = selectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi rest := by
    funext j
    by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hd : j = dst <;>
      by_cases hiJ : j = index <;> by_cases hlJ : j = localOffset <;>
      simp_all [H, G, B, sourceTagDispatchBank, selectorRunLoaded, selectedSourceCallBank,
        selectedSourceRecord, List.reverse_append, List.append_assoc]
  rw [hiG, length_binSyms] at hx₂
  rw [hf, hlH, length_binSyms] at hx₃
  exact ⟨v₃, m₁ + ((2 * Li + 2) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
