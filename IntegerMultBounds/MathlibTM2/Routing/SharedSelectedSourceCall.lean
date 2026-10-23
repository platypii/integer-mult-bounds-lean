module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceCall
public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceCall

/-! Emit the always-active X frame from the same activity-bearing raw record
used for key generation. The activity bit is consumed and archived unchanged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sharedSelectedSourceCallProgram (rg : Fin 4 → Fin 13 → Fin T)
    (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (selectedSourceCallProgram rg src saved index localOffset tmp dst)
    (.act (sourceActivityArchive src saved))

def sharedSelectedSourceCallBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk i k b r : ℕ) (lo hi enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((gatedSelectedSourceRecord Li Lk i r lo hi enabled).reverse ++ R saved)) dst
    (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ R dst)

theorem sharedSelectedSourceCall_exec (body : P → Pr P T Q A U)
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
    (enabled : Bool) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (selectedSourceFrameCost Li Lk + 4) + (2 * Li + 2) + (2 * (Li + Lk) + 2) + 1 ∧
      Exec body (sharedSelectedSourceCallProgram rg src saved index localOffset tmp dst) (mk v S) steps
        (mk v' { S with R := sharedSelectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi enabled rest }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := selectedSourceCall_exec body rg lo hi hrg
    src saved index localOffset tmp dst hreg hsrc hsaved hindexReg hlocalReg hsep hdsrc hdsaved
    Li Lk i k b r hiFit hk hfit (bitSymbol enabled :: rest) v S hraw hindex hlocal htmp hstride hbase hblank
  let G : Stacks T A := { S with R := selectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi (bitSymbol enabled :: rest) }
  let u := { v₁ with sym := some (bitSymbol enabled), flag := enabled }
  let H : Stacks T A := { S with R := sharedSelectedSourceCallBank S.R src saved dst Li Lk i k b r lo hi enabled rest }
  have hrawG : G.R src = bitSymbol enabled :: rest := by
    simp [G, selectedSourceCallBank, hdsrc.symm, ‹src ≠ saved›]
  have hbank : Function.update (Function.update G.R src rest) saved (bitSymbol enabled :: G.R saved) = H.R := by
    funext j
    by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hd : j = dst <;>
      simp_all [G, H, selectedSourceCallBank, sharedSelectedSourceCallBank,
        selectedSourceRecord, gatedSelectedSourceRecord, List.reverse_append, List.append_assoc]
  have hp : (sourceActivityArchive src saved : Act T Q A U).run (mk v₁ G) = mk u H := by
    simp [sourceActivityArchive, Action.run, update_rt, hrawG, u, ‹src ≠ saved›.symm, hbank]
    rfl
  exact ⟨u, m₁ + 1, hu₁, Nat.add_le_add_right hm₁ 1,
    Exec.seq hx₁ (hp ▸ Exec.act (body := body) _ (mk v₁ G))⟩

end IntegerMultBounds.MathlibTM2.Routing
