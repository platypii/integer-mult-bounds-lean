module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # Execute block-count preparation with complete bank restoration -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpBlockCountSetup (rg : TblR 10 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpBlockCount)
    (.seq (toUnary (rg (.v 4)) dst (rg (.z 0)) (rg (.z 1)) (rg (.z 2)))
      (tblCompile rg tblChirpControlClear))

/-- Compute and convert the block count, then restore all six owned binary words. -/
theorem chirpBlockCountSetup_exec (hrg : Function.Injective rg) (dst : Fin T)
    (hout : ∀ b, rg b ≠ dst) {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (t m : ℕ) (ht : st.val 1 = t) (hm : st.val 2 = m) (ht0 : 0 < t)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧
      k ≤ 11 * tblC W e + W * (4 * chirpBlockCount t m + 11) + 2 * chirpBlockCount t m + 6 ∧
      Exec body (chirpBlockCountSetup rg dst) (mk v S) k
        (mk v' { S with R := Function.update S.R dst (List.replicate (chirpBlockCount t m) tick ++ S.R dst) }) := by
  classical
  obtain ⟨st₁, ⟨hv₁, hf₁, ha₁, hfit₁⟩, hargs⟩ :=
    (tblChirpBlockCount_do (e := e) st t m ht hm ht0 hfit).host (body := body) hrg wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, k₁, hu₁, hk₁, he₁, hb₁, hfr₁⟩ := hargs v S hS
  have hreg : [rg (.v 4), dst, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hout, Ne.symm (hout (.z 0)),
      Ne.symm (hout (.z 1)), Ne.symm (hout (.z 2))]
  obtain ⟨v₂, k₂, hu₂, hk₂, he₂⟩ := toUnary_exec body hreg (by simpa only [hv₁] using hfit₁ 4) v₁ S₁
    (by simpa only [tblRho_v, hv₁] using hb₁ (.v 4))
    (by simpa only [tblRho_z] using hb₁ (.z 0))
    (by simpa only [tblRho_z] using hb₁ (.z 1))
    (by simpa only [tblRho_z] using hb₁ (.z 2))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (List.replicate (chirpBlockCount t m) tick ++ S₁.R dst) }
  have hb₂ : tblHolds rg S₂ (tblRho W wl nl st₁) := by
    intro b
    simpa only [S₂, Function.update_of_ne (hout b)] using hb₁ b
  obtain ⟨st₃, ⟨hv₃, ha₃⟩, hclear⟩ :=
    (tblChirpControlClear_frame_do (W := W) (e := e) st st₁ hf₁ hzero).host
      (body := body) hrg wl nl hwl hnl heW hfit₁
  have hst₃ : st₃ = st := by
    have ha : st₃.acc = st.acc := ha₃.trans ha₁
    cases st₃; cases st
    simp_all only
  subst st₃
  obtain ⟨v₃, S₃, k₃, hu₃, hk₃, he₃, hb₃, hfr₃⟩ := hclear v₂ S₂ hb₂
  refine ⟨v₃, k₁ + (k₂ + k₃), hu₃.trans (hu₂.trans hu₁), by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · exact hfr₃.1.trans hfr₁.1
  · exact hfr₃.2.1.trans hfr₁.2.1
  · exact hfr₃.2.2.1.trans hfr₁.2.2.1
  funext k
  by_cases hkd : k = dst
  · subst k
    rw [hfr₃.2.2.2 dst hout]
    simp only [S₂, Function.update_self, hfr₁.2.2.2 dst hout]
  by_cases hbank : ∃ b, rg b = k
  · obtain ⟨b, rfl⟩ := hbank
    simpa only [Function.update_of_ne (hout b)] using (hb₃ b).trans (hS b).symm
  · have hoff : ∀ b, rg b ≠ k := by simpa using hbank
    rw [hfr₃.2.2.2 k hoff]
    simpa only [S₂, Function.update_of_ne hkd] using hfr₁.2.2.2 k hoff

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
