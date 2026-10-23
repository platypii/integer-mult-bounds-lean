module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlArgs
public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlEmit

/-! # Compute and emit a gathering-control packet on actual host tapes -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpControlNext (rg : TblR 10 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpControlStep)
    (chirpControlEmit (rg (.v 9)) dst (rg (.z 0)) (rg (.z 1)) (rg (.z 2)))

/-- No supplied advance values: compute the next centre and emit its exact unary packet. -/
theorem chirpControlNext_exec (hrg : Function.Injective rg) (dst : Fin T)
    (hdst : ∀ r, rg r ≠ dst) {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s t m w j : ℕ) (hready : ChirpControlReady st s t m w j)
    (hst : s ≤ t) (ht : 0 < t) (hk : (j + 1) * m < 2 ^ W)
    (hnum : s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (hfit : ∀ i, st.val i < 2 ^ W) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ (st' : TblSt 10 A) (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ),
      ChirpControlReady st' s t m w (j + 1) ∧ st'.acc = st.acc ∧
      (∀ i, st'.val i < 2 ^ W) ∧ v'.user = v.user ∧
      n ≤ 6 * tblC W e + W * (4 * (chirpAdvance s t m j * w) + 11) +
        2 * (chirpAdvance s t m j * w) + 7 ∧
      Exec body (chirpControlNext rg dst) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl st') ∧
      S'.R dst = blank :: (List.replicate (chirpAdvance s t m j * w) tick ++ S.R dst) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, k ≠ dst → (∀ r, rg r ≠ k) → S'.R k = S.R k) := by
  have hdo := tblChirpControlStep_do (e := e) st s t m w j hready hst ht hk hnum hwidth hfit
  obtain ⟨st', ⟨⟨hready', hd, ha⟩, hfit'⟩, hrun⟩ :=
    hdo.host (body := body) hrg wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hb₁, hf₁⟩ := hrun v S hS
  have hreg : [rg (.v 9), dst, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hdst, Ne.symm (hdst (.z 0)),
      Ne.symm (hdst (.z 1)), Ne.symm (hdst (.z 2))]
  have hword : S₁.R (rg (.v 9)) = binSyms W (chirpAdvance s t m j * w) := by
    simpa only [tblRho_v, hd] using hb₁ (.v 9)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpControlEmit_exec (body := body) hreg W
    (chirpAdvance s t m j * w) (by simpa only [hd] using hfit' 9) v₁ S₁ hword
    (by simpa only [tblRho_z] using hb₁ (.z 0))
    (by simpa only [tblRho_z] using hb₁ (.z 1))
    (by simpa only [tblRho_z] using hb₁ (.z 2))
  let S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (blank :: (List.replicate (chirpAdvance s t m j * w) tick ++ S₁.R dst))) }
  refine ⟨st', v₂, S₂, n₁ + n₂, hready', ha, hfit', hu₂.trans hu₁,
    by omega, Exec.seq he₁ he₂, ?_, ?_, hf₁.1, hf₁.2.1, hf₁.2.2.1, ?_⟩
  · intro r
    simpa only [S₂, Function.update_of_ne (hdst r)] using hb₁ r
  · simp only [S₂, Function.update_self, hf₁.2.2.2 dst hdst]
  · intro k hk hoff
    simpa only [S₂, Function.update_of_ne hk] using hf₁.2.2.2 k hoff

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
