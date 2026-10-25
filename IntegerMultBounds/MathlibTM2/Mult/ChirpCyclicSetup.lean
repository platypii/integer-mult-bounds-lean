module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicCounters
public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlCleanup

/-! # Generate the cyclic-source counters and restore the binary bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpCyclicSetup (rg : TblR 10 → Fin T) (dst : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpCyclicArgs)
    (.seq (tblUnaryCopies rg (chirpCyclicAssignments dst)) (tblCompile rg tblChirpControlClear))

/-- All five unary counts are computed from the retained dimension words. Every other stack,
including the full binary working bank, returns to its initial state. -/
theorem chirpCyclicSetup_exec (hrg : Function.Injective rg) (dst : Fin 5 → Fin T)
    (hout : ∀ i r, rg r ≠ dst i) {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s m w : ℕ) (hs : st.val 0 = s) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (hs0 : 0 < s) (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧
      k ≤ 25 * tblC W e + 6 * chirpCyclicCounterTotal s m w + 55 * W + 31 ∧
      Exec body (chirpCyclicSetup rg dst) (mk v S) k
        (mk v' { S with R := unaryCopiesR (chirpCyclicValues s m w) S.R (chirpCyclicAssignments dst) }) := by
  classical
  obtain ⟨st₁, ⟨hv₁, hf₁, ha₁, hfit₁⟩, hargs⟩ :=
    (tblChirpCyclicArgs_do (e := e) st s m w hs hm hw hs0 hsize hvolume hfit).host
      (body := body) hrg wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, k₁, hu₁, hk₁, he₁, hb₁, hfr₁⟩ := hargs v S hS
  have hpout : ∀ p ∈ chirpCyclicAssignments dst, ∀ r, rg r ≠ p.2 := by
    intro p hp
    obtain ⟨i, rfl⟩ := (chirpCyclicAssignments_mem dst p).mp hp
    exact hout i
  obtain ⟨v₂, k₂, hu₂, hk₂, he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl nl st₁ hfit₁
    (chirpCyclicAssignments dst) hpout v₁ S₁ hb₁
  let S₂ : Stacks T A := { S₁ with R := unaryCopiesR st₁.val S₁.R (chirpCyclicAssignments dst) }
  have hb₂ : tblHolds rg S₂ (tblRho W wl nl st₁) := by
    intro r
    change unaryCopiesR st₁.val S₁.R (chirpCyclicAssignments dst) (rg r) = _
    rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hpout p hp r).symm)]
    exact hb₁ r
  obtain ⟨st₃, ⟨hv₃, ha₃⟩, hclear⟩ :=
    (tblChirpControlClear_frame_do (W := W) (e := e) st st₁ hf₁ hzero).host
      (body := body) hrg wl nl hwl hnl heW hfit₁
  have hst₃ : st₃ = st := by
    have ha : st₃.acc = st.acc := ha₃.trans ha₁
    cases st₃; cases st
    simp_all only
  subst st₃
  obtain ⟨v₃, S₃, k₃, hu₃, hk₃, he₃, hb₃, hfr₃⟩ := hclear v₂ S₂ hb₂
  rw [chirpCyclicCounters_cost dst W s m w hs0 st₁.val hv₁] at hk₂
  refine ⟨v₃, k₁ + (k₂ + k₃), hu₃.trans (hu₂.trans hu₁), by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · exact hfr₃.1.trans hfr₁.1
  · exact hfr₃.2.1.trans hfr₁.2.1
  · exact hfr₃.2.2.1.trans hfr₁.2.2.1
  funext k
  by_cases hbank : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hbank
    change S₃.R (rg r) = unaryCopiesR (chirpCyclicValues s m w) S.R (chirpCyclicAssignments dst) (rg r)
    rw [unaryCopiesR_off _ _ _ _ (fun p hp => (hpout p hp r).symm)]
    exact (hb₃ r).trans (hS r).symm
  · have hoff : ∀ r, rg r ≠ k := by simpa using hbank
    rw [hfr₃.2.2.2 k hoff]
    change unaryCopiesR st₁.val S₁.R (chirpCyclicAssignments dst) k = _
    rw [unaryCopiesR_congr st₁.val (chirpCyclicValues s m w) S₁.R _
      (chirpCyclicAssignments_values dst s m w st₁.val hv₁)]
    exact unaryCopiesR_congr_base _ _ _ _ k
      (fun p hp => hfr₁.2.2.2 p.2 (hpout p hp)) (hfr₁.2.2.2 k hoff)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
