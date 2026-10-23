module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawGather
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCountSetup

/-! # Raw-line gathering from binary dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def chirpGatherFromDimensions (rg : TblR 10 → Fin T) (r : ChirpRawReg → Fin T) : Pr P T Q A U :=
  .seq (chirpBlockCountSetup rg (r .count)) (.seq (chirpRawGather rg r) (uclear (r .count)))

def chirpGatherFromDimensionsCost (W e s t m w : ℕ) : ℕ :=
  let M := chirpBlockCount t m
  chirpRawGatherCost W e s t m w M + 11 * tblC W e + W * (4 * M + 11) + 4 * M + 8

/-- All counters, the cyclic extension and gathering controls are generated and erased.
Only the destination changes; the retained binary dimension bank and raw line are restored. -/
theorem chirpGatherFromDimensions_exec {rg : TblR 10 → Fin T} {r : ChirpRawReg → Fin T}
    (hrg : Function.Injective rg) (hr : Function.Injective r) (hsep : ∀ q b, rg b ≠ r q)
    {W e : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s t m w : ℕ)
    (hs : st.val 0 = s) (htval : st.val 1 = t) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (hs0 : 0 < s) (hst : s ≤ t) (ht : 0 < t) (hm0 : 0 < m)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (htm : t + m < 2 ^ W) (hproduct : s * (t + m) < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hsrc : S.R (r .raw) = cstream A w (chirpLine s u))
    (hclean : ∀ q, q ≠ .raw → q ≠ .dst → S.R (r q) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpGatherFromDimensionsCost W e s t m w ∧
      Exec body (chirpGatherFromDimensions rg r) (mk v S) n
        (mk v' { S with R := (Function.update S.R (r .dst)
          ((List.range (chirpBlockCount t m)).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R (r .dst))) }) := by
  let M := chirpBlockCount t m
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpBlockCountSetup_exec (body := body) hrg (r .count)
    (hsep .count) wl nl hwl hnl heW st t m htval hm ht hzero hfit v S hS
  let S₁ : Stacks T A := { S with R := Function.update S.R (r .count) (List.replicate M tick ++ S.R (r .count)) }
  have hc0 : S.R (r .count) = [] := hclean .count (by simp) (by simp)
  have hc₁ : S₁.R (r .count) = List.replicate M tick := by simp [S₁, hc0]
  have off₁ (k : Fin T) (hk : k ≠ r .count) : S₁.R k = S.R k := by simp [S₁, hk]
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := by
    intro b
    rw [off₁ _ (hsep .count b)]
    exact hS b
  have hMm := chirpBlockCount_mul_le t m
  have hstep (j : ℕ) (hj : j < M) : (j + 1) * m ≤ t + m :=
    (Nat.mul_le_mul_right m (Nat.succ_le_of_lt hj)).trans hMm
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpRawGather_exec (body := body) hrg hr hsep wl nl hwl hnl heW
    st s t m w M hs htval hm hw hs0 hst ht hsize hvolume
    (fun j hj => (hstep j hj).trans_lt htm)
    (fun j hj => (Nat.mul_le_mul_left s (hstep j hj)).trans_lt hproduct)
    ((Nat.mul_le_mul_right w (by omega : m ≤ s + 3 * m + 1)).trans_lt hvolume)
    hzero hfit u (fun j hj => chirpBlock_valid ht hm0 hj) v₁ S₁ hb₁
    (by rw [off₁ _ (hr.ne (by decide : ChirpRawReg.raw ≠ .count))]; exact hsrc)
    (by rw [hc₁, List.length_replicate]) (by
      intro q hqr hqd hqc
      rw [off₁ _ (hr.ne hqc)]
      exact hclean q hqr hqd)
  let rows := (List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (r .dst) (rows ++ S₁.R (r .dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (r .count) v₂ S₂
  have hc₂ : S₂.R (r .count) = List.replicate M tick := by
    simpa only [S₂, Function.update_of_ne (hr.ne (by decide : ChirpRawReg.count ≠ .dst))] using hc₁
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hc₂, List.length_replicate]
    change n₁ + (n₂ + (2 * M + 2)) ≤ chirpRawGatherCost W e s t m w M +
      11 * tblC W e + W * (4 * M + 11) + 4 * M + 8
    change n₁ ≤ 11 * tblC W e + W * (4 * M + 11) + 2 * M + 6 at hn₁
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hkc : k = r .count
    · subst k
      simp [S₂, S₁, hr.ne (by decide : ChirpRawReg.count ≠ .dst), hc0]
    by_cases hkd : k = r .dst
    · subst k
      simp [S₂, S₁, hr.ne (by decide : ChirpRawReg.dst ≠ .count), rows, M]
    · simp [S₂, S₁, hkc, hkd]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
