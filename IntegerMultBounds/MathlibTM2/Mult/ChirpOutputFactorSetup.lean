module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputTableSetup

/-! # Generate both output-factor tapes with one reusable bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast

def chirpOutputFactors (s t α q Γ m : ℕ) : List ℤ :=
  (List.range m).map fun b => (chirpTableE s t α (q - Γ) b : ℤ)

@[simp] theorem chirpOutputFactors_length (s t α q Γ m : ℕ) :
    (chirpOutputFactors s t α q Γ m).length = m := by simp [chirpOutputFactors]

/-- The generated E tape has the exact representation consumed by the real-table multiplier. -/
theorem chirpOutputFactors_stream (A w s t α q Γ m : ℕ) :
    cstream A w ((chirpOutputFactors s t α q Γ m).map fun e => (⟨e, 0⟩ : GaussianInt)) =
      chirpEntryStream A w m (fun b => chirpTableE s t α (q - Γ) b) := by
  simp only [chirpOutputFactors, chirpEntryStream, List.map_map]
  rfl

/-- The analytic factor bounds discharge every generated E word's multiplier precondition. -/
theorem chirpOutputFactors_bound (s t α q Γ m : ℕ) (hs : 0 < s) (hst : s < t)
    (hα : 0 < α) (hΓq : Γ ≤ q) (hq : 13 ≤ q - Γ)
    (hgate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hΓ : ∀ b < m, NLogN.chirpE s t (α : ℝ) b ≤ 2 ^ Γ) :
    ∀ e ∈ chirpOutputFactors s t α q Γ m, |(e : ℝ) / 2 ^ q| ≤ 2 := by
  intro e he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  have hb' := List.mem_range.mp hb
  simpa only [Int.cast_natCast] using
    chirpOutputE_abs_le_two s t α q Γ b hs hst hα hΓq hq (hgate b hb') (hΓ b hb')

def chirpOutputFactorSetup (rg : TblR 48 → Fin T) (es norm : Fin T) : Pr P T Q A U :=
  .seq (tblHost rg tblChirpOutputReducedTable es) (tblHost rg tblChirpNormalization norm)

def chirpOutputFactorSetupCost (W w q Γ m : ℕ) : ℕ :=
  ((m * (310 * (q - Γ) + 113) + 150 * (q - Γ) + 445) * tblC W w + 2 * (m * w) + 2) +
    ((4 * q + 13) * tblC W w + 2 * w + 2)

/-- Generate E and normalization together, retaining the shared bank and all other stacks. -/
theorem chirpOutputFactorSetup_exec {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}
    (hrg : Function.Injective rg) (es norm : Fin T) (hne : es ≠ norm)
    (hE : ∀ r, rg r ≠ es) (hNorm : ∀ r, rg r ≠ norm)
    {W w q Γ B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W (q - Γ) B) (s t α m : ℕ)
    (hq : st.val 19 = q) (hΓ : st.val 46 = Γ) (hΓq : Γ ≤ q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (h44 : st.val 44 = 0) (hqW : q < W) (hαW : 2 * α < 2 ^ W)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpOutputFactorSetupCost W w q Γ m ∧
      Exec body (chirpOutputFactorSetup rg es norm) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update S.R es
            (cstream A w ((chirpOutputFactors s t α q Γ m).map fun e => (⟨e, 0⟩ : GaussianInt)) ++ S.R es))
          norm (csyms A w (⟨(chirpNormalization q α : ℤ), 0⟩ : GaussianInt) ++ S.R norm)) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOutputTableSetup_exec (body := body) hrg hE
    wl nl hwl hnl hw st size s t α m hq hΓ hΓq hs ht hα hm h44
    hst hsB htB hαB hmB ht0 hα0 hgate howned hfit hacc v S hS
  let S₁ : Stacks T A := { S with R := (Function.update S.R es
    (chirpEntryStream A w m (fun b => chirpTableE s t α (q - Γ) b) ++ S.R es)) }
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := fun r => by
    simpa only [S₁, Function.update_of_ne (hE r)] using hS r
  have hz : ∀ i : Fin 48, i.val < 4 → st.val i = 0 := by
    intro i hi
    exact howned i ((chirpTableOwned_mem i).mpr (Or.inl ⟨by omega, by
      intro h; subst i; norm_num at hi⟩))
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpNormalizationSetup_exec (body := body) hrg hNorm
    wl nl hwl hnl hw st q α hq hα hqW hαW hz hfit hacc v₁ S₁ hb₁
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  simp only [S₁, Function.update_of_ne hne.symm, chirpOutputFactors_stream]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
