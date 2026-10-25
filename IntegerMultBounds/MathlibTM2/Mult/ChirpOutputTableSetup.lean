module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpNormalizationSetup

/-! # Generate normalized E factors while retaining the original precision

The original q and Γ words determine the evaluator precision q-Γ. The row count
comes from m; after emission both q and the initially empty row-count slot are
restored. No normalized E values or adjusted precision word are supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast

def tblChirpOutputReducedTable : TblCode 48 :=
  .seq (tblBlock 48 [.copy 45 44] (.sub 19 46 19))
    (.seq tblChirpOutputTable (tblBlock 48 [.add 19 46 19] (.zero 44)))

/-- Compute the normalized E row from the full-precision dimension bank. -/
theorem tblChirpOutputReducedTable_do {A W w q Γ B : ℕ} (st : TblSt 48 A)
    (size : ChirpTableSize W (q - Γ) B) (s t α m : ℕ)
    (hq : st.val 19 = q) (hΓ : st.val 46 = Γ) (hΓq : Γ ≤ q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (h44 : st.val 44 = 0) (hqW : q < 2 ^ W)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) :
    TblDo A W w tblChirpOutputReducedTable st
      (fun z => z.val = st.val ∧ z.acc =
        (chirpEntryStream A w m (fun b => chirpTableE s t α (q - Γ) b)).reverse ++ st.acc)
      (m * (310 * (q - Γ) + 113) + 150 * (q - Γ) + 445) := by
  let st₁ : TblSt 48 A := ⟨Function.update (Function.update st.val 44 m) 19 (q - Γ), st.acc⟩
  have hp : TblDo A W w (tblBlock 48 [.copy 45 44] (.sub 19 46 19)) st
      (fun z => z = st₁) 2 := TblDo.block _ _
    (by simp [tblFitsList, TblIns.fits, TblIns.exact, hq, hΓ, hΓq, hqW])
    (by simp [tblExactList, TblIns.exact, st₁, hq, hΓ, hm])
  have ho : ∀ i ∈ chirpTableOwned, st₁.val i = 0 := by
    intro i hi
    have hi19 : i ≠ 19 := by
      intro he; subst i; simp [chirpTableOwned_mem] at hi
    have hi44 : i ≠ 44 := by
      intro he; subst i; simp [chirpTableOwned_mem] at hi
    simpa only [st₁, Function.update_of_ne hi19, Function.update_of_ne hi44] using howned i hi
  have he := tblChirpOutputTable_do (w := w) st₁ size s t α m
    (by simp [st₁]) (by simpa [st₁] using hs) (by simpa [st₁] using ht)
    (by simpa [st₁] using hα) (by simp [st₁])
    hst hsB htB hαB hmB ht0 hα0 hgate ho
  have htail : ∀ u : TblSt 48 A, u.val = st₁.val →
      TblDo A W w (tblBlock 48 [.add 19 46 19] (.zero 44)) u
        (fun z => z.val = st.val ∧ z.acc = u.acc) 2 := by
    intro u hu
    have hfit : u.val 19 + u.val 46 < 2 ^ W := by
      simpa [hu, st₁, hΓ, Nat.sub_add_cancel hΓq] using hqW
    exact TblDo.block _ _ (by simpa [tblFitsList, TblIns.fits, TblIns.exact] using hfit)
      ⟨by
        funext i
        by_cases hi19 : i = 19
        · subst i; simp [tblExactList, TblIns.exact, hu, st₁, hq, hΓ, Nat.sub_add_cancel hΓq]
        by_cases hi44 : i = 44
        · subst i; simp [tblExactList, TblIns.exact, h44]
        · simp [tblExactList, TblIns.exact, hu, st₁, hi19, hi44], rfl⟩
  have hr : TblDo A W w tblChirpOutputReducedTable st
      (fun z => z.val = st.val ∧ z.acc =
        (chirpEntryStream A w m (fun b => chirpTableE s t α (q - Γ) b)).reverse ++ st.acc)
      (2 + (m * (310 * (q - Γ) + 113) + 150 * (q - Γ) + 441 + 2)) := hp.seq (fun u hu => by
    cases hu
    exact he.seq (fun z ⟨hv, ha⟩ =>
      (htail z hv).mono (fun v ⟨hv', ha'⟩ => ⟨hv', ha'.trans ha⟩) le_rfl))
  exact hr.mono (fun _ h => h) (by omega)

/-- Only the E-row destination changes; full precision and all table work are restored. -/
theorem chirpOutputTableSetup_exec {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}
    (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w q Γ B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W (q - Γ) B) (s t α m : ℕ)
    (hq : st.val 19 = q) (hΓ : st.val 46 = Γ) (hΓq : Γ ≤ q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (h44 : st.val 44 = 0)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (m * (310 * (q - Γ) + 113) + 150 * (q - Γ) + 445) * tblC W w + 2 * (m * w) + 2 ∧
      Exec body (tblHost rg tblChirpOutputReducedTable out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (chirpEntryStream A w m (fun b => chirpTableE s t α (q - Γ) b) ++ S.R out)) }) := by
  simpa only [length_chirpEntryStream] using tblChirpRestored_host (body := body) hrg hout
    wl nl hwl hnl hw tblChirpOutputReducedTable st _ _
    (tblChirpOutputReducedTable_do st size s t α m hq hΓ hΓq hs ht hα hm h44
      (by simpa only [hq] using hfit 19) hst hsB htB hαB hmB ht0 hα0 hgate howned)
    hfit hacc v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
