module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRestored

/-! # Table generation changes only its destination stack

The owned table variables return to zero, dimensions and controls retain their values,
and the host compiler restores its internal bank. Together these facts yield one full
stack equation, including user state, native stacks, left stacks and all spectators.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}

/-- Lower a restored table program to a destination-only host execution. -/
theorem tblChirpRestored_host (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (code : TblCode 48) (st : TblSt 48 A) (words : List (Fin (A + 4))) (K : ℕ)
    (run : TblDo A W w code st (fun z => z.val = st.val ∧ z.acc = words.reverse ++ st.acc) K)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ K * tblC W w + 2 * words.length + 2 ∧
      Exec body (tblHost rg code out) (mk v S) n
        (mk v' { S with R := Function.update S.R out (words ++ S.R out) }) := by
  classical
  obtain ⟨v', S', n, st', ⟨hv, ha⟩, hu, hn, he, ho, hb, hi, hno, hl, hf⟩ :=
    tblHost_runs (body := body) hrg hout wl nl hwl hnl hw run hfit v S hS
  rw [ha, hacc, List.append_nil, List.length_reverse] at hn
  rw [ha, hacc, List.append_nil, List.reverse_reverse] at ho
  have hst : (⟨st'.val, []⟩ : TblSt 48 A) = st := by
    calc _ = ⟨st.val, st.acc⟩ := by rw [hv, hacc]
      _ = st := rfl
  rw [hst] at hb
  have hstack : S' = { S with R := Function.update S.R out (words ++ S.R out) } := by
    ext1
    · exact hi
    · exact hno
    · exact hl
    · funext k
      by_cases hk : k = out
      · subst k
        simpa only [Function.update_self] using ho
      · change S'.R k = Function.update S.R out (words ++ S.R out) k
        rw [Function.update_of_ne hk]
        by_cases hr : ∃ r, rg r = k
        · obtain ⟨r, rfl⟩ := hr
          exact (hb r).trans (hS r).symm
        · exact hf k hk (fun r h => hr ⟨r, h⟩)
  exact ⟨v', n, hu, hn, by simpa only [hstack] using he⟩

/-- Input/kernel table generation with complete working-bank and scratch restoration. -/
theorem tblChirpNegativeTable_host (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset k0 N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hkB : k0 ≤ B) (hNB : N ≤ B) (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (N * (310 * q + 122) + 150 * q + 441) * tblC W w + 2 * (N * w) + 2 ∧
      Exec body (tblHost rg (tblChirpNegativeTable kernel) out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j) ++ S.R out)) }) := by
  simpa only [length_chirpEntryStream] using tblChirpRestored_host (body := body) hrg hout wl nl hwl hnl hw
    (tblChirpNegativeTable kernel) st _ _
    (tblChirpNegativeTable_do st size kernel s t α offset k0 N hq hs ht hα ho hk hN
      hst hsB htB hαB hoB hkB hNB howned) hfit hacc v S hS

/-- Output-factor table generation with only the destination changed. -/
theorem tblChirpOutputTable_host (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (s t α N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hNB : N ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α) (hgate : ∀ b < N, 4 * chirpEN s t b ≤ (q - 1) * chirpED t α)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (N * (310 * q + 113) + 150 * q + 441) * tblC W w + 2 * (N * w) + 2 ∧
      Exec body (tblHost rg tblChirpOutputTable out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (chirpEntryStream A w N (fun b => chirpTableE s t α q b) ++ S.R out)) }) := by
  simpa only [length_chirpEntryStream] using tblChirpRestored_host (body := body) hrg hout wl nl hwl hnl hw
    tblChirpOutputTable st _ _ (tblChirpOutputTable_do st size s t α N hq hs ht hα hN
      hst hsB htB hαB hNB ht0 hα0 hgate howned) hfit hacc v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
