module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableStreams

/-! # Chirp table emission on the actual tape host

Lower the proved stream programs using the existing table compiler. The output stack gains
the words in forward order, with explicit tape-step costs, native-stack preservation and
an exact bank contract. Table variables are owned working data; final cleanup is a later
composition phase.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.Resampling.WeightNat

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}

private theorem chirpTableHost_stream (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (code : TblCode 48) (st : TblSt 48 A) (Post : TblSt 48 A → Prop) (K : ℕ)
    (words : List (Fin (A + 4)))
    (run : TblDo A W w code st (fun z => z.acc = words.reverse ++ st.acc ∧ Post z) K)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ) (st' : TblSt 48 A), Post st' ∧ v'.user = v.user ∧ n ≤ K * tblC W w + 2 * words.length + 2 ∧
      Exec body (tblHost rg code out) (mk v S) n (mk v' S') ∧
      S'.R out = words ++ S.R out ∧ tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v', S', n, st', ⟨ha, hp⟩, hu, hn, he, ho, hb, hi, hno, hl, hf⟩ :=
    tblHost_runs (body := body) hrg hout wl nl hwl hnl hw run hfit v S hS
  rw [ha, hacc, List.append_nil, List.length_reverse] at hn
  rw [ha, hacc, List.append_nil, List.reverse_reverse] at ho
  exact ⟨v', S', n, st', hp, hu, hn, he, ho, hb, hi, hno, hl, hf⟩

/-- Actual input/kernel table generation, with no prepared pi or coefficient inputs. -/
theorem tblChirpNegativeStream_host (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset k0 N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hk : st.val 38 = k0) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hkB : k0 ≤ B) (hNB : N ≤ B) (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ) (st' : TblSt 48 A),
      (st'.val 18 = piN q ∧ st'.val 19 = q ∧ st'.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → st'.val i = st.val i) ∧
      v'.user = v.user ∧ n ≤ (N * (310 * q + 122) + 150 * q + 404) * tblC W w + 2 * (N * w) + 2 ∧
      Exec body (tblHost rg (tblChirpNegativeStream kernel) out) (mk v S) n (mk v' S') ∧
      S'.R out = chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j) ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  simpa only [length_chirpEntryStream] using chirpTableHost_stream (body := body) hrg hout wl nl hwl hnl hw
    (tblChirpNegativeStream kernel) st _ _
    (chirpEntryStream A w N (fun j => chirpNegativeNumerator kernel s t α q offset k0 j))
    (tblChirpNegativeStream_do st size kernel s t α offset k0 N hq hs ht hα ho hk hN
      hst hsB htB hαB hoB hkB hNB) hfit hacc v S hS

/-- Actual normalized output-factor table generation, with all exponent arguments computed. -/
theorem tblChirpOutputStream_host (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (s t α N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hNB : N ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α) (hgate : ∀ b < N, 4 * chirpEN s t b ≤ (q - 1) * chirpED t α)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ) (st' : TblSt 48 A),
      (st'.val 18 = piN q ∧ st'.val 19 = q ∧ st'.val 39 = N ∧
        ∀ i : Fin 48, 34 ≤ i.val → i ≠ 39 → i ≠ 40 → i ≠ 41 → st'.val i = st.val i) ∧
      v'.user = v.user ∧ n ≤ (N * (310 * q + 113) + 150 * q + 404) * tblC W w + 2 * (N * w) + 2 ∧
      Exec body (tblHost rg tblChirpOutputStream out) (mk v S) n (mk v' S') ∧
      S'.R out = chirpEntryStream A w N (fun b => chirpTableE s t α q b) ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  simpa only [length_chirpEntryStream] using chirpTableHost_stream (body := body) hrg hout wl nl hwl hnl hw
    tblChirpOutputStream st _ _ (chirpEntryStream A w N (fun b => chirpTableE s t α q b))
    (tblChirpOutputStream_do st size s t α N hq hs ht hα hN hst hsB htB hαB hNB ht0 hα0 hgate)
    hfit hacc v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
