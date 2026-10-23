module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableSchedule
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableRestoredHost

/-! # One host execution for the complete chirp table block schedule -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem length_chirpBlockStream {A : ℕ} (M L : ℕ) (row : ℕ → List (Fin (A + 4)))
    (hlen : ∀ j < M, (row j).length = L) :
    (chirpBlockStream M row).length = M * L := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [chirpBlockStream_succ, List.length_append, ih (fun j hj => hlen j (by omega)), hlen M (by omega)]
    ring

/-- All table rows are generated in one host invocation, with every scratch stack restored. -/
theorem tblChirpNegativeBlockTable_host {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}
    (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (kernel : Bool) (s t α offset m M N : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (ho : st.val 37 = offset) (hm : st.val 45 = m) (hM : st.val 43 = M) (hN : st.val 44 = N)
    (hst : s ≤ t) (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hoB : offset ≤ B)
    (hMB : M ≤ B) (hprod : M * m ≤ B) (hNB : N ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (M * (N * (310 * q + 122) + 150 * q + 445) + 5) * tblC W w + 2 * (M * (N * w)) + 2 ∧
      Exec body (tblHost rg (tblChirpNegativeBlockTable kernel) out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (chirpBlockStream M (fun j => chirpEntryStream A w N
            (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a)) ++ S.R out)) }) := by
  have hlen : (chirpBlockStream M (fun j => chirpEntryStream A w N
      (fun a => chirpNegativeNumerator kernel s t α q offset (j * m) a))).length = M * (N * w) :=
    length_chirpBlockStream M (N * w) _ (fun _ _ => length_chirpEntryStream ..)
  simpa only [hlen] using tblChirpRestored_host (body := body) hrg hout wl nl hwl hnl hw
    (tblChirpNegativeBlockTable kernel) st _ _
    (tblChirpNegativeBlockTable_do st size kernel s t α offset m M N hq hs ht hα ho hm hM hN
      hst hsB htB hαB hoB hMB hprod hNB howned h38 h42) hfit hacc v S hS

/-- Shape generation, all rows and cleanup in one host call; only the destination changes. -/
theorem tblChirpTableSchedule_host {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}
    (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (kernel : Bool) (s t α m M : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (hM : st.val 43 = M) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hMB : M ≤ B)
    (hprod : M * m ≤ B) (hm0 : 1 ≤ m) (hshape : 4 * m + 1 ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (h37 : st.val 37 = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) (h44 : st.val 44 = 0)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (M * (chirpTableLength kernel m * (310 * q + 122) + 150 * q + 445) + 8 +
        (if kernel then 7 else 4)) * tblC W w + 2 * (M * (chirpTableLength kernel m * w)) + 2 ∧
      Exec body (tblHost rg (tblChirpTableSchedule kernel) out) (mk v S) n
        (mk v' { S with R := (Function.update S.R out
          (chirpBlockStream M (fun j => chirpEntryStream A w (chirpTableLength kernel m)
            (fun a => chirpNegativeNumerator kernel s t α q (chirpTableOffset kernel m) (j * m) a)) ++ S.R out)) }) := by
  have hlen : (chirpBlockStream M (fun j => chirpEntryStream A w (chirpTableLength kernel m)
      (fun a => chirpNegativeNumerator kernel s t α q (chirpTableOffset kernel m) (j * m) a))).length =
      M * (chirpTableLength kernel m * w) :=
    length_chirpBlockStream M _ _ (fun _ _ => length_chirpEntryStream ..)
  simpa only [hlen] using tblChirpRestored_host (body := body) hrg hout wl nl hwl hnl hw
    (tblChirpTableSchedule kernel) st _ _
    (tblChirpTableSchedule_do st size kernel s t α m M hq hs ht hα hm hM hst
      hsB htB hαB hMB hprod hm0 hshape howned h37 h38 h42 h44) hfit hacc v S hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
