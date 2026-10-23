module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableBlockHost

/-! # Generate both input and kernel chirp table streams

Reuse the restored table bank for both schedules. No coefficient or pi stream is supplied;
only the two destinations change, with all row and bank work charged explicitly.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {rg : TblR 48 → Fin T}

def chirpScheduledStream (A w q s t α m M : ℕ) (kernel : Bool) : List (Fin (A + 4)) :=
  chirpBlockStream M (fun j => chirpEntryStream A w (chirpTableLength kernel m)
    (fun a => chirpNegativeNumerator kernel s t α q (chirpTableOffset kernel m) (j * m) a))

def chirpTableScheduleCost (W w q m M : ℕ) (kernel : Bool) : ℕ :=
  (M * (chirpTableLength kernel m * (310 * q + 122) + 150 * q + 445) + 8 +
    (if kernel then 7 else 4)) * tblC W w + 2 * (M * (chirpTableLength kernel m * w)) + 2

def chirpTablePair (rg : TblR 48 → Fin T) (input kernel : Fin T) : Pr P T Q A U :=
  .seq (tblHost rg (tblChirpTableSchedule false) input) (tblHost rg (tblChirpTableSchedule true) kernel)

@[simp] theorem length_chirpScheduledStream (A w q s t α m M : ℕ) (kernel : Bool) :
    (chirpScheduledStream A w q s t α m M kernel).length = M * (chirpTableLength kernel m * w) :=
  length_chirpBlockStream M _ _ (fun _ _ => length_chirpEntryStream ..)

/-- Generate the pair with exact whole-stack semantics and the complete bank restored. -/
theorem chirpTablePair_exec (hrg : Function.Injective rg) (input kernel : Fin T)
    (hne : input ≠ kernel) (hin : ∀ r, rg r ≠ input) (hker : ∀ r, rg r ≠ kernel)
    {W w q B : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 48 A) (size : ChirpTableSize W q B) (s t α m M : ℕ)
    (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t) (hα : st.val 36 = α)
    (hm : st.val 45 = m) (hM : st.val 43 = M) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hMB : M ≤ B)
    (hprod : M * m ≤ B) (hm0 : 1 ≤ m) (hshape : 4 * m + 1 ≤ B)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (h37 : st.val 37 = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) (h44 : st.val 44 = 0)
    (hfit : ∀ j, st.val j < 2 ^ W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true ∧
      Exec body (chirpTablePair rg input kernel) (mk v S) n
        (mk v' { S with R := (Function.update
          (Function.update S.R input (chirpScheduledStream A w q s t α m M false ++ S.R input))
          kernel (chirpScheduledStream A w q s t α m M true ++ S.R kernel)) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := tblChirpTableSchedule_host (body := body) hrg hin
    wl nl hwl hnl hw st size false s t α m M hq hs ht hα hm hM hst hsB htB hαB hMB hprod hm0 hshape
    howned h37 h38 h42 h44 hfit hacc v S hS
  let S₁ : Stacks T A := { S with R := (Function.update S.R input
    (chirpScheduledStream A w q s t α m M false ++ S.R input)) }
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := by
    intro r
    simpa only [S₁, Function.update_of_ne (hin r)] using hS r
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := tblChirpTableSchedule_host (body := body) hrg hker
    wl nl hwl hnl hw st size true s t α m M hq hs ht hα hm hM hst hsB htB hαB hMB hprod hm0 hshape
    howned h37 h38 h42 h44 hfit hacc v₁ S₁ hb₁
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  simp only [S₁, Function.update_of_ne hne.symm]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
