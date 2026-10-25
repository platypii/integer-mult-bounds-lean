module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

/-! # Initialize the scalar source bank from four original binary words

A shared empty source initializes every workspace variable and the zero-length
emission header. Only the binary-word-width counter is supplied separately.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

namespace ForwardParameters

def sourceIndex (i : Fin 16) : Fin 5 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 14 then 2 else if i = 15 then 3 else 4

def sourceValues (p α s t : ℕ) : Fin 16 → ℕ :=
  fun i => (![p, α, s, t, 0] : Fin 5 → ℕ) (sourceIndex i)

end ForwardParameters

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpForwardSourceLoad (rg : TblR 16 → Fin T) (raw : Fin 5 → Fin T) (width : Fin T) : Pr P T Q A U :=
  chirpBankLoad rg (fun i => raw (ForwardParameters.sourceIndex i)) width (raw 4)

/-- No source-bank variable, header, accumulator or scratch template is a caller input. -/
theorem chirpForwardSourceLoad_exec (rg : TblR 16 → Fin T) (hrg : Function.Injective rg)
    (raw : Fin 5 → Fin T) (hraw : Function.Injective raw) (width : Fin T)
    (hsep : ∀ r i, rg r ≠ raw i) (hwidth : ∀ r, rg r ≠ width)
    (W b p α s t : ℕ) (hbW : b ≤ W)
    (hfit : ∀ i : Fin 4, (![p, α, s, t] : Fin 4 → ℕ) i < 2 ^ b)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = W)
    (hwords : ∀ i : Fin 4, S.R (raw i.castSucc) = binSyms b ((![p, α, s, t] : Fin 4 → ℕ) i))
    (hzero : S.R (raw 4) = []) (hblank : ∀ r, S.R (rg r) = []) :
    ∃ v' R k, v'.user = v.user ∧ k = 100 * W + 8 * b + 137 ∧
      Exec body (chirpForwardSourceLoad rg raw width) (mk v S) k (mk v' { S with R := R }) ∧
      tblHolds rg { S with R := R } (tblRho W (List.replicate W tick) []
        ⟨ForwardParameters.sourceValues p α s t, []⟩) ∧
      (∀ k, (∀ r, k ≠ rg r) → R k = S.R k) := by
  classical
  let values : Fin 5 → ℕ := ![p, α, s, t, 0]
  let lengths : Fin 5 → ℕ := ![b, b, b, b, 0]
  let value := Function.extend raw values (fun _ => 0)
  let bits := Function.extend raw lengths (fun _ => 0)
  have hvalue (i : Fin 5) : value (raw i) = values i := hraw.extend_apply _ _ i
  have hbits (i : Fin 5) : bits (raw i) = lengths i := hraw.extend_apply _ _ i
  have hfits (i : Fin 5) : values i < 2 ^ lengths i := by
    fin_cases i <;> first | exact hfit 0 | exact hfit 1 | exact hfit 2 | exact hfit 3 | (simp [values, lengths])
  have hlength (i : Fin 5) : lengths i ≤ W := by fin_cases i <;> simp [lengths] <;> exact hbW
  have hword (i : Fin 5) : S.R (raw i) = binSyms (lengths i) (values i) := by
    fin_cases i <;> first | exact hwords 0 | exact hwords 1 | exact hwords 2 | exact hwords 3 | simpa [lengths, values, binSyms] using hzero
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) rg hrg
    (fun i => raw (ForwardParameters.sourceIndex i)) width (raw 4) hwidth (fun r => hsep r 4)
    (fun i r => hsep r _) W 0 bits value
    (by intro i; rw [hvalue, hbits]; exact hfits _) (by intro i; rw [hbits]; exact hlength _)
    v S hw (by rw [hzero]; rfl) (by intro i; rw [hvalue, hbits]; exact hword _) hblank
  have hcost : chirpBankLoadCost rg (fun i => raw (ForwardParameters.sourceIndex i)) W 0 bits =
      100 * W + 8 * b + 137 := by
    simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
      List.ofFn_succ, ForwardParameters.sourceIndex, hbits, lengths]
    omega
  refine ⟨v', _, _, hu, hcost, he, ?_, ?_⟩
  · have hh := chirpBankLoad_holds rg hrg (fun i => raw (ForwardParameters.sourceIndex i)) W 0 value S hblank
    have hv : (fun i => value (raw (ForwardParameters.sourceIndex i))) =
        ForwardParameters.sourceValues p α s t := by
      funext i
      rw [hvalue]
      rfl
    rw [hv, List.replicate_zero] at hh
    exact hh
  · exact fun k hk => chirpBankLoad_off rg _ W 0 value S.R k hk

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
