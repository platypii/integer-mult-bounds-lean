module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost

/-! Fixed-width binary geometry loading for packed lookups. The geometry metadata
words occupy the existing geometry source ports; the remaining variables use
the shared encoded-zero source. This path does not scan unary ambient sizes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

def packedLookupBankSource (i : Fin 16) : Fin 117 :=
  if i = 0 then 97 else if i = 1 then 98 else if i = 2 then 100 else
  if i = 3 then 107 else if i = 4 then 101 else if i = 5 then 103 else
  if i = 7 then 107 else if i = 8 then 105 else 106

def loadPackedLookupBank {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  chirpBankLoad originReg packedLookupBankSource 115 115

theorem loadPackedLookupBank_cost (V : ℕ) :
    chirpBankLoadCost originReg packedLookupBankSource V V (fun _ => V) = 136*V+137 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments]
  ring

theorem loadPackedLookupBank_frame {A : ℕ} (V : ℕ) (value : Fin 117 → ℕ)
    (R : Fin 117 → List (Fin (A+4))) (k : Fin 117) (hk : 31 ≤ k.val) :
    chirpBankLoadR originReg packedLookupBankSource V V value R k = R k := by
  apply chirpBankLoad_off
  intro r he
  have hr := originReg_range r
  rw [← he] at hr
  omega

theorem loadPackedLookupBank_exec {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}
    (V : ℕ) (value : Fin 117 → ℕ)
    (hfit : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V)
    (hsrc : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, S.R (originReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body loadPackedLookupBank (mk v S) (136*V+137)
        (mk v' {S with R := chirpBankLoadR originReg packedLookupBankSource V V value S.R}) ∧
      tblHolds originReg {S with R := chirpBankLoadR originReg packedLookupBankSource V V value S.R}
        (tblRho V (List.replicate V tick) (List.replicate V tick)
          ⟨fun i => value (packedLookupBankSource i),[]⟩) ∧
      ∀ k : Fin 117, 31 ≤ k.val →
        chirpBankLoadR originReg packedLookupBankSource V V value S.R k = S.R k := by
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  have hinput : ∀ i r, originReg r ≠ packedLookupBankSource i := by
    intro i
    apply hoff
    simp only [packedLookupBankSource]
    split_ifs <;> decide
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective
    packedLookupBankSource 115 115 (hoff 115 (by decide)) (hoff 115 (by decide))
    hinput V V (fun _ => V) value hfit (fun _ => le_rfl) v S hV hV hsrc hblank
  exact ⟨v',hu,he.cast (loadPackedLookupBank_cost V) rfl,
    chirpBankLoad_holds originReg originReg_injective packedLookupBankSource V V value S hblank,fun k hk => loadPackedLookupBank_frame V value S.R k hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
