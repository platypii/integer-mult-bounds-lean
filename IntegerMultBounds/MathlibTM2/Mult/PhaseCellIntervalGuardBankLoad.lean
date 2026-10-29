module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardBank

/-! Fixed-width binary geometry loading for packed lookups. The geometry metadata
words occupy the existing geometry source ports; the remaining variables use
the shared encoded-zero source. This path does not scan unary ambient sizes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

def intervalGuardBankSource (i : Fin 17) : Fin 117 :=
  if i = 0 then 97 else if i = 1 then 98 else if i = 2 then 100 else
  if i = 3 then 107 else if i = 4 then 101 else if i = 5 then 103 else
  if i = 16 then 108 else 106

def loadIntervalGuardBank {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  chirpBankLoad intervalGuardReg intervalGuardBankSource 115 115

theorem loadIntervalGuardBank_cost (V : ℕ) :
    chirpBankLoadCost intervalGuardReg intervalGuardBankSource V V (fun _ => V) = 144*V+145 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments]
  ring

theorem loadIntervalGuardBank_frame {A : ℕ} (V : ℕ) (value : Fin 117 → ℕ)
    (R : Fin 117 → List (Fin (A+4))) (k : Fin 117) (hk : 32 ≤ k.val) :
    chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value R k = R k := by
  apply chirpBankLoad_off
  intro r he
  have hr := intervalGuardReg_range r
  rw [← he] at hr
  omega

theorem loadIntervalGuardBank_exec {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}
    (V : ℕ) (value : Fin 117 → ℕ)
    (hfit : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V)
    (hsrc : ∀ i, S.R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, S.R (intervalGuardReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body loadIntervalGuardBank (mk v S) (144*V+145)
        (mk v' {S with R := chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value S.R}) ∧
      tblHolds intervalGuardReg {S with R := chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value S.R}
        (tblRho V (List.replicate V tick) (List.replicate V tick)
          ⟨fun i => value (intervalGuardBankSource i),[]⟩) ∧
      ∀ k : Fin 117, 32 ≤ k.val →
        chirpBankLoadR intervalGuardReg intervalGuardBankSource V V value S.R k = S.R k := by
  have hoff (k : Fin 117) (hk : 32 ≤ k.val) : ∀ r, intervalGuardReg r ≠ k := by
    intro r he
    have hr := intervalGuardReg_range r
    rw [he] at hr
    omega
  have hinput : ∀ i r, intervalGuardReg r ≠ intervalGuardBankSource i := by
    intro i
    apply hoff
    simp only [intervalGuardBankSource]
    split_ifs <;> decide
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) intervalGuardReg intervalGuardReg_injective
    intervalGuardBankSource 115 115 (hoff 115 (by decide)) (hoff 115 (by decide))
    hinput V V (fun _ => V) value hfit (fun _ => le_rfl) v S hV hV hsrc hblank
  exact ⟨v',hu,he.cast (loadIntervalGuardBank_cost V) rfl,
    chirpBankLoad_holds intervalGuardReg intervalGuardReg_injective intervalGuardBankSource V V value S hblank,fun k hk => loadIntervalGuardBank_frame V value S.R k hk⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
