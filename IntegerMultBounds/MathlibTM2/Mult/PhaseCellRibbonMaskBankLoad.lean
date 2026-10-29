module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def ribbonMaskBankSource (i : Fin 18) : Fin 168 :=
  if i = 0 then 145 else if i = 1 then 146 else if i = 2 then 147 else
  if i = 4 then 149 else if i = 5 then 151 else if i = 16 then 155 else
  if i = 17 then 164 else 154

def loadRibbonMaskBank {P U : Type} {Q A : ℕ} : Pr P 168 Q A U :=
  chirpBankLoad ribbonTableReg ribbonMaskBankSource 163 163

theorem loadRibbonMaskBank_exec {P U : Type} {Q A : ℕ} {body : P → Pr P 168 Q A U}
    (V : ℕ) (value : Fin 168 → ℕ) (hfit : ∀ i, value (ribbonMaskBankSource i) < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hsrc : ∀ i, S.R (ribbonMaskBankSource i) = binSyms V (value (ribbonMaskBankSource i)))
    (hblank : ∀ r, S.R (ribbonTableReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body loadRibbonMaskBank (mk v S) (152*V+153)
        (mk v' {S with R := chirpBankLoadR ribbonTableReg ribbonMaskBankSource V V value S.R}) ∧
      tblHolds ribbonTableReg {S with R := chirpBankLoadR ribbonTableReg ribbonMaskBankSource V V value S.R}
        (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun i => value (ribbonMaskBankSource i),[]⟩) ∧
      ∀ k : Fin 168, 33 ≤ k.val →
        chirpBankLoadR ribbonTableReg ribbonMaskBankSource V V value S.R k = S.R k := by
  have hoff (k : Fin 168) (hk : 33 ≤ k.val) : ∀ r, ribbonTableReg r ≠ k := by
    intro r he
    have hr := ribbonTableReg_range r
    rw [he] at hr
    omega
  have hinput : ∀ i r, ribbonTableReg r ≠ ribbonMaskBankSource i := by
    intro i
    apply hoff
    simp only [ribbonMaskBankSource]; split_ifs <;> decide
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) ribbonTableReg ribbonTableReg_injective
    ribbonMaskBankSource 163 163 (hoff 163 (by decide)) (hoff 163 (by decide))
    hinput V V (fun _ => V) value hfit (fun _ => le_rfl) v S hV hV hsrc hblank
  have hcost : chirpBankLoadCost ribbonTableReg ribbonMaskBankSource V V (fun _ => V) = 152*V+153 := by
    simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments]
    ring
  refine ⟨v',hu,he.cast hcost rfl,
    chirpBankLoad_holds ribbonTableReg ribbonTableReg_injective ribbonMaskBankSource V V value S hblank,?_⟩
  intro k hk
  exact chirpBankLoad_off ribbonTableReg ribbonMaskBankSource V V value S.R k (fun r => (hoff k hk r).symm)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
