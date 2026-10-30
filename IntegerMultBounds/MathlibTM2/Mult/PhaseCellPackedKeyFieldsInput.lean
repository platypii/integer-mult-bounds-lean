module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyInputCounted
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeySetupFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData

/-! The executed input stage establishes the packed supplier's local field ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 276 Q A U}

theorem packedKeyFieldsInput_exec {p l s t u target rhsExp a b V : ℕ} [NeZero s]
    {α gap : ℝ} {C : ZMod s → GaussianInt} (q W : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (tail : List (Fin (A+4))) (v : HS 276 Q A U) (S : Stacks 276 A)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C (embStk packedKeySetupReg S))
    (hq : (S.R 119).length = q) (hpHeader : (S.R 266).length = p)
    (hcommon : (S.R 265).length = W) (hreplicas : (S.R 264).length = Fs.length)
    (hpacket : (S.R 267).length = (b-a)*W)
    (hsrc : S.R 263 = cstream A W (Fs.map (packedInterval a (b-a))).flatten++tail)
    (hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), S.R i = [])
    (hcountBlank : S.R 251 = []) :
    let rhs := (Fs.map (fun F => cstream A (2*q+8)
      (packedInterval a (b-a) (fun i => (2 : GaussianInt)^(q-p-1)*F i)))).flatten
    let B : Stacks 276 A := {S with R := (Function.update
      (Function.update (Function.update S.R 263 tail) 110 rhs) 251 (List.replicate Fs.length tick))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedKeyInputCost p q W Fs.length (b-a)+(4*Fs.length+4) ∧
      Exec body packedKeyInputCounted (mk v S) n (mk v' B) ∧
      PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
        (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C (embStk packedKeySetupReg B) ∧
      (∀ F ∈ Fs, ∀ i, ‖value q ((2 : GaussianInt)^(q-p-1)*F i)‖ ≤ (2 : ℝ)^rhsExp) := by
  dsimp only
  have hfit : a+(b-a) ≤ s := by have ha := hsetup.hab; have hb := hsetup.hbs; omega
  obtain ⟨v',n,hu,hn,he⟩ := packedKeyInputCounted_exec (body := body) p q W Fs.length (b-a) hpq hW
    (Fs.map (packedInterval a (b-a))).flatten (packedBatch_length a (b-a) Fs hfit) tail v S
    hq hpHeader hcommon hreplicas hpacket hsrc hblank hcountBlank
  rw [packedBatch_shift_source] at he
  exact ⟨v',n,hu,hn,he,hsetup.packed_key_input _ _ _,packedBatch_shift_bound p q rhsExp hpq Fs hF⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
