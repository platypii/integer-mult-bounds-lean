module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowBinaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishBinaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRowCoefficient
import Mathlib.Tactic.FinCases

/-! Retain pi and scaling powers with the row geometry, preparing them once per pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.Resampling.WeightNat

def preparedRowPacketFields : List (Fin 50) := [37,19,44,34,35,36,49,18,22,39,40]

def preparedRowPacketArguments (P q s t u band i : ℕ) : List (Fin 50 × ℕ) :=
  [(37,i),(19,P),(44,q),(34,s),(35,t),(36,u),(49,band),(18,piN P),(22,1),(39,2^q),(40,2^P)]

def preparedRowPacket (A W P q s t u band i : ℕ) : List (Fin (A+4)) :=
  (preparedRowPacketArguments P q s t u band i).flatMap (fun r => binSyms W r.2)

def preparedRowHeaderState {A : ℕ} (P q s t u band i : ℕ) : TblSt 50 A :=
  ⟨Function.update (Function.update (Function.update (Function.update
    (rowCoefficientHeaderState (A := A) P q s t u band i).val 18 (piN P)) 22 1) 39 (2^q)) 40 (2^P),[]⟩

@[simp] theorem preparedRowPacket_length (A W P q s t u band i : ℕ) :
    (preparedRowPacket A W P q s t u band i).length = 11*W := by
  simp [preparedRowPacket,preparedRowPacketArguments]; omega

theorem preparedRowHeaderState_ready {A : ℕ} (P q s t u band i : ℕ) :
    CoefficientRowReady P q s t u band i (preparedRowHeaderState (A := A) P q s t u band i) := by
  constructor <;> simp [preparedRowHeaderState,rowCoefficientHeaderState]

theorem preparedRowHeaderState_fits {A : ℕ} (P q w s t u band i : ℕ)
    (hP : 13 ≤ P) (hi : i < s) :
    ∀ r, (preparedRowHeaderState (A := A) P q s t u band i).val r <
      2^(liftedCoefficientWidth P q w s t u band) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hf := liftedCoefficientWidth_fits false P q w s t u band i 0 hi (by omega)
  have hpiBase : piN P < 2^(5*P+2) := by
    have hh := tbl_piN_lt P (by omega)
    convert hh using 1 <;> rw [pow_add] <;> ring
  have hpi : piN P < 2^V := hpiBase.trans_le
    (Nat.pow_le_pow_right (by decide) (by have hh := hf.semanticWidth; dsimp [V]; omega))
  have hq : 2^q < 2^V := Nat.pow_lt_pow_right (by decide)
    (by have hh := hf.gridWidth; dsimp [V]; omega)
  have hp : 2^P < 2^V := Nat.pow_lt_pow_right (by decide)
    (by have hh := hf.semanticWidth; dsimp [V]; omega)
  have hone : 1 < 2^V := by
    have hpos : 0 < V := by have hh := hf.semanticWidth; dsimp [V]; omega
    exact Nat.one_lt_two_pow hpos.ne'
  intro r
  simp only [preparedRowHeaderState,Function.update_apply]
  split_ifs <;> first | assumption | exact rowCoefficientHeaderState_fits P q w s t u band i hi r

theorem loadedBinaryState_preparedRowPacket {A : ℕ} (P q s t u band i : ℕ) :
    loadedBinaryState (preparedRowPacketArguments P q s t u band i) (⟨fun _ => 0,[]⟩ : TblSt 50 A) =
      preparedRowHeaderState P q s t u band i := by
  simp only [preparedRowPacketArguments,loadedBinaryState,preparedRowHeaderState,rowCoefficientHeaderState]
  congr 1
  funext r
  fin_cases r <;> simp

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def borrowPreparedRowPacket (rg : TblR 50 → Fin T) (src work count saved tmp : Fin T) : Pr P₀ T Q A U :=
  borrowBinaryHeaders rg src work count saved tmp preparedRowPacketFields

theorem borrowPreparedRowPacket_exec {rg : TblR 50 → Fin T} (hrg : Function.Injective rg)
    (src work count saved tmp : Fin T) (hreg : [src,work,count,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [src,work,count,saved,tmp], ∀ r, rg r ≠ k)
    (W P q s t u band i : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl ⟨fun _ => 0,[]⟩))
    (hsrc : S.R src = preparedRowPacket A W P q s t u band i++tail)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ 224*W+105 ∧
      Exec body (borrowPreparedRowPacket rg src work count saved tmp) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl (preparedRowHeaderState P q s t u band i)) ∧ tblFr rg S S' := by
  obtain ⟨v',S',m,hu,hm,he,hh,hf⟩ := borrowBinaryHeaders_exec (body := body) hrg src work count saved tmp
    hreg hsep (preparedRowPacketArguments P q s t u band i) W wl nl hwl ⟨fun _ => 0,[]⟩ tail v S hS hsrc
    hcount hsaved htmp
  refine ⟨v',S',m,hu,?_,?_,?_,hf⟩
  · simp only [preparedRowPacketArguments,List.length_cons,List.length_nil] at hm
    nlinarith only [hm]
  · simpa [borrowPreparedRowPacket,borrowBinaryHeaders,preparedRowPacketArguments,preparedRowPacketFields] using he
  · simpa only [loadedBinaryState_preparedRowPacket] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
