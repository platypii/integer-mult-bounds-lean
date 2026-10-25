module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Generate the phase-scan constants and emit the exact group origin packets
from four binary numeric headers. No prepared endpoints or origin list is an
input. Loading those headers from the outer bank remains separate work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem weightWorkspaceWidth_control {P q w s t u band : ℕ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) :
    let V := weightWorkspaceWidth P q w t u
    8*(t+1)^2+2*band+8 < 2^V ∧ s ≤ 2^V := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨_, _, _, _, _, _, _, hb⟩ :=
    coefficientWorkspaceWidth_bound P (w+q+2) s t u 0 t hst.le
  change u*t*(t+1)^2*2^(13*P+8) < 2^V at hb
  have hp : 32 ≤ 2^(13*P+8) := (show 32 = 2^5 by decide).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hf := Nat.mul_le_mul (show 1 ≤ u*t by nlinarith) hp
  have hm := Nat.mul_le_mul_right ((t+1)^2) hf
  have hh : 8*(t+1)^2+2*band+8 < 2^V := by nlinarith only [hb, hm, hband, hst, hs]
  exact ⟨hh, by nlinarith only [hh, hband, hst, hs]⟩

def originRawState (A s t band L : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 3 L, []⟩

def originReadyState (A s t band L : ℕ) : TblSt 16 A :=
  let st := originRawState A s t band L
  ⟨Function.update (Function.update (Function.update st.val 6 (2*(t-s))) 7 1) 15 (t-s+1), []⟩

def originInitCode : TblCode 16 :=
  tblBlock 16 [.sub 1 0 6, .add 6 6 6, .zero 7, .inc 7, .sub 1 0 15] (.inc 15)

theorem originInitCode_do {A W w s t band L : ℕ} (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w originInitCode (originRawState A s t band L)
      (fun st' => st' = originReadyState A s t band L) 6 := by
  have hb : 2*t+2 < 2^W := by nlinarith only [hwide]
  have hW : W ≠ 0 := by intro he; subst W; simp at hb
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, originRawState, hW]
    omega
  · simp [tblExactList, TblIns.exact, originRawState, originReadyState, Function.update_idem, two_mul]

theorem originRawState_bounded {A W s t band L : ℕ} (hL : L ≤ s) (hst : s < t) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    ∀ k, (originRawState A s t band L).val k < 2^W := by
  have hb : t < 2^W := by nlinarith only [hwide]
  intro k
  simp only [originRawState, Function.update_apply]
  split_ifs <;> omega

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def originController : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg originInitCode) naturalGroupHost

theorem originController_exec (P q w s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho (weightWorkspaceWidth P q w t u)
      (List.replicate (weightWorkspaceWidth P q w t u) tick)
      (List.replicate (weightWorkspaceWidth P q w t u) tick) (originRawState A s t band L))) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (27*(t-s+1)+9)*tblC V V + 2*((naturalLengthGroup s t band L).length*V)+2 ∧
      Exec body originController (mk v S) m (mk v' S') ∧
      S'.R 109 = naturalOriginPackets A V s t band L ++ S.R 109 ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨hwide, hpkt⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  have hbound := originRawState_bounded (A := A) hLs hst hband hwide
  have hc := originInitCode_do (A := A) (W := V) (w := V) (L := L) hs hst hwide
  obtain ⟨st₁, ⟨heq, hb₁⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hbound) hbound
  subst heq
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hout, hh₂, hb₂, hi₂, ho₂, hl₂, hframe⟩ :=
    naturalGroupHost_exec (body := body) (originReadyState A s t band L)
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState]) hs hst hL hwide hpkt le_rfl hA hb₁ rfl v₁ S₁ hh₁
  refine ⟨v₂, S₂, m₁+m₂, st₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, hh₂, hb₂,
    hi₂.trans hf₁.1, ho₂.trans hf₁.2.1, hl₂.trans hf₁.2.2.1, ?_⟩
  · nlinarith only [hm₁, hm₂]
  · rw [hout, hf₁.2.2.2 109 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)]
  · intro k hk109 hk
    exact (hframe k hk109 hk).trans (hf₁.2.2.2 k hk)


/-- Generate both the exact origin packets and their batch count from four headers. -/
def originCountedController : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg originInitCode) naturalGroupCountedHost

theorem originCountedController_exec (P q w s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho (weightWorkspaceWidth P q w t u)
      (List.replicate (weightWorkspaceWidth P q w t u) tick)
      (List.replicate (weightWorkspaceWidth P q w t u) tick) (originRawState A s t band L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (27*(t-s+1)+9)*tblC V V + (naturalLengthGroup s t band L).length*(8*V+6)+6 ∧
      Exec body originCountedController (mk v S) m (mk v' S') ∧
      S'.R 109 = naturalOriginPackets A V s t band L ++ S.R 109 ∧
      S'.R 116 = List.replicate (naturalLengthGroup s t band L).length tick ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨hwide, hpkt⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  have hbound := originRawState_bounded (A := A) hLs hst hband hwide
  have hc := originInitCode_do (A := A) (W := V) (w := V) (L := L) hs hst hwide
  obtain ⟨st₁, ⟨heq, hb₁⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hbound) hbound
  subst heq
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hout, hcount, hh₂, hb₂, hi₂, ho₂, hl₂, hframe⟩ :=
    naturalGroupCountedHost_exec (body := body) (originReadyState A s t band L)
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState])
      (by simp [originReadyState, originRawState]) (by simp [originReadyState, originRawState]) hs hst hL hwide hpkt le_rfl hA (by
        have hv : V ≠ 0 := by intro he; change 8*(t+1)^2+2*band+8 < 2^V at hwide; rw [he] at hwide; simp at hwide
        omega) hb₁ rfl v₁ S₁ hh₁
      (by rw [hf₁.2.2.2 104 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega), h104])
      (by rw [hf₁.2.2.2 106 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega), h106])
      (by rw [hf₁.2.2.2 116 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega), h116])
  refine ⟨v₂, S₂, m₁+m₂, st₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, hcount, hh₂, hb₂,
    hi₂.trans hf₁.1, ho₂.trans hf₁.2.1, hl₂.trans hf₁.2.2.1, ?_⟩
  · nlinarith only [hm₁, hm₂]
  · rw [hout, hf₁.2.2.2 109 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)]
  · intro k hk109 hk116 hk
    exact (hframe k hk109 hk116 hk).trans (hf₁.2.2.2 k hk)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
