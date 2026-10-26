module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Initialize the ambient phase constants and emit clipped origin/length
descriptors from the five numeric geometry headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloRawState (A s t band a b : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 13 a) 14 b, []⟩

def haloReadyState (A s t band a b : ℕ) : TblSt 16 A :=
  let st := haloRawState A s t band a b
  ⟨Function.update (Function.update (Function.update st.val 6 (2*(t-s))) 7 1) 15 (t-s+1), []⟩

theorem haloInitCode_do {A W w s t band a b : ℕ} (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w originInitCode (haloRawState A s t band a b)
      (fun st' => st' = haloReadyState A s t band a b) 6 := by
  have hb : 2*t+2 < 2^W := by nlinarith only [hwide]
  have hW : W ≠ 0 := by intro he; subst W; simp at hb
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, haloRawState, hW]
    omega
  · simp [tblExactList, TblIns.exact, haloRawState, haloReadyState, Function.update_idem, two_mul]

theorem haloRawState_bounded {A W s t band a b : ℕ} (ha : a ≤ s) (hb : b ≤ s) (hst : s < t) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    ∀ k, (haloRawState A s t band a b).val k < 2^W := by
  have ht : t < 2^W := by nlinarith only [hwide]
  intro k
  simp only [haloRawState, Function.update_apply]
  split_ifs <;> omega

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloDescriptorController : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg originInitCode) haloDescriptorHost

theorem haloDescriptorController_exec {V s t band a b : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V
      (List.replicate V tick)
      (List.replicate V tick) (haloRawState A s t band a b))) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+9)*tblC V V + 2*((haloCellPhases s t band a b).length*(2*V))+2 ∧
      Exec body haloDescriptorController (mk v S) m (mk v' S') ∧
      S'.R 109 = haloDescriptorPackets A V s t band a b ++ S.R 109 ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hpkt : s < 2^V := by nlinarith only [hwide, hst]
  have hbound := haloRawState_bounded (A := A) has hbs hst hband hwide
  have hc := haloInitCode_do (A := A) (W := V) (w := V) (a := a) (b := b) hs hst hwide
  obtain ⟨st₁, ⟨heq, hb₁⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hbound) hbound
  subst heq
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hout, hh₂, hb₂, hi₂, ho₂, hl₂, hframe⟩ :=
    haloDescriptorHost_exec (body := body) (s := s) (t := t) (band := band) (a := a) (b := b)
      (haloReadyState A s t band a b)
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      (by simp [haloReadyState, haloRawState])
      has hbs hs hst hwide hpkt le_rfl hA hb₁ rfl v₁ S₁ hh₁
  refine ⟨v₂, S₂, m₁+m₂, st₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, hh₂, hb₂,
    hi₂.trans hf₁.1, ho₂.trans hf₁.2.1, hl₂.trans hf₁.2.2.1, ?_⟩
  · nlinarith only [hm₁, hm₂]
  · rw [hout, hf₁.2.2.2 109 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)]
  · intro k hk109 hk
    exact (hframe k hk109 hk).trans (hf₁.2.2.2 k hk)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
