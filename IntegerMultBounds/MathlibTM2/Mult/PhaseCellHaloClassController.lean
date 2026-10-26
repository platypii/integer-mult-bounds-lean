module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGroupHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Initialize the ambient phase constants and generate the origins and count
of one positive clipped length class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloClassRawState (A s t band a b L : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 13 a) 14 b) 3 L, []⟩

def haloClassReadyState (A s t band a b L : ℕ) : TblSt 16 A :=
  let st := haloClassRawState A s t band a b L
  ⟨Function.update (Function.update (Function.update st.val 6 (2*(t-s))) 7 1) 15 (t-s+1), []⟩

theorem haloClassInitCode_do {A W w s t band a b L : ℕ} (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w originInitCode (haloClassRawState A s t band a b L)
      (fun st' => st' = haloClassReadyState A s t band a b L) 6 := by
  have hb : 2*t+2 < 2^W := by nlinarith only [hwide]
  have hW : W ≠ 0 := by intro he; subst W; simp at hb
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, haloClassRawState, hW]
    omega
  · simp [tblExactList, TblIns.exact, haloClassRawState, haloClassReadyState, Function.update_idem, two_mul]

theorem haloClassRawState_bounded {A W s t band a b L : ℕ} (ha : a ≤ s) (hb : b ≤ s) (hL : L ≤ s) (hst : s < t) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    ∀ k, (haloClassRawState A s t band a b L).val k < 2^W := by
  have ht : t < 2^W := by nlinarith only [hwide]
  intro k
  simp only [haloClassRawState, Function.update_apply]
  split_ifs <;> omega

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloClassController : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg originInitCode) haloGroupCountedHost

theorem haloClassController_exec {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V
      (List.replicate V tick)
      (List.replicate V tick) (haloClassRawState A s t band a b L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+9)*tblC V V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      Exec body haloClassController (mk v S) m (mk v' S') ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hpkt : s < 2^V := by nlinarith only [hwide, hst]
  have hbound := haloClassRawState_bounded (A := A) has hbs hLs hst hband hwide
  have hc := haloClassInitCode_do (A := A) (W := V) (w := V) (a := a) (b := b) (L := L) hs hst hwide
  obtain ⟨st₁, ⟨heq, hb₁⟩, hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hbound) hbound
  subst heq
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hh₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hout, hcount, hh₂, hb₂, hi₂, ho₂, hl₂, hframe⟩ :=
    haloGroupCountedHost_exec (body := body) (s := s) (t := t) (band := band) (a := a) (b := b) (L := L)
      (haloClassReadyState A s t band a b L)
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      has hbs hs hst hL hwide hpkt.le le_rfl hA (by
        have hv : V ≠ 0 := by intro he; rw [he] at hwide; simp at hwide
        omega) hb₁ rfl v₁ S₁ hh₁
      (by rw [hf₁.2.2.2 104 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h104])
      (by rw [hf₁.2.2.2 106 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h106])
      (by rw [hf₁.2.2.2 116 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h116])
  refine ⟨v₂, S₂, m₁+m₂, st₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, hcount, hh₂, hb₂,
    hi₂.trans hf₁.1, ho₂.trans hf₁.2.1, hl₂.trans hf₁.2.2.1, ?_⟩
  · nlinarith only [hm₁, hm₂]
  · rw [hout, hf₁.2.2.2 109 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)]
  · intro k hk109 hk116 hk
    exact (hframe k hk109 hk116 hk).trans (hf₁.2.2.2 k hk)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
