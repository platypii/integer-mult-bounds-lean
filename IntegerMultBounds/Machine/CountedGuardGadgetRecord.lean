import IntegerMultBounds.Machine.CountedGuardTest
import IntegerMultBounds.Machine.CountedGuardGadgetPosition
import IntegerMultBounds.Machine.GuardGadget

/-! Fixed-control guard-record bodies. Comparison widths are immutable runtime
headers; both replay and constant rewinds are literal, charged tape programs. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetRecord
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def bank (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw pc1 pc2 pc3 pf : ℤ) (ds bs : List Bool) : Tapes 11 a :=
  ⟨![pv,pw,pc1,pc2,pc3,pf,0,0,1,1,0],
    ![word V,word W,word C1,word C2,word C3,F,fun _ => blank,
      fun _ => blank,CountedLoopReuseAlphabet.binary ds,CountedLoopReuseAlphabet.binary bs,fun _ => blank]⟩

def cmpV1Place : Fin (6+5) ≃ Fin 11 where
  toFun := ![0,2,6,5,7,8,1,3,4,9,10]
  invFun := ![0,6,1,7,8,3,2,4,5,9,10]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cmpV2Place : Fin (6+5) ≃ Fin 11 where
  toFun := ![0,3,6,5,7,8,1,2,4,9,10]
  invFun := ![0,6,7,1,8,3,2,4,5,9,10]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cmpWPlace : Fin (6+5) ≃ Fin 11 where
  toFun := ![1,4,6,5,7,9,0,2,3,8,10]
  invFun := ![6,0,7,8,1,3,2,4,9,5,10]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def replayPlace : Fin (3+8) ≃ Fin 11 where
  toFun := ![0,10,8,1,2,3,4,5,6,7,9]
  invFun := ![0,3,4,5,6,7,8,9,2,10,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def compareV1 := Placement.placed (CountedGuardTest.program (a := a) .lt) cmpV1Place
def compareV2 := Placement.placed (CountedGuardTest.program (a := a) .gt) cmpV2Place
def compareW := Placement.placed (CountedGuardTest.program (a := a) .gt) cmpWPlace
def replay := Placement.placed (CountedGuardGadgetPosition.program (a := a)) replayPlace
def stepV := Placement.placed (StepRight.program (a := a)) (FiniteReturnStackAt.placement (0 : Fin 11))
def returnC1 := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement (2 : Fin 11))
def returnC2 := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement (3 : Fin 11))
def returnC3 := Placement.placed (ReturnOrigin.program (a := a)) (FiniteReturnStackAt.placement (4 : Fin 11))
def digitV := seq (seq (seq (seq (seq (stepV (a := a)) compareV1) replay) returnC1) compareV2) returnC2
def digitW := seq (compareW (a := a)) returnC3

theorem compareV1_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (_pv pw _pc1 pc2 pc3 pf : ℤ) (ds bs : List Bool) (start d : ℕ)
    (hk : Counter.value ds=d) (ck : GrowingCounterData.Canonical ds)
    (hx : start+d ≤ V.length) (hy : d ≤ C1.length) :
    HoareTime (compareV1 (a := a))
      (fun v => v=bank V W C1 C2 C3 F ((start : ℤ)) (pw) (0) (pc2) (pc3) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3
        (Function.update F pf (bitSymbol (decide (GuardTest.orderAfter .eq V C1 start d=.lt))))
        ((start+d : ℕ)) (pw) (d) (pc2) (pc3) (pf+1) ds bs) (14*d+32) := by
  have h := CountedGuardTest.runs_linear .lt (fun _ => blank) (fun _ => blank) F 0 0 pf
    V C1 start d ds hk ck hx hy
  have hh := Placement.hoare_at h cmpV1Place
    (bank V W C1 C2 C3 F ((start : ℤ)) (pw) (0) (pc2) (pc3) (pf) ds bs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (start : ℤ)=0+start; omega))
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> first | rfl | (change 0+(start : ℤ)+d=((start+d : ℕ) : ℤ); push_cast; omega) | (change 0+(d : ℤ)=d; omega)
  · funext i; fin_cases i <;> rfl

theorem compareV2_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (_pv pw pc1 _pc2 pc3 pf : ℤ) (ds bs : List Bool) (start d : ℕ)
    (hk : Counter.value ds=d) (ck : GrowingCounterData.Canonical ds)
    (hx : start+d ≤ V.length) (hy : d ≤ C2.length) :
    HoareTime (compareV2 (a := a))
      (fun v => v=bank V W C1 C2 C3 F ((start : ℤ)) (pw) (pc1) (0) (pc3) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3
        (Function.update F pf (bitSymbol (decide (GuardTest.orderAfter .eq V C2 start d=.gt))))
        ((start+d : ℕ)) (pw) (pc1) (d) (pc3) (pf+1) ds bs) (14*d+32) := by
  have h := CountedGuardTest.runs_linear .gt (fun _ => blank) (fun _ => blank) F 0 0 pf
    V C2 start d ds hk ck hx hy
  have hh := Placement.hoare_at h cmpV2Place
    (bank V W C1 C2 C3 F ((start : ℤ)) (pw) (pc1) (0) (pc3) (pf) ds bs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (start : ℤ)=0+start; omega))
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> first | rfl | (change 0+(start : ℤ)+d=((start+d : ℕ) : ℤ); push_cast; omega) | (change 0+(d : ℤ)=d; omega)
  · funext i; fin_cases i <;> rfl

theorem compareW_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv _pw pc1 pc2 _pc3 pf : ℤ) (ds bs : List Bool) (start d : ℕ)
    (hk : Counter.value bs=d) (ck : GrowingCounterData.Canonical bs)
    (hx : start+d ≤ W.length) (hy : d ≤ C3.length) :
    HoareTime (compareW (a := a))
      (fun v => v=bank V W C1 C2 C3 F (pv) ((start : ℤ)) (pc1) (pc2) (0) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3
        (Function.update F pf (bitSymbol (decide (GuardTest.orderAfter .eq W C3 start d=.gt))))
        (pv) ((start+d : ℕ)) (pc1) (pc2) (d) (pf+1) ds bs) (14*d+32) := by
  have h := CountedGuardTest.runs_linear .gt (fun _ => blank) (fun _ => blank) F 0 0 pf
    W C3 start d bs hk ck hx hy
  have hh := Placement.hoare_at h cmpWPlace
    (bank V W C1 C2 C3 F (pv) ((start : ℤ)) (pc1) (pc2) (0) (pf) ds bs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (start : ℤ)=0+start; omega))
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> first | rfl | (change 0+(start : ℤ)+d=((start+d : ℕ) : ℤ); push_cast; omega) | (change 0+(d : ℤ)=d; omega)
  · funext i; fin_cases i <;> rfl

theorem replay_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw pc1 pc2 pc3 pf : ℤ) (ds bs : List Bool) (d : ℕ) (hk : Counter.value ds=d) :
    HoareTime (replay (a := a))
      (fun v => v=bank V W C1 C2 C3 F pv pw pc1 pc2 pc3 pf ds bs)
      (fun v => v=bank V W C1 C2 C3 F (pv-d) pw pc1 pc2 pc3 pf ds bs)
      (7*d+7*ds.length+23) := by
  have h := CountedGuardGadgetPosition.positions (word (a := a) V) pv ds d hk
  have hh := Placement.hoare_at h replayPlace
    (bank V W C1 C2 C3 F pv pw pc1 pc2 pc3 pf ds bs) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  refine hh.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem stepV_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw pc1 pc2 pc3 pf : ℤ) (ds bs : List Bool) :
    HoareTime (stepV (a := a))
      (fun v => v=bank V W C1 C2 C3 F pv pw pc1 pc2 pc3 pf ds bs)
      (fun v => v=bank V W C1 C2 C3 F (pv+1) pw pc1 pc2 pc3 pf ds bs) 1 := by
  have h := Placement.hoare_at (StepRight.step_hoare (word (a := a) V) pv)
    (FiniteReturnStackAt.placement (0 : Fin 11))
    (bank V W C1 C2 C3 F pv pw pc1 pc2 pc3 pf ds bs) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem returnC1_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw _pc1 pc2 pc3 pf : ℤ) (ds bs : List Bool) :
    HoareTime (returnC1 (a := a))
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (C1.length) (pc2) (pc3) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (0) (pc2) (pc3) (pf) ds bs) (C1.length+2) := by
  have hn := ReturnOrigin.bits_nonblank (a := a) C1
  have h0 := ReturnOrigin.return_hoare (C1.map (bitSymbol (a := a))) hn
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement (2 : Fin 11))
    (bank V W C1 C2 C3 F (pv) (pw) (C1.length) (pc2) (pc3) (pf) ds bs) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem returnC2_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw pc1 _pc2 pc3 pf : ℤ) (ds bs : List Bool) :
    HoareTime (returnC2 (a := a))
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (pc1) (C2.length) (pc3) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (pc1) (0) (pc3) (pf) ds bs) (C2.length+2) := by
  have hn := ReturnOrigin.bits_nonblank (a := a) C2
  have h0 := ReturnOrigin.return_hoare (C2.map (bitSymbol (a := a))) hn
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement (3 : Fin 11))
    (bank V W C1 C2 C3 F (pv) (pw) (pc1) (C2.length) (pc3) (pf) ds bs) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem returnC3_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pw pc1 pc2 _pc3 pf : ℤ) (ds bs : List Bool) :
    HoareTime (returnC3 (a := a))
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (pc1) (pc2) (C3.length) (pf) ds bs)
      (fun v => v=bank V W C1 C2 C3 F (pv) (pw) (pc1) (pc2) (0) (pf) ds bs) (C3.length+2) := by
  have hn := ReturnOrigin.bits_nonblank (a := a) C3
  have h0 := ReturnOrigin.return_hoare (C3.map (bitSymbol (a := a))) hn
  simp only [List.length_map] at h0
  have h := Placement.hoare_at h0 (FiniteReturnStackAt.placement (4 : Fin 11))
    (bank V W C1 C2 C3 F (pv) (pw) (pc1) (pc2) (C3.length) (pf) ds bs) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank _ _) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Both first-word guards, including paid within-record replay and both
constant rewinds. The control is independent of the supplied q descriptor. -/
theorem digitV_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pw pf : ℤ) (ds bs : List Bool) (p q : ℕ) (hq : 1 ≤ q)
    (hk : Counter.value ds=q-1) (ck : GrowingCounterData.Canonical ds)
    (hx : p+q ≤ V.length) (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) :
    HoareTime (digitV (a := a))
      (fun v => v=bank V W C1 C2 C3 F p pw 0 0 0 pf ds bs)
      (fun v => v=bank V W C1 C2 C3
        (Function.update (Function.update F pf
          (bitSymbol (decide (GuardTest.orderAfter .eq V C1 (p+1) (q-1)=.lt)))) (pf+1)
          (bitSymbol (decide (GuardTest.orderAfter .eq V C2 (p+1) (q-1)=.gt))))
        (p+q : ℕ) pw 0 0 0 (pf+2) ds bs) (44*q+104) := by
  let F1 := Function.update F pf (bitSymbol (a := a) (decide (GuardTest.orderAfter .eq V C1 (p+1) (q-1)=.lt)))
  let F2 := Function.update F1 (pf+1) (bitSymbol (a := a) (decide (GuardTest.orderAfter .eq V C2 (p+1) (q-1)=.gt)))
  have hd : p+1+(q-1)=p+q := by omega
  have h1 := stepV_hoare V W C1 C2 C3 F p pw 0 0 0 pf ds bs
  rw [show (p : ℤ)+1=((p+1 : ℕ) : ℤ) by push_cast; omega] at h1
  have h2 := compareV1_hoare V W C1 C2 C3 F 0 pw 0 0 0 pf ds bs (p+1) (q-1) hk ck
    (by omega) (by omega)
  have h3 := replay_hoare V W C1 C2 C3 F1 (p+1+(q-1) : ℕ) pw (q-1 : ℕ) 0 0 (pf+1) ds bs (q-1) hk
  rw [show ((p+1+(q-1) : ℕ) : ℤ)-(q-1 : ℕ)=((p+1 : ℕ) : ℤ) by push_cast; omega] at h3
  have h4 := returnC1_hoare V W C1 C2 C3 F1 (p+1 : ℕ) pw 0 0 0 (pf+1) ds bs
  rw [hc1] at h4
  have h5 := compareV2_hoare V W C1 C2 C3 F1 0 pw 0 0 0 (pf+1) ds bs (p+1) (q-1) hk ck
    (by omega) (by omega)
  have h6 := returnC2_hoare V W C1 C2 C3 F2 (p+1+(q-1) : ℕ) pw 0 0 0 (pf+1+1) ds bs
  rw [hc2,hd,show pf+1+1=pf+2 by omega] at h6
  rw [hd,show pf+1+1=pf+2 by omega] at h5
  have hl := GrowingCounterData.canonical_width ds ck
  rw [hk] at hl
  have hn := Nat.log2_le_self (q-1)
  exact (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- The second-word guard and physical rewind of its constant. -/
theorem digitW_hoare (V W C1 C2 C3 : List Bool) (F : ℤ → Fin (a+4))
    (pv pf : ℤ) (ds bs : List Bool) (p b : ℕ)
    (hk : Counter.value bs=b) (ck : GrowingCounterData.Canonical bs)
    (hx : p+b ≤ W.length) (hc3 : C3.length=b) :
    HoareTime (digitW (a := a))
      (fun v => v=bank V W C1 C2 C3 F pv p 0 0 0 pf ds bs)
      (fun v => v=bank V W C1 C2 C3
        (Function.update F pf (bitSymbol (decide (GuardTest.orderAfter .eq W C3 p b=.gt))))
        pv (p+b : ℕ) 0 0 0 (pf+1) ds bs) (15*b+35) := by
  have h1 := compareW_hoare V W C1 C2 C3 F pv 0 0 0 0 pf ds bs p b hk ck hx (by omega)
  have h2 := returnC3_hoare V W C1 C2 C3
    (Function.update F pf (bitSymbol (decide (GuardTest.orderAfter .eq W C3 p b=.gt))))
    pv (p+b : ℕ) 0 0 0 (pf+1) ds bs
  rw [hc3] at h2
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedGuardGadgetRecord
