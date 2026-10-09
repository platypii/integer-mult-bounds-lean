import IntegerMultBounds.Machine.CountedPackedLateData
import IntegerMultBounds.Machine.CountedPackedParityRun
import IntegerMultBounds.Machine.CountedPackedReusable
import IntegerMultBounds.Machine.CountedPackedControlLoadValue

/-! Entire fixed-control late gadget on a common bank, sharing physically
blank metadata and recycling the parity word between the two early calls. -/
namespace IntegerMultBounds.Machine.CountedPackedLateRun
noncomputable section
variable {a : ℕ}

def payload (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) : Tapes 11 a :=
  ⟨![pv,pw,pu,px,0,0,0,0,0,0,0],
    ![putWord f pv (V.map bitSymbol),putWord g pw (W.map bitSymbol),
      putWord h pu (U.map bitSymbol),putWord k px (X.map bitSymbol),
      putWord (fun _ => blank) 0 (Z.map bitSymbol),fun _ => blank,fun _ => blank,
      fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank]⟩
def bank (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) : Tapes 28 a :=
  ((payload V W U X Z f g h k pv pw pu px).append (FixedHeaderBankCopy.headerBank hs)).append
    (FixedHeaderBankCopy.empty 14)
def bn (hs : Fin 3 → List Bool) : Fin 2 → List Bool := ![hs 1,hs 2]

def parityPlace : Fin (19+9) ≃ Fin 28 where
  toFun := ![2,3,4,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,0,1,5,6,7,8,9,10,11]
  invFun := ![19,20,0,1,2,21,22,23,24,25,26,27,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def earlyPlace : Fin (26+2) ≃ Fin 28 where
  toFun := ![0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,2,3]
  invFun := ![0,1,26,27,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def loadPlace : Fin (21+7) ≃ Fin 28 where
  toFun := ![5,3,6,2,7,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,0,1,4,8,9,10,11]
  invFun := ![21,22,3,1,23,0,2,4,24,25,26,27,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def parityExtra (V W : List Bool) (f g : ℤ → Fin (a+4)) (pv pw : ℤ) (hs : Fin 3 → List Bool) : Tapes 9 a :=
  ⟨![pv,pw,0,0,0,0,0,0,1],![putWord f pv (V.map bitSymbol),putWord g pw (W.map bitSymbol),
    fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,
    RadixZeroFill.encodedBinary (hs 0)]⟩
def earlyExtra (U X : List Bool) (h k : ℤ → Fin (a+4)) (pu px : ℤ) : Tapes 2 a :=
  ⟨![pu,px],![putWord h pu (U.map bitSymbol),putWord k px (X.map bitSymbol)]⟩
def loadExtra (V W Z : List Bool) (f g : ℤ → Fin (a+4)) (pv pw : ℤ) (hs : Fin 3 → List Bool) : Tapes 7 a :=
  ⟨![pv,pw,0,0,0,0,1],![putWord f pv (V.map bitSymbol),putWord g pw (W.map bitSymbol),
    putWord (fun _ => blank) 0 (Z.map bitSymbol),fun _ => blank,fun _ => blank,fun _ => blank,
    RadixZeroFill.encodedBinary (hs 0)]⟩

theorem parity_bank (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) :
    ((CountedPackedParityRun.input (Gather.bank (putWord h pu (U.map bitSymbol))
      (putWord k px (X.map bitSymbol)) (putWord (fun _ => blank) 0 (Z.map bitSymbol)) pu px 0) (bn hs)).append
      (parityExtra V W f g pv pw hs)).reindex parityPlace = bank V W U X Z f g h k pv pw pu px hs := by
  unfold CountedPackedParityRun.input CountedPackedParityRun.caller CountedPackedParityHeaders.input
    parityExtra bank payload bn Gather.bank Tapes.reindex Tapes.append parityPlace
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem early_bank (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) :
    ((CountedPackedArith.bank (PackedArith.input V W Z f g (fun _ => blank) pv pw 0 0 0 0 0 0 0) hs).append
      (earlyExtra U X h k pu px)).reindex earlyPlace = bank V W U X Z f g h k pv pw pu px hs := by
  unfold CountedPackedArith.bank CountedPackedArith.tail PackedArith.input PackedArith.bank
    earlyExtra bank payload Tapes.reindex Tapes.append earlyPlace
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem load_bank (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) :
    ((CountedPackedControlLoadRun.input (CountedPackedControlLoadRun.payload U X k h pu px) (bn hs)).append
      (loadExtra V W Z f g pv pw hs)).reindex loadPlace = bank V W U X Z f g h k pv pw pu px hs := by
  unfold CountedPackedControlLoadRun.input CountedPackedControlLoadLine.input CountedPackedControlLoadLine.caller
    CountedPackedControlLoadHeaders.input CountedPackedControlLoadRun.payload PackedLine.bank
    loadExtra bank payload bn Tapes.reindex Tapes.append loadPlace
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def parity (a : ℕ) := reindex (extend (CountedPackedParityRun.program a) 9) parityPlace
def early (a : ℕ) := reindex (extend (CountedPackedReusable.forwardProgram a) 2) earlyPlace
def load (a : ℕ) := reindex (extend (CountedPackedControlLoadRun.program ColumnTransducer.addRule a) 7) loadPlace
def unload (a : ℕ) := reindex (extend (CountedPackedControlLoadRun.program ColumnTransducer.subRule a) 7) loadPlace
def clear (a : ℕ) := WordBankCleanup.clearProgram (4 : Fin 28) (by decide) a
def program (a : ℕ) := seq (seq (seq (seq (seq (seq (seq (parity a) (early a))
  (clear a)) (load a)) (parity a)) (early a)) (clear a)) (unload a)

theorem bn_values (q b n : ℕ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b n i) :
    ∀ i, Counter.value (bn hs i) = CountedPackedParityHeaders.originalValues b n i := by
  intro i; fin_cases i
  · exact hv 1
  · exact hv 2

theorem bn_canonical (hs : Fin 3 → List Bool) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (bn hs i) := by
  intro i; fin_cases i
  · exact hc 1
  · exact hc 2

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W U X Z : List Bool)
variable (f g h k : ℤ → Fin (a+4)) (pv pw pu px : ℤ) (hs : Fin 3 → List Bool)

include hb in
theorem parity_hoare
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hU : U.length = X.length*b)
    (hh : h (pu-1) = blank) (hk : k (px-1) = blank) :
    HoareTime (parity a) (fun v => v = bank V W U X [] f g h k pv pw pu px hs)
      (fun v => v = bank V W U X (CountedPackedParityRun.parities b U X.length) f g h k pv pw pu px hs)
      (330*((X.length+1)*(b+2))) := by
  have hp := hoare_place (CountedPackedParityRun.runs b hb U X h k pu px 0 (bn hs)
    (bn_values q b X.length hs hv) (bn_canonical hs hc) hU hh hk)
    parityPlace (parityExtra V W f g pv pw hs)
  have hpre := parity_bank V W U X [] f g h k pv pw pu px hs
  simp only [List.map_nil,putWord] at hpre
  rw [hpre,parity_bank] at hp
  exact hp

theorem early_hoare
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hZ : Z.length=X.length)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank) :
    HoareTime (early a) (fun v => v = bank V W U X Z f g h k pv pw pu px hs)
      (fun v => v = bank (PackedArith.v2 q b hb hbq V W Z) (PackedArith.w2 q b hb hbq V W Z)
        U X Z f g h k pv pw pu px hs) (2720*((X.length+1)*(q+b+1))) := by
  have hp := hoare_place (CountedPackedReusable.forward_hoare q b hb hbq V W Z f g
    (fun _ => blank) pv pw 0 0 0 0 0 0 0 hs
    (by simpa only [hZ] using hV) (by simpa only [hZ] using hW) hf hf' hg hg' rfl
    (by intro i; simpa only [hZ] using hv i) hc) earlyPlace (earlyExtra U X h k pu px)
  rw [early_bank,early_bank] at hp
  simp only [hZ] at hp
  exact hp

theorem clear_hoare :
    HoareTime (clear a) (fun v => v = bank V W U X Z f g h k pv pw pu px hs)
      (fun v => v = bank V W U X [] f g h k pv pw pu px hs) (2*Z.length+3) := by
  have hp := WordBankCleanup.clear_hoare (bank V W U X Z f g h k pv pw pu px hs)
    (4 : Fin 28) (by decide) (Z.map bitSymbol) (ReturnOrigin.bits_nonblank Z) rfl
  refine hp.consequence (fun _ h => h) ?_ (by simp)
  intro v hv
  rw [hv]
  unfold WordBankCleanup.write bank payload Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem control_hoare {s : ℕ} (R : ColumnTransducer.Rule s)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hU : U.length=X.length*b)
    (hh : h (pu-1) = blank) (hh' : h (pu+U.length) = blank)
    (hk : k (px-1) = blank) (hk' : k (px+X.length) = blank) :
    HoareTime (reindex (extend (CountedPackedControlLoadRun.program R a) 7) loadPlace)
      (fun v => v = bank V W U X Z f g h k pv pw pu px hs)
      (fun v => v = bank V W (CountedPackedControlLoadRun.word R b hb U X) X Z
        f g h k pv pw pu px hs) (380*((X.length+1)*(b+2))) := by
  have hp := hoare_place (CountedPackedControlLoadRun.runs R b hb U X k h pu px (bn hs)
    (bn_values q b X.length hs hv) (bn_canonical hs hc) hU hk hk' hh hh')
    loadPlace (loadExtra V W Z f g pv pw hs)
  rw [load_bank,load_bank] at hp
  exact hp

open CountedPackedLateData

/-- Eight genuine stages share blank metadata, retain the original headers
and controls, and finish with every temporary word and head restored. -/
theorem runs
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank)
    (hh : h (pu-1) = blank) (hh' : h (pu+U.length) = blank)
    (hk : k (px-1) = blank) (hk' : k (px+X.length) = blank) :
    HoareTime (program a) (fun v => v = bank V W U X [] f g h k pv pw pu px hs)
      (fun v => v = bank (target q b hb hbq V W U X) (temp q b hb hbq V W U X)
        (restored b hb U X) X [] f g h k pv pw pu px hs)
      (7000*((X.length+1)*(q+b+1))) := by
  obtain ⟨hfv,hfw,hlu,ht,hw,hu⟩ := CountedPackedLateData.lengths q b hb hbq V W U X hV hW hU
  let Z0 := CountedPackedParityRun.parities b U X.length
  let V1 := firstV q b hb hbq V W U X
  let W1 := firstW q b hb hbq V W U X
  let U1 := loaded b hb U X
  let Z1 := CountedPackedParityRun.parities b U1 X.length
  let V2 := target q b hb hbq V W U X
  let W2 := temp q b hb hbq V W U X
  have hp0 := parity_hoare q b hb V W U X f g h k pv pw pu px hs hv hc hU hh hk
  have he0 := early_hoare q b hb hbq V W U X Z0 f g h k pv pw pu px hs
    hv hc hV hW (by simp [Z0]) hf hf' hg hg'
  have hc0 := clear_hoare V1 W1 U X Z0 f g h k pv pw pu px hs
  have hl := control_hoare q b hb V1 W1 U X [] f g h k pv pw pu px hs
    ColumnTransducer.addRule hv hc hU hh hh' hk hk'
  have hp1 := parity_hoare q b hb V1 W1 U1 X f g h k pv pw pu px hs
    hv hc (hlu.trans hU) hh hk
  have he1 := early_hoare q b hb hbq V1 W1 U1 X Z1 f g h k pv pw pu px hs
    hv hc (hfv.trans hV) (hfw.trans hW) (by simp [Z1]) hf
    (by simpa only [V1,hfv] using hf') hg (by simpa only [W1,hfw] using hg')
  have hc1 := clear_hoare V2 W2 U1 X Z1 f g h k pv pw pu px hs
  have hr := control_hoare q b hb V2 W2 U1 X [] f g h k pv pw pu px hs
    ColumnTransducer.subRule hv hc (hlu.trans hU) hh (by simpa only [U1,hlu] using hh') hk hk'
  have hall := ((((((hp0.seq he0).seq hc0).seq hl).seq hp1).seq he1).seq hc1).seq hr
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  have hs : (X.length+1)*(b+2) ≤ (X.length+1)*(q+b+1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hn : X.length ≤ (X.length+1)*(q+b+1) := by nlinarith
  have hp : 1 ≤ (X.length+1)*(q+b+1) := by nlinarith
  simp only [Z0,Z1,CountedPackedParityRun.parities_length]
  omega

/-- The actual tape assembly realizes the unrestricted packedLate value map. -/
theorem runs_value
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank)
    (hh : h (pu-1) = blank) (hh' : h (pu+U.length) = blank)
    (hk : k (px-1) = blank) (hk' : k (px+X.length) = blank) :
    HoareTime (program a) (fun v => v = bank V W U X [] f g h k pv pw pu px hs)
      (fun v => v = bank (target q b hb hbq V W U X) (temp q b hb hbq V W U X)
        (restored b hb U X) X [] f g h k pv pw pu px hs ∧
        ((Counter.value (target q b hb hbq V W U X) : ℤ),
          (Counter.value (temp q b hb hbq V W U X) : ℤ), (Counter.value (restored b hb U X) : ℤ)) =
            Compact.packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl)
              (Counter.value V) (Counter.value W) (Counter.value U))
      (7000*((X.length+1)*(q+b+1))) := by
  refine (runs q b hb hbq V W U X f g h k pv pw pu px hs hv hc hV hW hU
    hf hf' hg hg' hh hh' hk hk').consequence (fun _ h => h) ?_ (le_refl _)
  intro v hv
  exact ⟨hv,CountedPackedLateData.value_spec q b hb hbq V W U X hV hW hU⟩

include hb hbq in
/-- On the guarded set only the selected target low bits change; both dirty
words, the control word, the original headers, and every private tape are restored. -/
theorem runs_guarded
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank)
    (hh : h (pu-1) = blank) (hh' : h (pu+U.length) = blank)
    (hk : k (px-1) = blank) (hk' : k (px+X.length) = blank)
    (hgood : ∀ d ∈ CountedPackedLateData.states q b V W U X,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    HoareTime (program a) (fun v => v = bank V W U X [] f g h k pv pw pu px hs)
      (fun v => v = bank (List.zipWith xor V (Compact.PowerTwo.toggleMask q X))
        W U X [] f g h k pv pw pu px hs) (7000*((X.length+1)*(q+b+1))) := by
  have hr := runs q b hb hbq V W U X f g h k pv pw pu px hs hv hc hV hW hU
    hf hf' hg hg' hh hh' hk hk'
  obtain ⟨ht,hw,hu⟩ := CountedPackedLateData.guarded_words q b hb hbq V W U X hV hW hU hgood
  rw [ht,hw,hu] at hr
  exact hr

end
end IntegerMultBounds.Machine.CountedPackedLateRun
