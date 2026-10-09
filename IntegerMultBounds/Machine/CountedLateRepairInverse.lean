import IntegerMultBounds.Machine.CountedPackedLateRun

/-! Fixed-control reverse execution of the later packed gadget. All stages
use the original three headers and restore their physical private tapes. -/
namespace IntegerMultBounds.Machine.CountedLateRepairInverse
noncomputable section
open CountedPackedLateRun
variable {a : ℕ}

def inverse (a : ℕ) := reindex (extend (CountedPackedReusable.inverseProgram a) 2) earlyPlace

def program (a : ℕ) := seq (seq (seq (seq (seq (seq (seq (load a) (parity a))
  (inverse a)) (clear a)) (unload a)) (parity a)) (inverse a)) (clear a)

theorem inverse_bank (V W U X Z : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) :
    ((CountedPackedArith.bank (PackedInverse.input V W Z f g (fun _ => blank) pv pw 0 0 0 0 0 0 0) hs).append
      (earlyExtra U X h k pu px)).reindex earlyPlace = bank V W U X Z f g h k pv pw pu px hs := by
  exact early_bank V W U X Z f g h k pv pw pu px hs

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W U X Z : List Bool)
variable (f g h k : ℤ → Fin (a+4)) (pv pw pu px : ℤ) (hs : Fin 3 → List Bool)

theorem inverse_hoare
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hZ : Z.length=X.length)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank) :
    HoareTime (inverse a) (fun v => v = bank V W U X Z f g h k pv pw pu px hs)
      (fun v => v = bank (PackedInverse.v q b hb hbq V W Z) (PackedInverse.w q b hb hbq V W Z)
        U X Z f g h k pv pw pu px hs) (2720*((X.length+1)*(q+b+1))) := by
  have hp := hoare_place (CountedPackedReusable.inverse_hoare q b hb hbq V W Z f g
    (fun _ => blank) pv pw 0 0 0 0 0 0 0 hs
    (by simpa only [hZ] using hV) (by simpa only [hZ] using hW) hf hf' hg hg' rfl
    (by intro i; simpa only [hZ] using hv i) hc) earlyPlace (earlyExtra U X h k pu px)
  rw [inverse_bank,inverse_bank] at hp
  simp only [hZ] at hp
  exact hp

theorem control_hoare {s : ℕ} (R : ColumnTransducer.Rule s)
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

def loaded := CountedPackedControlLoadRun.word ColumnTransducer.addRule b hb U X

def firstV := PackedInverse.v q b hb hbq V W
  (CountedPackedParityRun.parities b (loaded b hb U X) X.length)
def firstW := PackedInverse.w q b hb hbq V W
  (CountedPackedParityRun.parities b (loaded b hb U X) X.length)
def restored := CountedPackedControlLoadRun.word ColumnTransducer.subRule b hb (loaded b hb U X) X

def target := PackedInverse.v q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (CountedPackedParityRun.parities b (restored b hb U X) X.length)
def temp := PackedInverse.w q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (CountedPackedParityRun.parities b (restored b hb U X) X.length)

theorem lengths (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    (loaded b hb U X).length=U.length ∧
    (firstV q b hb hbq V W U X).length=V.length ∧
    (firstW q b hb hbq V W U X).length=W.length ∧
    (restored b hb U X).length=U.length ∧
    (target q b hb hbq V W U X).length=V.length ∧
    (temp q b hb hbq V W U X).length=W.length := by
  have hlu := CountedPackedControlLoadRun.word_length ColumnTransducer.addRule b hb U X hU
  have hru := CountedPackedControlLoadRun.word_length ColumnTransducer.subRule b hb
    (loaded b hb U X) X (hlu.trans hU)
  obtain ⟨_,_,_,_,_,_,_,hw,_,hv⟩ := PackedInverse.lengths q b hb hbq V W
    (CountedPackedParityRun.parities b (loaded b hb U X) X.length)
    (by simpa using hV) (by simpa using hW)
  have hfv : (firstV q b hb hbq V W U X).length=V.length := by
    simpa only [firstV,CountedPackedParityRun.parities_length,hV] using hv
  have hfw : (firstW q b hb hbq V W U X).length=W.length := by
    simpa only [firstW,CountedPackedParityRun.parities_length,hW] using hw
  obtain ⟨_,_,_,_,_,_,_,hw',_,hv'⟩ := PackedInverse.lengths q b hb hbq
    (firstV q b hb hbq V W U X) (firstW q b hb hbq V W U X)
    (CountedPackedParityRun.parities b (restored b hb U X) X.length)
    (by simpa only [CountedPackedParityRun.parities_length,hfv] using hV)
    (by simpa only [CountedPackedParityRun.parities_length,hfw] using hW)
  exact ⟨hlu,hfv,hfw,hru.trans hlu,
    by simpa only [target,CountedPackedParityRun.parities_length,hV] using hv',
    by simpa only [temp,CountedPackedParityRun.parities_length,hW] using hw'⟩

/-- Physical modular addition followed by subtraction restores every input
word, including addresses outside the guarded set. -/
theorem restored_word (hU : U.length=X.length*b) : restored b hb U X = U := by
  have hlu := CountedPackedControlLoadRun.word_length ColumnTransducer.addRule b hb U X hU
  have hru := CountedPackedControlLoadRun.word_length ColumnTransducer.subRule b hb
    (loaded b hb U X) X (hlu.trans hU)
  have hl := CountedPackedControlLoadRun.load_value b hb U X hU
  have hr := CountedPackedControlLoadRun.unload_value b hb (loaded b hb U X) X (hlu.trans hU)
  change (Counter.value (loaded b hb U X) : ℤ) = _ at hl
  change (Counter.value (restored b hb U X) : ℤ) = _ at hr
  rw [hl,Compact.PowerTwo.emod_cancel_add,
    Int.emod_eq_of_lt (by positivity) (Compact.PowerTwo.value_lt_blocks U X.length b hU)] at hr
  apply CountedPackedGuarded.word_eq_of_length_value _ _ (hru.trans hlu)
  exact_mod_cast hr

/-- The forward integer map applied to the physically recovered words is
exactly the original address; this is the unrestricted inverse contract. -/
theorem value_spec (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    Compact.packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl)
      (Counter.value (target q b hb hbq V W U X))
      (Counter.value (temp q b hb hbq V W U X)) (Counter.value (restored b hb U X)) =
      ((Counter.value V : ℤ),(Counter.value W : ℤ),(Counter.value U : ℤ)) := by
  obtain ⟨hlu,hfv,hfw,hru,_,_⟩ := lengths q b hb hbq V W U X hV hW hU
  have he1 := Compact.PowerTwo.inverse_value q b hb hbq V W
    (CountedPackedParityRun.parities b (loaded b hb U X) X.length)
    (by simpa using hV) (by simpa using hW)
  rw [CountedPackedParityValue.controls_eq_digit_parities b hb (loaded b hb U X) X.length
    (hlu.trans hU)] at he1
  change Compact.packedEarly _ _ _ (Counter.value (firstV q b hb hbq V W U X))
    (Counter.value (firstW q b hb hbq V W U X)) = _ at he1
  have he0 := Compact.PowerTwo.inverse_value q b hb hbq
    (firstV q b hb hbq V W U X) (firstW q b hb hbq V W U X)
    (CountedPackedParityRun.parities b (restored b hb U X) X.length)
    (by simpa only [CountedPackedParityRun.parities_length,hfv] using hV)
    (by simpa only [CountedPackedParityRun.parities_length,hfw] using hW)
  rw [CountedPackedParityValue.controls_eq_digit_parities b hb (restored b hb U X) X.length
    (hru.trans hU)] at he0
  change Compact.packedEarly _ _ _ (Counter.value (target q b hb hbq V W U X))
    (Counter.value (temp q b hb hbq V W U X)) = _ at he0
  have hl := CountedPackedControlLoadRun.load_value b hb U X hU
  change (Counter.value (loaded b hb U X) : ℤ) = _ at hl
  have hr := CountedPackedControlLoadRun.unload_value b hb (loaded b hb U X) X (hlu.trans hU)
  change (Counter.value (restored b hb U X) : ℤ) = _ at hr
  have hu := restored_word b hb U X hU
  rw [hu] at he0
  unfold Compact.packedLate
  simp only [List.length_map,hu,he0,← hl,he1,← hr]


/-- Reverse the eight real stages, with all parity, arithmetic and header
work tapes blank and all original heads restored at the endpoint. -/
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
  obtain ⟨hlu,hfv,hfw,hru,ht,hw⟩ := lengths q b hb hbq V W U X hV hW hU
  let U1 := loaded b hb U X
  let Z1 := CountedPackedParityRun.parities b U1 X.length
  let V1 := firstV q b hb hbq V W U X
  let W1 := firstW q b hb hbq V W U X
  let U0 := restored b hb U X
  let Z0 := CountedPackedParityRun.parities b U0 X.length
  let V0 := target q b hb hbq V W U X
  let W0 := temp q b hb hbq V W U X
  have hl := control_hoare q b hb V W U X [] f g h k pv pw pu px hs
    ColumnTransducer.addRule hv hc hU hh hh' hk hk'
  have hp1 := parity_hoare q b hb V W U1 X f g h k pv pw pu px hs hv hc (hlu.trans hU) hh hk
  have he1 := inverse_hoare q b hb hbq V W U1 X Z1 f g h k pv pw pu px hs
    hv hc hV hW (by simp [Z1]) hf hf' hg hg'
  have hc1 := clear_hoare V1 W1 U1 X Z1 f g h k pv pw pu px hs
  have hr := control_hoare q b hb V1 W1 U1 X [] f g h k pv pw pu px hs
    ColumnTransducer.subRule hv hc (hlu.trans hU) hh (by simpa only [U1,hlu] using hh') hk hk'
  have hp0 := parity_hoare q b hb V1 W1 U0 X f g h k pv pw pu px hs hv hc (hru.trans hU) hh hk
  have he0 := inverse_hoare q b hb hbq V1 W1 U0 X Z0 f g h k pv pw pu px hs
    hv hc (hfv.trans hV) (hfw.trans hW) (by simp [Z0]) hf
    (by simpa only [V1,hfv] using hf') hg (by simpa only [W1,hfw] using hg')
  have hc0 := clear_hoare V0 W0 U0 X Z0 f g h k pv pw pu px hs
  have hall := ((((((hl.seq hp1).seq he1).seq hc1).seq hr).seq hp0).seq he0).seq hc0
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  have hs : (X.length+1)*(b+2) ≤ (X.length+1)*(q+b+1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hn : X.length ≤ (X.length+1)*(q+b+1) := by nlinarith
  have hp : 1 ≤ (X.length+1)*(q+b+1) := by nlinarith
  simp only [Z0,Z1,CountedPackedParityRun.parities_length]
  omega

/-- The paid physical reverse machine carries its exact unrestricted integer
inverse semantics together with the restored tape endpoint. -/
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
        Compact.packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl)
          (Counter.value (target q b hb hbq V W U X))
          (Counter.value (temp q b hb hbq V W U X)) (Counter.value (restored b hb U X)) =
          ((Counter.value V : ℤ),(Counter.value W : ℤ),(Counter.value U : ℤ)))
      (7000*((X.length+1)*(q+b+1))) := by
  refine (runs q b hb hbq V W U X f g h k pv pw pu px hs hv hc hV hW hU
    hf hf' hg hg' hh hh' hk hk').consequence (fun _ h => h) ?_ (le_refl _)
  intro v hv
  exact ⟨hv,value_spec q b hb hbq V W U X hV hW hU⟩

end
end IntegerMultBounds.Machine.CountedLateRepairInverse
