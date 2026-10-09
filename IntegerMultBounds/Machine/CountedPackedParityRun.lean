import IntegerMultBounds.Machine.CountedPackedParityHeaders
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! Uniform extraction of the low bit of every dirty b-bit digit from its
original b/count headers, with every generated header and clock erased. -/
namespace IntegerMultBounds.Machine.CountedPackedParityRun
noncomputable section
variable {a : ℕ}
open CountedPackedParityHeaders (shape words)

def parities (b : ℕ) (U : List Bool) (n : ℕ) := (List.range n).map fun i => U.getD (i*b) false
@[simp] theorem parities_length (b : ℕ) (U : List Bool) (n : ℕ) : (parities b U n).length = n := by
  simp [parities]
theorem gather_parities (b : ℕ) (hb : 1 ≤ b) (U X : List Bool) (n : ℕ) :
    Gather.gather (fun x _ => x) (shape b hb) U X n = parities b U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Gather.gather,ih]
    simp [parities,List.range_succ,Gather.digitWord,Gather.field,shape]

def source : Fin 2 → Fin 5 := ![3,4]
def caller (payload : Tapes 3 a) (hs : Fin 2 → List Bool) :=
  payload.append (FixedHeaderBankCopy.headerBank hs)
def input (payload : Tapes 3 a) (hs : Fin 2 → List Bool) :=
  (CountedPackedParityHeaders.input (caller payload hs)).append (FixedHeaderBankCopy.empty 6)
def ready (payload : Tapes 3 a) (hs : Fin 2 → List Bool) :=
  (CountedPackedParityHeaders.output (caller payload hs) hs).append (FixedHeaderBankCopy.empty 6)
def tail (hs : Fin 2 → List Bool) : Tapes 16 a :=
  (FixedHeaderBankCopy.headerBank hs).append (FixedHeaderBankCopy.empty 14)

theorem input_eq (payload : Tapes 3 a) (hs : Fin 2 → List Bool) :
    input payload hs = payload.append (tail hs) := by
  unfold input caller CountedPackedParityHeaders.input tail Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def focus : Fin 9 → Fin 13 := ![0,1,2,7,8,9,10,11,12]
theorem focus_injective : Function.Injective focus := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [focus] at h

def setup (a : ℕ) := extend (CountedPackedParityHeaders.program (a := a) source) 6
def gatherProgram (a : ℕ) := CountedGatherOriginalRun.program (a := a) (fun x _ => x) focus focus_injective
def cleanup (a : ℕ) := extend (CountedPackedParityHeaders.cleanup (a := a) (t := 5)) 6
def rewindProgram (a : ℕ) := seq (seq (extend (ReturnOrigin.program (a := a)) 2)
  (reindex (extend ReturnOrigin.program 2) Gather.zPlace))
  (reindex (extend ReturnOrigin.program 2) Gather.tPlace)
def program (a : ℕ) := seq (seq (seq (setup a) (gatherProgram a)) (cleanup a))
  (extend (rewindProgram a) 16)

theorem rewind_hoare (U X Y : List Bool) (f g : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (hf : f (px-1) = blank) (hg : g (pz-1) = blank) :
    HoareTime (rewindProgram a)
      (fun v => v = Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
        (putWord (fun _ => blank) pt (Y.map bitSymbol)) (px+U.length) (pz+X.length) (pt+Y.length))
      (fun v => v = Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
        (putWord (fun _ => blank) pt (Y.map bitSymbol)) px pz pt)
      (U.length+X.length+Y.length+8) := by
  have h0 := hoare_extend_eq (ReturnOrigin.return_hoare_at f px (U.map bitSymbol)
    (ReturnOrigin.bits_nonblank U) hf)
    (⟨fun i => if i = 0 then pz+X.length else pt+Y.length,
      fun i => if i = 0 then putWord g pz (X.map bitSymbol) else putWord (fun _ => blank) pt (Y.map bitSymbol)⟩ : Tapes 2 a)
  change HoareTime (extend ReturnOrigin.program 2)
    (fun v => v = (StepRight.cfg (putWord f px (U.map bitSymbol)) (px+(U.map bitSymbol).length) 0).tapes.append _)
    (fun v => v = (StepRight.cfg (putWord f px (U.map bitSymbol)) px 0).tapes.append _) _ at h0
  rw [Gather.x_bank,Gather.x_bank] at h0
  have h1 := hoare_place (ReturnOrigin.return_hoare_at g pz (X.map bitSymbol)
    (ReturnOrigin.bits_nonblank X) hg) Gather.zPlace
    (⟨fun i => if i = 0 then px else pt+Y.length,
      fun i => if i = 0 then putWord f px (U.map bitSymbol) else putWord (fun _ => blank) pt (Y.map bitSymbol)⟩ : Tapes 2 a)
  change HoareTime (reindex (extend ReturnOrigin.program 2) Gather.zPlace)
    (fun v => v = ((⟨fun _ => pz+(X.map bitSymbol).length,fun _ => putWord g pz (X.map bitSymbol)⟩ : Tapes 1 a).append _).reindex Gather.zPlace)
    (fun v => v = ((⟨fun _ => pz,fun _ => putWord g pz (X.map bitSymbol)⟩ : Tapes 1 a).append _).reindex Gather.zPlace) _ at h1
  rw [Gather.z_bank,Gather.z_bank] at h1
  have h2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pt (Y.map bitSymbol)
    (ReturnOrigin.bits_nonblank Y) rfl) Gather.tPlace
    (⟨fun i => if i = 0 then px else pz,
      fun i => if i = 0 then putWord f px (U.map bitSymbol) else putWord g pz (X.map bitSymbol)⟩ : Tapes 2 a)
  change HoareTime (reindex (extend ReturnOrigin.program 2) Gather.tPlace)
    (fun v => v = ((⟨fun _ => pt+(Y.map bitSymbol).length,fun _ => putWord (fun _ => blank) pt (Y.map bitSymbol)⟩ : Tapes 1 a).append _).reindex Gather.tPlace)
    (fun v => v = ((⟨fun _ => pt,fun _ => putWord (fun _ => blank) pt (Y.map bitSymbol)⟩ : Tapes 1 a).append _).reindex Gather.tPlace) _ at h2
  rw [Gather.t_bank,Gather.t_bank] at h2
  simp only [List.length_map] at h0 h1 h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem source_tapes (payload : Tapes 3 a) (hs : Fin 2 → List Bool) (i : Fin 2) :
    (caller payload hs).tape (source i) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> rfl
theorem source_heads (payload : Tapes 3 a) (hs : Fin 2 → List Bool) (i : Fin 2) :
    (caller payload hs).head (source i) = 1 := by fin_cases i <;> rfl

theorem result_eq (payload : Tapes 3 a) (hs : Fin 2 → List Bool)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) :
    CountedGatherOriginalRun.result (CountedPackedParityHeaders.output (caller payload hs) hs)
      focus target px pz pt = CountedPackedParityHeaders.output
        (caller (Gather.bank (payload.tape 0) (payload.tape 1) target px pz pt) hs) hs := by
  unfold CountedGatherOriginalRun.result SharedPlacementAlphabet.setTape
    CountedPackedParityHeaders.output caller Gather.bank Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem gathers (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (f g : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedParityHeaders.originalValues b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hU : U.length = X.length*b) :
    HoareTime (gatherProgram a)
      (fun v => v = ready (Gather.bank (putWord f px (U.map bitSymbol))
        (putWord g pz (X.map bitSymbol)) (fun _ => blank) px pz pt) hs)
      (fun v => v = ready (Gather.bank (putWord f px (U.map bitSymbol))
        (putWord g pz (X.map bitSymbol))
        (putWord (fun _ => blank) pt ((parities b U X.length).map bitSymbol))
        (px+X.length*b) (pz+X.length) (pt+X.length)) hs)
      (169*((X.length+1)*(b+2))) := by
  let payload := Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
    (fun _ => blank) px pz pt
  have hv6 := CountedPackedParityHeaders.words_values b X.length hb hs hv
  have hc6 := CountedPackedParityHeaders.words_canonical hs hc
  have h := CountedGatherOriginalRun.runs (CountedPackedParityHeaders.output (caller payload hs) hs)
    focus focus_injective (fun x _ => x) (shape b hb) U X f g (fun _ => blank) px pz pt
    (words hs) hv6 hc6
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    rfl rfl rfl rfl rfl rfl (by change X.length*b ≤ U.length; omega)
  rw [result_eq,gather_parities] at h
  simp only [shape,Nat.cast_one,mul_one] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (CountedGatherOriginalRun.cost_linear (shape b hb) X.length (words hs) hv6 hc6)

/-- Original b/count headers are preserved, all fourteen private tapes are
blank again, source and dummy-control words are retained, and every head is restored. -/
theorem runs (b : ℕ) (hb : 1 ≤ b) (U X : List Bool)
    (f g : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedParityHeaders.originalValues b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hU : U.length = X.length*b) (hf : f (px-1) = blank) (hg : g (pz-1) = blank) :
    HoareTime (program a)
      (fun v => v = input (Gather.bank (putWord f px (U.map bitSymbol))
        (putWord g pz (X.map bitSymbol)) (fun _ => blank) px pz pt) hs)
      (fun v => v = input (Gather.bank (putWord f px (U.map bitSymbol))
        (putWord g pz (X.map bitSymbol))
        (putWord (fun _ => blank) pt ((parities b U X.length).map bitSymbol)) px pz pt) hs)
      (330*((X.length+1)*(b+2))) := by
  let payload := Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
    (fun _ => blank) px pz pt
  let Y := parities b U X.length
  let after := Gather.bank (putWord f px (U.map bitSymbol)) (putWord g pz (X.map bitSymbol))
    (putWord (fun _ => blank) pt (Y.map bitSymbol)) (px+X.length*b) (pz+X.length) (pt+X.length)
  have h0 := hoare_extend_eq (CountedPackedParityHeaders.constructs source (caller payload hs)
    b X.length hs hv hc (source_tapes payload hs) (source_heads payload hs)) (FixedHeaderBankCopy.empty 6)
  have h1 := gathers b hb U X f g px pz pt hs hv hc hU
  have h2 := hoare_extend_eq (CountedPackedParityHeaders.cleans (caller after hs)
    b X.length hs hv hc) (FixedHeaderBankCopy.empty 6)
  have h3 := hoare_extend_eq (rewind_hoare U X Y f g px pz pt hf hg) (tail hs)
  rw [← input_eq,← input_eq] at h3
  simp only [hU,Y,parities_length] at h3
  have hall := ((h0.seq h1).seq h2).seq h3
  refine hall.consequence (fun _ h => h) (fun _ h => h) ?_
  have hdim : b+X.length+1 ≤ (X.length+1)*(b+2) := by nlinarith
  have hvol : X.length*b+2*X.length ≤ (X.length+1)*(b+2) := by nlinarith
  have hp : 1 ≤ (X.length+1)*(b+2) := by nlinarith
  omega

end
end IntegerMultBounds.Machine.CountedPackedParityRun
