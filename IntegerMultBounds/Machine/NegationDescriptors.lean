import IntegerMultBounds.Machine.TranslationDescriptors
import IntegerMultBounds.Machine.BinaryOneInit

/-! Literal construction of canonical coordinate-negation metadata. The fixed
program writes its own constant one and derives both tail volume and tail count;
no precomputed difference or tail descriptor is supplied. -/
namespace IntegerMultBounds.Machine.NegationDescriptors

open CountedCopyReuse (empty binary)

private def one (f : ℤ → Fin 4) (r : ℤ) : Tapes 1 0 := ⟨fun _ => r,fun _ => f⟩

private def uninitialized (bs qs : List Bool) : Tapes 10 0 :=
  ⟨Function.update (TranslationDescriptors.initial bs qs []).head 8 0,
   Function.update (TranslationDescriptors.initial bs qs []).tape 8 (fun _ => blank)⟩

/-- Only canonical B and Q are supplied; the one and all derived words start blank. -/
def initial (bs qs : List Bool) : Tapes 11 0 :=
  (uninitialized bs qs).append (one (fun _ => blank) 0)

private def initialized (bs qs : List Bool) : Tapes 11 0 :=
  (TranslationDescriptors.initial bs qs [true]).append (one (fun _ => blank) 0)

private def bankAt (ds : Fin 3 → List Bool) (bs qs diff : List Bool)
    (tail : ℤ → Fin 4) (r : ℤ) : Tapes 11 0 :=
  (TranslationDescriptors.bank ds bs qs [true] (binary diff) 1).append (one tail r)

/-- Output slots 1 and 10 contain the canonical tail volume and tail count.
Slots 2, 3, 8, 9 retain the other generated lengths, one, and padded difference. -/
def bank (ds : Fin 3 → List Bool) (bs qs diff tail : List Bool) : Tapes 11 0 :=
  bankAt ds bs qs diff (binary tail) 1

private def onePlacement : Fin (1+10) ≃ Fin 11 := Equiv.swap 0 8

def oneProgram : Program 11 3 0 := Placement.placed BinaryOneInit.program onePlacement

private theorem one_hoare (bs qs : List Bool) :
    HoareTime oneProgram (fun v => v = initial bs qs) (fun v => v = initialized bs qs) 2 := by
  have ha : Placement.active onePlacement (initial bs qs) = BinaryOneInit.initial := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he : Placement.extra onePlacement (initial bs qs) = Placement.extra onePlacement (initialized bs qs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf : Placement.active onePlacement (initialized bs qs) = BinaryOneInit.finalBank := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at BinaryOneInit.init_hoare onePlacement (initial bs qs) ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,he]
  simpa only [hf] using Placement.view onePlacement (initialized bs qs)

private def marked (v : Tapes 11 0) : Tapes 11 0 :=
  ⟨Function.update v.head 10 1,Function.update v.tape 10 empty⟩

/-- Install the tail-count output's sentinel after translation metadata synthesis. -/
def markerProgram : Program 11 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if i = 10 then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem marker_hoare (v : Tapes 11 0) (hh : v.head 10 = 0) (ht : v.tape 10 = fun _ => blank) :
    HoareTime markerProgram (fun w => w = v) (fun w => w = marked v) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(marked v).head,(marked v).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      by_cases hi : i = 10 <;> simp [hi,marked,hh,Move.offset]
    · funext i z
      by_cases hi : i = 10
      · subst i
        simp [marked,hh,ht,empty]
      · by_cases hz : z = v.head i <;> simp [hi,marked,hz]
  · simp [step,markerProgram]

private theorem marked_bank (ds : Fin 3 → List Bool) (bs qs diff : List Bool) :
    marked (bankAt ds bs qs diff (fun _ => blank) 0) = bank ds bs qs diff [] := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The six active product tapes are spare, tail count, B clock, one,
outer clock, and padded difference, sharing both emptied translation clocks. -/
def productPlacement : Fin (6+5) ≃ Fin 11 :=
  ((((Equiv.swap 1 10).trans (Equiv.swap 2 4)).trans (Equiv.swap 3 8)).trans
    (Equiv.swap 5 9)).trans (Equiv.swap 2 6)

def productProgram : Program 11 35 0 :=
  Placement.placed (TranslationProduct.program (0 : Fin 1)) productPlacement

private theorem active_product (ds : Fin 3 → List Bool) (bs qs diff tail : List Bool) :
    Placement.active productPlacement (bank ds bs qs diff tail) =
      TranslationProduct.bank (fun _ : Fin 1 => tail) [true] diff := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace_product (ds : Fin 3 → List Bool) (bs qs diff tail tail' : List Bool) :
    Placement.replace productPlacement (bank ds bs qs diff tail)
      (TranslationProduct.bank (fun _ : Fin 1 => tail') [true] diff) = bank ds bs qs diff tail' := by
  have he : Placement.extra productPlacement (bank ds bs qs diff tail) =
      Placement.extra productPlacement (bank ds bs qs diff tail') := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [Placement.replace,he]
  simpa only [active_product] using Placement.view productPlacement (bank ds bs qs diff tail')

/-- Canonical physical size of the nonzero-coordinate tail. -/
def tailVolume (Q B : ℕ) : List Bool := TranslationDescriptors.descriptors Q 1 B 0

theorem tailVolume_value (Q B : ℕ) : Counter.value (tailVolume Q B) = (Q-1)*B :=
  (TranslationDescriptors.descriptor_values Q 1 B).1

theorem tailVolume_canonical (Q B : ℕ) : GrowingCounterData.Canonical (tailVolume Q B) :=
  TranslationDescriptors.descriptors_canonical Q 1 B 0

theorem bank_volume (ds : Fin 3 → List Bool) (bs qs diff tail : List Bool) :
    (bank ds bs qs diff tail).head 1 = 1 ∧
      (bank ds bs qs diff tail).tape 1 = binary (ds 0) := ⟨rfl,rfl⟩

theorem bank_count (ds : Fin 3 → List Bool) (bs qs diff tail : List Bool) :
    (bank ds bs qs diff tail).head 10 = 1 ∧
      (bank ds bs qs diff tail).tape 10 = binary tail := ⟨rfl,rfl⟩

/-- Canonical Q minus one, independent of any padding in the subtraction output. -/
def tailCount (Q : ℕ) : List Bool := GrowingCounterData.advance (Q-1) []

theorem tailCount_value (Q : ℕ) : Counter.value (tailCount Q) = Q-1 := GrowingCounterData.empty_value _

theorem tailCount_canonical (Q : ℕ) : GrowingCounterData.Canonical (tailCount Q) :=
  GrowingCounterData.advance_canonical _ [] (Or.inl rfl)

private theorem product_hoare (Q : ℕ) (ds : Fin 3 → List Bool) (bs qs diff : List Bool)
    (hd : Counter.value diff = Q-1) (wd : diff.length ≤ Q+1) :
    HoareTime productProgram (fun v => v = bank ds bs qs diff [])
      (fun v => v = bank ds bs qs diff (tailCount Q)) (53*Q+23) := by
  have h := TranslationProduct.product_empty_hoare_bounded (fun _ : Fin 1 => []) 0 rfl [true] diff 1 (Q-1) Q
    (by decide) BinaryOneInit.value_one hd (Nat.sub_le _ _) (by decide) wd
  have hf : Function.update (fun _ : Fin 1 => []) 0 (GrowingCounterData.advance ((Q-1)*1) []) =
      fun _ : Fin 1 => tailCount Q := by
    funext i
    fin_cases i
    simp [tailCount]
  rw [hf] at h
  have hp := Placement.hoare_at h productPlacement (bank ds bs qs diff []) (active_product ds bs qs diff [])
  apply hp.consequence (fun _ h => h) _ (by omega)
  rintro v ⟨w,rfl,rfl⟩
  exact replace_product _ _ _ _ _ _

/-- The entire fixed bootstrap has no size or offset parameter in its control. -/
def program : Program 11 160 0 :=
  seq (seq (seq oneProgram (extend TranslationDescriptors.program 1)) markerProgram) productProgram

/-- Both negation-tail descriptors are canonical, derived from the supplied
Q/B data with every marker, constant write, arithmetic loop and join charged. -/
theorem descriptors_hoare (Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) :
    HoareTime program (fun v => v = initial bs qs)
      (fun v => v = bank (TranslationDescriptors.descriptors Q 1 B) bs qs
        (BinarySubReuse.difference qs [true]) (tailCount Q)) (216*(Q*B)+121) := by
  have hs := TranslationDescriptors.descriptors_hoare Q 1 B hQ hB bs qs [true]
    hb hq BinaryOneInit.value_one cb cq BinaryOneInit.canonical_one
  have he : HoareTime (extend TranslationDescriptors.program 1)
      (fun v => v = initialized bs qs)
      (fun v => v = bankAt (TranslationDescriptors.descriptors Q 1 B) bs qs
        (BinarySubReuse.difference qs [true]) (fun _ => blank) 0) (163*(Q*B)+92) := by
    apply (hs.extend (one (fun _ => blank) 0)).consequence _ _ le_rfl
    · intro v hv
      exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩
      exact hv
  have hm := marker_hoare
    (bankAt (TranslationDescriptors.descriptors Q 1 B) bs qs (BinarySubReuse.difference qs [true]) (fun _ => blank) 0)
    rfl rfl
  rw [marked_bank] at hm
  have hd : Counter.value (BinarySubReuse.difference qs [true]) = Q-1 := by
    rw [BinarySubReuse.difference_value qs [true] (by rw [hq,BinaryOneInit.value_one]; omega),hq,BinaryOneInit.value_one]
  have wd : (BinarySubReuse.difference qs [true]).length ≤ Q+1 := by
    rw [BinarySubReuse.difference_length]
    have h := GrowingCounterData.canonical_width qs cq
    rw [hq] at h
    have := Nat.log2_le_self Q
    exact max_le (by omega) (by simp)
  have hp := product_hoare Q (TranslationDescriptors.descriptors Q 1 B) bs qs _ hd wd
  apply ((((one_hoare bs qs).seq he).seq hm).seq hp).consequence (fun _ h => h) (fun _ h => h) _
  have hQB : Q ≤ Q*B := by nlinarith
  omega

end IntegerMultBounds.Machine.NegationDescriptors
