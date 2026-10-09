import IntegerMultBounds.Machine.RowPaddingExecution
import IntegerMultBounds.Machine.RowPaddingSpanCounts
import IntegerMultBounds.Machine.RowPaddingWord

/-! Paid descriptor construction, physical row padding/cropping, and disposal
of both generated span descriptors. Only the four immutable dimensions are
inputs; no generated span count is supplied to the contract. -/
namespace IntegerMultBounds.Machine.RowPaddingConstructed
noncomputable section

theorem encoded_zero (bs : List Bool) : RadixZeroFill.encodedBinary (q := 0) bs =
    CountedCopyReuse.binary bs := by
  funext z; rfl

private def head : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tape : Option (List Bool) → ℤ → Fin 4
  | none => fun _ => blank
  | some bs => CountedCopyReuse.binary bs

/-- Slots: source, destination, P, R, rounded R, L, generated N and M,
difference scratch, and three work tapes. -/
def bank (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls : List Bool)
    (valid padding : Option (List Bool)) : Tapes 12 0 :=
  ⟨(fun i => match i.val with
      | 0 => p | 1 => q | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1
      | 6 => head valid | 7 => head padding | _ => 0),
    (fun i => match i.val with
      | 0 => source | 1 => dest | 2 => CountedCopyReuse.binary ps
      | 3 => CountedCopyReuse.binary rs | 4 => CountedCopyReuse.binary rps
      | 5 => CountedCopyReuse.binary ls | 6 => tape valid | 7 => tape padding
      | _ => fun _ => blank)⟩

def countPlacement : Fin (9+3) ≃ Fin 12 where
  toFun := fun i => match i.val with
    | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 8 | 4 => 6 | 5 => 7
    | 6 => 9 | 7 => 10 | 8 => 11 | 9 => 0 | 10 => 1 | _ => 2
  invFun := fun i => match i.val with
    | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 0 | 4 => 1 | 5 => 2
    | 6 => 4 | 7 => 5 | 8 => 3 | 9 => 6 | 10 => 7 | _ => 8
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def physicalPlacement : Fin (7+5) ≃ Fin 12 where
  toFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 9 | 3 => 6 | 4 => 7 | 5 => 10
    | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 8 | _ => 11
  invFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 7 | 4 => 8 | 5 => 9
    | 6 => 3 | 7 => 4 | 8 => 10 | 9 => 2 | 10 => 5 | _ => 11
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r 0}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t 0) (small small' : Tapes s 0)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def countProgram : Program 12 97 0 := Placement.placed RowPaddingSpanCounts.program countPlacement
def physicalPadProgram : Program 12 110 0 := Placement.placed RowPaddingExecution.program physicalPlacement
def physicalCropProgram : Program 12 110 0 := Placement.placed RowPaddingExecution.cropProgram physicalPlacement
def cleanupProgram : Program 12 8 0 :=
  seq (BinaryDescriptorCleanupList.oneProgram 6) (BinaryDescriptorCleanupList.oneProgram 7)
def program : Program 12 (97+(110+8)) 0 := seq countProgram (seq physicalPadProgram cleanupProgram)
def cropProgram : Program 12 (97+(110+8)) 0 := seq countProgram (seq physicalCropProgram cleanupProgram)

theorem count_active (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls : List Bool)
    (valid padding : Option (List Bool)) :
    Placement.active countPlacement (bank source dest p q ps rs rps ls valid padding) =
      RowPaddingSpanCounts.bank (q := 0) rs rps ls none valid padding := by
  cases valid <;> cases padding <;>
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem count_extra_index (i : Fin 3) : countPlacement (Fin.natAdd 9 i) = Fin.castAdd 9 i := by
  fin_cases i <;> rfl

theorem count_extra (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls : List Bool)
    (valid padding valid' padding' : Option (List Bool)) :
    Placement.extra countPlacement (bank source dest p q ps rs rps ls valid padding) =
      Placement.extra countPlacement (bank source dest p q ps rs rps ls valid' padding') := by
  apply congrArg₂ Tapes.mk <;> funext i
  · rw [count_extra_index]; fin_cases i <;> rfl
  · rw [count_extra_index]; fin_cases i <;> rfl

theorem physical_active (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls valid padding : List Bool) :
    Placement.active physicalPlacement (bank source dest p q ps rs rps ls (some valid) (some padding)) =
      RowPaddingExecution.clockBank source dest p q valid padding ps (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem physical_extra (source dest source' dest' : ℤ → Fin 4) (p q p' q' : ℤ)
    (ps rs rps ls valid padding : List Bool) :
    Placement.extra physicalPlacement (bank source dest p q ps rs rps ls (some valid) (some padding)) =
      Placement.extra physicalPlacement (bank source' dest' p' q' ps rs rps ls (some valid) (some padding)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem construct_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls : List Bool)
    (R R' L : ℕ) (hr : Counter.value rs = R) (hp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cr : GrowingCounterData.Canonical rs)
    (cp : GrowingCounterData.Canonical rps) (cl : GrowingCounterData.Canonical ls)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime countProgram (fun v => v = bank source dest p q ps rs rps ls none none)
      (fun v => v = bank source dest p q ps rs rps ls
        (some (RowPaddingSpanCounts.validBits R L)) (some (RowPaddingSpanCounts.padBits R R' L)))
      (112*(R'*L)+83) := by
  apply placed_exact countPlacement _ _ _ _ _ _ _
    (RowPaddingSpanCounts.construct_hoare rs rps ls R R' L hr hp hl cr cp cl hR hL)
  · exact count_active _ _ _ _ _ _ _ _ _ _
  · exact count_active _ _ _ _ _ _ _ _ _ _
  · exact count_extra _ _ _ _ _ _ _ _ _ _ _ _

theorem physical_pad_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (ps rs rps ls : List Bool) (R R' L : ℕ)
    (hv : ∀ xs ∈ groups, xs.length = R*L) (hc : Counter.value ps = groups.length)
    (cc : GrowingCounterData.Canonical ps) (hR : R ≤ R') (hRp : 0 < R') (hL : 0 < L) :
    HoareTime physicalPadProgram
      (fun v => v = bank (putWord source p groups.flatten) dest p q ps rs rps ls
        (some (RowPaddingSpanCounts.validBits R L)) (some (RowPaddingSpanCounts.padBits R R' L)))
      (fun v => v = bank (CountedRawFill.filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (RowPaddingStream.padded groups ((R'-R)*L)).flatten) p q ps rs rps ls
        (some (RowPaddingSpanCounts.validBits R L)) (some (RowPaddingSpanCounts.padBits R R' L)))
      (148*groups.length*(R'*L)+53) := by
  have hh := RowPaddingExecution.pad_linear source dest p q groups
    (RowPaddingSpanCounts.validBits R L) (RowPaddingSpanCounts.padBits R R' L) ps
    (by intro xs hx; rw [RowPaddingSpanCounts.valid_value,hv xs hx]) hc
    (RowPaddingSpanCounts.valid_canonical R L) (RowPaddingSpanCounts.pad_canonical R R' L) cc
    (by rw [RowPaddingSpanCounts.span_sum R R' L hR]; exact Nat.mul_pos hRp hL)
  rw [RowPaddingSpanCounts.span_sum R R' L hR,RowPaddingSpanCounts.pad_value] at hh
  apply placed_exact physicalPlacement _ _ _ _ _ _ _ hh
  · exact physical_active _ _ _ _ _ _ _ _ _ _
  · exact physical_active _ _ _ _ _ _ _ _ _ _
  · exact physical_extra _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem physical_crop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (ps rs rps ls : List Bool) (R R' L : ℕ)
    (hv : ∀ xs ∈ groups, xs.length = R*L) (hc : Counter.value ps = groups.length)
    (cc : GrowingCounterData.Canonical ps) (hR : R ≤ R') (hRp : 0 < R') (hL : 0 < L) :
    HoareTime physicalCropProgram
      (fun v => v = bank (putWord source p (RowPaddingStream.padded groups ((R'-R)*L)).flatten)
        dest p q ps rs rps ls (some (RowPaddingSpanCounts.validBits R L))
        (some (RowPaddingSpanCounts.padBits R R' L)))
      (fun v => v = bank (CountedRawFill.filled
        (putWord source p (RowPaddingStream.padded groups ((R'-R)*L)).flatten)
        p (RowPaddingStream.padded groups ((R'-R)*L)).flatten.length blank)
        (putWord dest q groups.flatten) p q ps rs rps ls
        (some (RowPaddingSpanCounts.validBits R L)) (some (RowPaddingSpanCounts.padBits R R' L)))
      (148*groups.length*(R'*L)+53) := by
  have hh := RowPaddingExecution.crop_linear source dest p q groups
    (RowPaddingSpanCounts.validBits R L) (RowPaddingSpanCounts.padBits R R' L) ps
    (by intro xs hx; rw [RowPaddingSpanCounts.valid_value,hv xs hx]) hc
    (RowPaddingSpanCounts.valid_canonical R L) (RowPaddingSpanCounts.pad_canonical R R' L) cc
    (by rw [RowPaddingSpanCounts.span_sum R R' L hR]; exact Nat.mul_pos hRp hL)
  rw [RowPaddingSpanCounts.span_sum R R' L hR,RowPaddingSpanCounts.pad_value] at hh
  apply placed_exact physicalPlacement _ _ _ _ _ _ _ hh
  · exact physical_active _ _ _ _ _ _ _ _ _ _
  · exact physical_active _ _ _ _ _ _ _ _ _ _
  · exact physical_extra _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem cleanup_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (ps rs rps ls valid padding : List Bool) :
    HoareTime cleanupProgram (fun v => v = bank source dest p q ps rs rps ls (some valid) (some padding))
      (fun v => v = bank source dest p q ps rs rps ls none none)
      (2*valid.length+4+1+(2*padding.length+4)) := by
  have h := BinaryDescriptorCleanupList.one_hoare (6 : Fin 12)
    (bank source dest p q ps rs rps ls (some valid) (some padding)) valid
    (by exact (BinaryDescriptorStackRoundtrip.descriptor_encoded valid).trans (encoded_zero valid) |>.symm) rfl
  have he : SharedPlacementAlphabet.setTape (bank source dest p q ps rs rps ls (some valid) (some padding))
      6 (fun _ => blank) 0 = bank source dest p q ps rs rps ls none (some padding) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  have hh := BinaryDescriptorCleanupList.one_hoare (7 : Fin 12)
    (bank source dest p q ps rs rps ls none (some padding)) padding
    (by exact (BinaryDescriptorStackRoundtrip.descriptor_encoded padding).trans (encoded_zero padding) |>.symm) rfl
  have he' : SharedPlacementAlphabet.setTape (bank source dest p q ps rs rps ls none (some padding))
      7 (fun _ => blank) 0 = bank source dest p q ps rs rps ls none none := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he'] at hh
  exact h.seq hh

theorem total_cost (P R R' L : ℕ) (hP : 0 < P) (hR : R ≤ R') (hRp : 0 < R') (hL : 0 < L) :
    112*(R'*L)+83+1+(148*P*(R'*L)+53+1+
      (2*(RowPaddingSpanCounts.validBits R L).length+4+1+
        (2*(RowPaddingSpanCounts.padBits R R' L).length+4))) ≤ 413*P*(R'*L) := by
  have hv := GrowingCounterData.canonical_width _ (RowPaddingSpanCounts.valid_canonical R L)
  have hm := GrowingCounterData.canonical_width _ (RowPaddingSpanCounts.pad_canonical R R' L)
  have hlv := Nat.log2_le_self (Counter.value (RowPaddingSpanCounts.validBits R L))
  have hlm := Nat.log2_le_self (Counter.value (RowPaddingSpanCounts.padBits R R' L))
  have hs := RowPaddingSpanCounts.span_sum R R' L hR
  have hw : (RowPaddingSpanCounts.validBits R L).length+
      (RowPaddingSpanCounts.padBits R R' L).length ≤ R'*L+2 := by omega
  have hp := Nat.le_mul_of_pos_left (R'*L) hP
  have hpv : 0 < P*(R'*L) := Nat.mul_pos hP (Nat.mul_pos hRp hL)
  nlinarith

/-- From immutable dimension descriptors alone, physically synthesize both
span counts, pad all rows, restore both origins and erase generated counts. -/
theorem pad_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (ps rs rps ls : List Bool) (P R R' L : ℕ)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) (hg : groups.length = P)
    (hv : ∀ xs ∈ groups, xs.length = R*L) :
    HoareTime program (fun v => v = bank (putWord source p groups.flatten) dest p q ps rs rps ls none none)
      (fun v => v = bank (CountedRawFill.filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (RowPaddingStream.padded groups ((R'-R)*L)).flatten) p q ps rs rps ls none none)
      (413*P*(R'*L)) := by
  have hRp : 0 < R' := lt_of_lt_of_le hRpos hR
  have h := (construct_hoare (putWord source p groups.flatten) dest p q ps rs rps ls R R' L
    hr hrp hl cr crp cl hR hL).seq
    ((physical_pad_hoare source dest p q groups ps rs rps ls R R' L hv (hp.trans hg.symm) cp hR hRp hL).seq
      (cleanup_hoare _ _ p q ps rs rps ls (RowPaddingSpanCounts.validBits R L)
        (RowPaddingSpanCounts.padBits R R' L)))
  rw [hg] at h
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (total_cost P R R' L hP hR hRp hL)

/-- Physical inverse with the same paid count synthesis and workspace cleanup. -/
theorem crop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (ps rs rps ls : List Bool) (P R R' L : ℕ)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) (hg : groups.length = P)
    (hv : ∀ xs ∈ groups, xs.length = R*L) :
    HoareTime cropProgram
      (fun v => v = bank (putWord source p (RowPaddingStream.padded groups ((R'-R)*L)).flatten)
        dest p q ps rs rps ls none none)
      (fun v => v = bank (CountedRawFill.filled
        (putWord source p (RowPaddingStream.padded groups ((R'-R)*L)).flatten)
        p (RowPaddingStream.padded groups ((R'-R)*L)).flatten.length blank)
        (putWord dest q groups.flatten) p q ps rs rps ls none none)
      (413*P*(R'*L)) := by
  have hRp : 0 < R' := lt_of_lt_of_le hRpos hR
  have h := (construct_hoare (putWord source p (RowPaddingStream.padded groups ((R'-R)*L)).flatten)
    dest p q ps rs rps ls R R' L hr hrp hl cr crp cl hR hL).seq
    ((physical_crop_hoare source dest p q groups ps rs rps ls R R' L hv (hp.trans hg.symm) cp hR hRp hL).seq
      (cleanup_hoare _ _ p q ps rs rps ls (RowPaddingSpanCounts.validBits R L)
        (RowPaddingSpanCounts.padBits R R' L)))
  rw [hg] at h
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (total_cost P R R' L hP hR hRp hL)

theorem padded_word (P R R' L : ℕ) (hR : R ≤ R') (x : Fin (P*R*L) → Fin 4) :
    (RowPaddingStream.padded (RowPaddingWord.groups x) ((R'-R)*L)).flatten =
      List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) x) :=
  (RowPaddingWord.ofFn_pad hR (bitSymbol false) x).symm

/-- Array-level padding has the actual row-major zero-extension endpoint and
uses only preserved dimension descriptors at the machine boundary. -/
theorem pad_array_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R*L) → Fin 4)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime program (fun v => v = bank (putWord source p (List.ofFn x)) dest p q ps rs rps ls none none)
      (fun v => v = bank (CountedRawFill.filled (putWord source p (List.ofFn x)) p (P*R*L) blank)
        (putWord dest q (List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) x)))
        p q ps rs rps ls none none) (413*P*(R'*L)) := by
  have h := pad_hoare source dest p q (RowPaddingWord.groups x) ps rs rps ls P R R' L
    hp hr hrp hl cp cr crp cl hP hRpos hR hL (RowPaddingWord.groups_length x)
    (RowPaddingWord.group_length x)
  simpa only [RowPaddingWord.groups_flatten,padded_word P R R' L hR x,List.length_ofFn] using h

/-- Array-level inverse consumes the literal padded row array and recovers
the original array, including data cells whose symbol is binary zero. -/
theorem crop_array_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (ps rs rps ls : List Bool) (P R R' L : ℕ) (x : Fin (P*R*L) → Fin 4)
    (hp : Counter.value ps = P) (hr : Counter.value rs = R) (hrp : Counter.value rps = R')
    (hl : Counter.value ls = L) (cp : GrowingCounterData.Canonical ps)
    (cr : GrowingCounterData.Canonical rs) (crp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hP : 0 < P) (hRpos : 0 < R)
    (hR : R ≤ R') (hL : 0 < L) :
    HoareTime cropProgram
      (fun v => v = bank (putWord source p (List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) x)))
        dest p q ps rs rps ls none none)
      (fun v => v = bank (CountedRawFill.filled
        (putWord source p (List.ofFn (RecursiveRowPadding.pad R' (bitSymbol false) x))) p (P*R'*L) blank)
        (putWord dest q (List.ofFn x)) p q ps rs rps ls none none) (413*P*(R'*L)) := by
  have h := crop_hoare source dest p q (RowPaddingWord.groups x) ps rs rps ls P R R' L
    hp hr hrp hl cp cr crp cl hP hRpos hR hL (RowPaddingWord.groups_length x)
    (RowPaddingWord.group_length x)
  simpa only [RowPaddingWord.groups_flatten,padded_word P R R' L hR x,List.length_ofFn] using h

end
end IntegerMultBounds.Machine.RowPaddingConstructed
