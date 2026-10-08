import IntegerMultBounds.Machine.CountedLoopAlphabet
import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.Alphabet

/-! Reusable binary-counted loops with arbitrary finite-alphabet bodies. Only the
two dedicated binary control tapes are passed through the alphabet encoding;
all payload/radix symbols remain literal spectators during setup and cleanup.
The loop copies its count once, amortizes real decrements, and restores controls. -/
namespace IntegerMultBounds.Machine.CountedLoopReuseAlphabet

variable {t q a : ℕ}

/-- Canonical first-four-symbol embedding; extra symbols never enter controls. -/
def encoding (a : ℕ) : Alphabet.Encoding 0 a where
  encode := fun x => ⟨x.val,Nat.lt_of_lt_of_le x.isLt (Nat.le_add_left 4 a)⟩
  decode := fun x => if h : x.val < 4 then ⟨x.val,h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

def empty : ℤ → Fin (a+4) := fun j => if j = 0 then separator else blank

def binary (bs : List Bool) : ℤ → Fin (a+4) := CountedLoopAlphabet.putBits empty 1 bs

def controls (clock descriptor : ℤ → Fin (a+4)) (r s : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then r else s,fun i => if i = 0 then clock else descriptor⟩

def bank (v : Tapes t a) (clock descriptor : ℤ → Fin (a+4)) (r s : ℤ) : Tapes (t+2) a :=
  v.append (controls clock descriptor r s)

def one (f : ℤ → Fin (a+4)) (r : ℤ) : Tapes 1 a := ⟨fun _ => r,fun _ => f⟩

theorem encoding_empty : (fun j => (encoding a).encode (CountedCopyReuse.empty j)) = (empty : ℤ → Fin (a+4)) := by
  funext j
  by_cases hj : j = 0 <;> simp [empty,CountedCopyReuse.empty,encoding,hj]
  all_goals rfl

theorem encoding_putBits (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    (fun j => (encoding a).encode (putBits f p bs j)) =
      CountedLoopAlphabet.putBits (fun j => (encoding a).encode (f j)) p bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    funext j
    by_cases hj : j = p
    · subst j
      simp [putBits,CountedLoopAlphabet.putBits,encoding]
      rfl
    · simp only [putBits,CountedLoopAlphabet.putBits,Function.update_of_ne hj]
      exact congrFun (ih (p+1)) j

theorem encoding_binary (bs : List Bool) :
    (fun j => (encoding a).encode (CountedCopyReuse.binary bs j)) = (binary bs : ℤ → Fin (a+4)) := by
  rw [CountedCopyReuse.binary,encoding_putBits,encoding_empty]
  rfl

theorem encoding_controls (clock descriptor : ℤ → Fin 4) (r s : ℤ) :
    Alphabet.mapTapes (encoding a) (CountedLoopReuse.controls clock descriptor r s) =
      controls (fun j => (encoding a).encode (clock j)) (fun j => (encoding a).encode (descriptor j)) r s := by
  unfold Alphabet.mapTapes CountedLoopReuse.controls controls
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem map_exact_hoare {s k : ℕ} {M : Program s k 0} {v w : Tapes s 0} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) :
    HoareTime (Alphabet.program (encoding a) M)
      (fun x => x = Alphabet.mapTapes (encoding a) v) (fun x => x = Alphabet.mapTapes (encoding a) w) cost := by
  apply (Alphabet.map_hoare (encoding a) h).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨original,rfl,rfl⟩; rfl

def prepareControls (a : ℕ) : Program 2 7 a := Alphabet.program (encoding a) CountedLoopReuse.prepareControls
def cleanControls (a : ℕ) : Program 2 4 a := Alphabet.program (encoding a) CountedLoopReuse.cleanControls

theorem prepare_hoare (bs : List Bool) :
    HoareTime (prepareControls a) (fun v => v = controls empty (binary bs) 1 1)
      (fun v => v = controls (binary bs) (binary bs) 1 1) (3*bs.length+8) := by
  have h : HoareTime CountedLoopReuse.prepareControls
      (fun v => v = CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary bs) 1 1)
      (fun v => v = CountedLoopReuse.controls (CountedCopyReuse.binary bs) (CountedCopyReuse.binary bs) 1 1)
      (3*bs.length+8) := by
    rintro v rfl
    obtain ⟨last,hr,hh,hf⟩ := CountedLoopReuse.prepare_exact bs
    exact ⟨3*bs.length+8,last,le_rfl,hr,hh,hf⟩
  have hh := map_exact_hoare (a := a) h
  simpa only [prepareControls,cleanControls,encoding_controls,encoding_empty,encoding_binary] using hh

theorem clean_hoare (cs ds : List Bool) :
    HoareTime (cleanControls a) (fun v => v = controls (binary cs) (binary ds) 1 1)
      (fun v => v = controls empty (binary ds) 1 1) (2*cs.length+4) := by
  have hh := map_exact_hoare (a := a) (CountedLoopReuse.clean_controls_hoare cs ds)
  simpa only [prepareControls,cleanControls,encoding_controls,encoding_empty,encoding_binary] using hh

def controlsProgram {k : ℕ} (M : Program 2 k a) (t : ℕ) : Program (t+2) k a :=
  Placement.placed M (finAddFlip : Fin (2+t) ≃ Fin (t+2))

private theorem active_controls (v : Tapes t a) (w : Tapes 2 a) :
    Placement.active (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) = w := by
  cases w
  simp [Placement.active,Tapes.append,finAddFlip_apply_castAdd]

private theorem extra_controls (v : Tapes t a) (w : Tapes 2 a) :
    Placement.extra (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) = v := by
  cases v
  simp [Placement.extra,Tapes.append,finAddFlip_apply_natAdd]

private theorem controls_hoare {k cost : ℕ} {M : Program 2 k a} {w w' : Tapes 2 a}
    (h : HoareTime M (fun x => x = w) (fun x => x = w') cost) (v : Tapes t a) :
    HoareTime (controlsProgram M t) (fun x => x = v.append w) (fun x => x = v.append w') cost := by
  apply (Placement.hoare_at h (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w) (active_controls v w)).consequence
    (fun _ h => h) _ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  rw [Placement.replace,extra_controls]
  simpa only [active_controls,extra_controls] using
    Placement.view (finAddFlip : Fin (2+t) ≃ Fin (t+2)) (v.append w')

private theorem loop_bank (v : Tapes t a) (cs ds : List Bool) :
    (CountedLoopAlphabet.bank v empty cs).append (one (binary ds) 1) = bank v (binary cs) (binary ds) 1 1 := by
  have hl (i : Fin t) : Fin.castAdd 1 (Fin.castAdd 1 i) = Fin.castAdd 2 i := Fin.ext rfl
  have hc : Fin.castAdd 1 (Fin.natAdd t (0 : Fin 1)) = Fin.natAdd t (0 : Fin 2) := Fin.ext rfl
  have hd : Fin.natAdd (t+1) (0 : Fin 1) = Fin.natAdd t (1 : Fin 2) := Fin.ext (by simp)
  unfold CountedLoopAlphabet.bank bank controls one Tapes.append binary
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left]; simp [hl]
      | right i => fin_cases i; simp only [Fin.addCases_left,Fin.addCases_right]; simp [hc]
    | right i => fin_cases i; simp only [Fin.addCases_right]; simp [hd]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left]; simp [hl]
      | right i => fin_cases i; simp only [Fin.addCases_left,Fin.addCases_right]; simp [hc]
    | right i => fin_cases i; simp only [Fin.addCases_right]; simp [hd]

/-- Only the binary controller is encoded; all original body actions run
unchanged in their original alphabet. -/
def program (M : Program t q a) : Program (t+2) (7+(q+5)+4) a :=
  seq (seq (controlsProgram (prepareControls a) t) (extend (CountedLoopAlphabet.program M) 1))
    (controlsProgram (cleanControls a) t)

/-- Arbitrary-alphabet exact-bank chain with real binary preparation, amortized
countdown, both joins, and cleanup. Foreign body symbols need no invariant or
encoding premise; the body contract alone determines their final contents. -/
theorem loop_hoare (M : Program t q a) (bs : List Bool) (n : ℕ)
    (v : ℕ → Tapes t a) (cost : ℕ → ℕ) (hcount : Counter.value bs = n)
    (hbody : ∀ i < n, HoareTime M (fun w => w = v i) (fun w => w = v (i+1)) (cost i)) :
    HoareTime (program M) (fun w => w = bank (v 0) empty (binary bs) 1 1)
      (fun w => w = bank (v n) empty (binary bs) 1 1)
      ((∑ i ∈ Finset.range n, cost i)+6*n+7*bs.length+16) := by
  have hl := (CountedLoopAlphabet.loop_hoare M empty bs n v cost hcount rfl
    (by simp [empty,show (1 : ℤ)+bs.length ≠ 0 by omega]) hbody).extend (one (binary bs) 1)
  have hl' : HoareTime (extend (CountedLoopAlphabet.program M) 1)
      (fun w => w = bank (v 0) (binary bs) (binary bs) 1 1)
      (fun w => w = bank (v n) (binary (List.replicate bs.length true)) (binary bs) 1 1)
      ((∑ i ∈ Finset.range n, cost i)+6*n+2*bs.length+2) := by
    apply hl.consequence _ _ le_rfl
    · intro w hw
      exact ⟨_,rfl,(loop_bank (v 0) bs bs).trans hw.symm |>.symm⟩
    · rintro w ⟨small,rfl,rfl⟩
      exact loop_bank (v n) (List.replicate bs.length true) bs
  have hp := controls_hoare (prepare_hoare (a := a) bs) (v 0)
  have he := controls_hoare (clean_hoare (a := a) (List.replicate bs.length true) bs) (v n)
  simp only [List.length_replicate] at he
  exact ((hp.seq hl').seq he).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.CountedLoopReuseAlphabet
