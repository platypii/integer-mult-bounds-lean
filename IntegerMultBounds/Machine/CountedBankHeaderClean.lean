import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! Paid native-tape rewind and erasure from a retained original length header.
Both generated binary controls start and finish blank; payload heads need not
start at zero. This permits composition immediately after a streaming scan. -/
namespace IntegerMultBounds.Machine.CountedBankHeaderClean
noncomputable section
variable {t a : ℕ}

def rewindProgram (ht : 0<t) (selected : Fin t → Bool) (src : Fin t) :=
  CountedLoopHeaderClean.program (CountedBankReset.rewindCell (a:=a) ht selected) src

def eraseProgram (ht : 0<t) (selected : Fin t → Bool) (src : Fin t) :=
  CountedLoopHeaderClean.program (CountedBankReset.eraseCell (a:=a) ht selected) src

def program (ht : 0<t) (selected : Fin t → Bool) (src : Fin t) :=
  seq (eraseProgram (a:=a) ht selected src) (rewindProgram ht selected src)

theorem rewind_runs (ht : 0<t) (selected : Fin t → Bool) (src : Fin t)
    (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hheader : v.head src=1 ∧ v.tape src=RadixZeroFill.encodedBinary bs)
    (hn : Counter.value bs=n) :
    HoareTime (rewindProgram ht selected src) (fun w => w=CountedLoopHeaderClean.bank v)
      (fun w => w=CountedLoopHeaderClean.bank (CountedBankReset.rewound selected v n))
      (7*n+11*bs.length+35) := by
  have hz : CountedBankReset.rewound selected v 0=v := by
    apply congrArg₂ Tapes.mk
    · funext i; simp
    · rfl
  have hh := CountedLoopHeaderClean.runs (CountedBankReset.rewindCell ht selected) src bs n
    (CountedBankReset.rewound selected v) (fun _ => 1) (by simpa only [hz] using hheader) hn
    (fun i _ => CountedBankReset.rewindCell_hoare ht selected v i)
  simpa only [rewindProgram,hz,CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,
    smul_eq_mul,mul_one,show n+6*n=7*n by omega] using hh

theorem erase_runs (ht : 0<t) (selected : Fin t → Bool) (src : Fin t)
    (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hheader : v.head src=1 ∧ v.tape src=RadixZeroFill.encodedBinary bs)
    (hn : Counter.value bs=n) :
    HoareTime (eraseProgram ht selected src) (fun w => w=CountedLoopHeaderClean.bank v)
      (fun w => w=CountedLoopHeaderClean.bank (CountedBankReset.after selected v n))
      (7*n+11*bs.length+35) := by
  have hz : CountedBankReset.after selected v 0=v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp
  have hh := CountedLoopHeaderClean.runs (CountedBankReset.eraseCell ht selected) src bs n
    (CountedBankReset.after selected v) (fun _ => 1) (by simpa only [hz] using hheader) hn
    (fun i _ => CountedBankReset.eraseCell_hoare ht selected v i)
  simpa only [eraseProgram,hz,CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,
    smul_eq_mul,mul_one,show n+6*n=7*n by omega] using hh

/-- Destructive reset explicitly erases the chosen length and walks back. The
source header is outside the chosen set, so the second loop reads the same data. -/
theorem runs (ht : 0<t) (selected : Fin t → Bool) (src : Fin t)
    (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hsrc : selected src=false)
    (hheader : v.head src=1 ∧ v.tape src=RadixZeroFill.encodedBinary bs)
    (hn : Counter.value bs=n) :
    HoareTime (program ht selected src) (fun w => w=CountedLoopHeaderClean.bank v)
      (fun w => w=CountedLoopHeaderClean.bank (CountedBankReset.restored selected v n))
      (14*n+22*bs.length+71) := by
  have hh := (erase_runs ht selected src v bs n hheader hn).seq
    (rewind_runs ht selected src (CountedBankReset.after selected v n) bs n
      (by simpa [CountedBankReset.after,hsrc] using hheader) hn)
  have he : CountedBankReset.rewound selected (CountedBankReset.after selected v n) n=
      CountedBankReset.restored selected v n := by
    apply congrArg₂ Tapes.mk
    · funext i; cases hi : selected i <;> simp [CountedBankReset.after,hi]
    · rfl
  exact hh.consequence (fun _ h => h) (fun _ h => by simpa only [he] using h) (by omega)

theorem cost_linear (bs : List Bool) (n : ℕ) (hn : Counter.value bs=n)
    (hc : GrowingCounterData.Canonical bs) : 14*n+22*bs.length+71 ≤ 36*n+93 := by
  have hw := GrowingCounterData.canonical_width bs hc
  rw [hn] at hw
  have hl := Nat.log2_le_self n
  omega

end
end IntegerMultBounds.Machine.CountedBankHeaderClean
