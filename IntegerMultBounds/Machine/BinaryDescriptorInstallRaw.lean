import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Physically remove a newly copied descriptor sentinel and return its head
to zero, charging both transitions and the copying-to-cleanup join. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorInstallRaw
open SharedPlacementAlphabet (setTape)
variable {t q : ℕ}

def rawWord (q : ℕ) (xs : List Bool) : ℤ → Fin (q+4) :=
  Function.update (RadixZeroFill.encodedBinary xs) 0 blank

def unmark (q : ℕ) (dst : Fin t) : Program t 3 q where
  tapes_pos := Nat.zero_lt_of_lt dst.isLt
  start := 0
  transition := fun st sy => if st = 0 then
    some (1,fun i => (sy i,if i = dst then .left else .stay))
    else if st = 1 then some (2,fun i => (if i = dst then blank else sy i,.stay))
    else none

theorem unmark_hoare (dst : Fin t) (v : Tapes t q) (hh : v.head dst = 1) :
    HoareTime (unmark q dst) (fun w => w = v)
      (fun w => w = setTape v dst (Function.update (v.tape dst) 0 blank) 0) 2 := by
  let mid : Config t 3 q := ⟨1,Function.update v.head dst 0,v.tape⟩
  let last : Config t 3 q := ⟨2,(setTape v dst (Function.update (v.tape dst) 0 blank) 0).head,
    (setTape v dst (Function.update (v.tape dst) 0 blank) 0).tape⟩
  have hs : step (unmark q dst) (v.start (unmark q dst)) = some mid := by
    simp only [step,unmark,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      by_cases hi : i = dst <;> simp [hi,hh,Move.offset]
    · funext i z
      by_cases hz : z = v.head i <;> simp [hz]
  have ht : step (unmark q dst) mid = some last := by
    simp only [step,unmark,mid,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i
      simp [setTape,Move.offset]
    · funext i z
      by_cases hi : i = dst
      · subst i
        simp [setTape,Function.update_apply]
      · by_cases hz : z = v.head i <;> simp [setTape,hi,hz]
  intro w hw
  subst w
  refine ⟨2,last,le_rfl,?_,?_,rfl⟩
  · change (step (unmark q dst) (v.start (unmark q dst)) >>= run (unmark q dst) 1) = _
    rw [hs]
    exact ht
  · simp [last,step,unmark]

noncomputable def program (q : ℕ) (src dst : Fin t) (hne : src ≠ dst) : Program t 8 q :=
  seq (BinaryDescriptorInstall.program q src dst hne) (unmark q dst)

theorem install_hoare (src dst : Fin t) (hne : src ≠ dst) (v : Tapes t q) (xs : List Bool)
    (hs : v.tape src = RadixZeroFill.encodedBinary xs) (hsh : v.head src = 1)
    (hd : v.tape dst = fun _ => blank) (hdh : v.head dst = 0) :
    HoareTime (program q src dst hne) (fun w => w = v)
      (fun w => w = setTape v dst (rawWord q xs) 0) (2*xs.length+8) := by
  have hh := (BinaryDescriptorInstall.install_hoare src dst hne v xs hs hsh hd hdh).seq
    (unmark_hoare dst (setTape v dst (RadixZeroFill.encodedBinary xs) 1) (by simp [setTape]))
  apply hh.consequence (fun _ h => h) _ (by omega)
  intro w hw
  simpa [setTape,rawWord,Function.update_idem] using hw

end IntegerMultBounds.Machine.BinaryDescriptorInstallRaw
