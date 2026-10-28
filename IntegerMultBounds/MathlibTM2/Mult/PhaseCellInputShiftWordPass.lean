module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftFits

/-! The fixed source port is converted and restored by one reversible word schedule. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ChirpSt
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def inputShiftSource (restore : Bool) (d : ℕ) (xs : List GaussianInt) : List GaussianInt :=
  if restore then xs.map (fun z => (2 : GaussianInt)^d*z) else xs

def inputShiftResult (restore : Bool) (d : ℕ) (xs : List GaussianInt) : List GaussianInt :=
  if restore then xs else xs.map (fun z => (2 : GaussianInt)^d*z)

def inputShiftWordPass (restore : Bool) : Pr P 303 Q A U :=
  if restore then restoreInputShift 110 4 5 0 1 2 3 6 7 8
  else shiftInto 110 4 110 1 2 9 10 (pairSym A false false)

theorem inputShiftWordPass_exec (hA : 4 ≤ A) (restore : Bool) (p d w : ℕ)
    (hw : p+1+d+5 ≤ w) (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hsrc : S.R 110 = cstream A w (inputShiftSource restore d xs))
    (hheaders : ∀ i, S.R (inputShiftPort i) = List.replicate (inputShiftHeaderValues w d i) tick)
    (hblank : ∀ r ∈ ([3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ xs.length*(20*w+44)+8 ∧
      Exec body (inputShiftWordPass restore) (mk v S) n
        (mk v' {S with R := (Function.update S.R 110 (cstream A w (inputShiftResult restore d xs)))}) := by
  have hc (i : Fin 3) : (S.R (inputShiftPort i)).length = inputShiftHeaderValues w d i := by
    rw [hheaders,List.length_replicate]
  cases restore with
  | false =>
    have he := chirpScale_exec (body := body)
      (show [(110 : Fin 303),4,1,2,9,10].Nodup by decide) w d (by omega) (by omega) xs v S
      (by simpa only [inputShiftSource,Bool.false_eq_true,ite_false] using hsrc)
      (hc 1) (hc 2) (hblank 4 (by decide)) (hblank 9 (by decide)) (hblank 10 (by decide))
    obtain ⟨v',hu,hrun⟩ := he
    refine ⟨v',xs.length*(6*w+4*d+14)+4,hu,?_,?_⟩
    · have hcoef : 6*w+4*d+14 ≤ 20*w+44 := by omega
      have hmul := Nat.mul_le_mul_left xs.length hcoef
      omega
    · simpa only [inputShiftWordPass,inputShiftResult,Bool.false_eq_true,ite_false] using hrun
  | true =>
    have hg : topShiftG 5 0 1 2 3 6 7 8 w d (w-d) S.R := by
      refine ⟨hc 0,hc 1,hc 2,?_,hblank 6 (by decide),hblank 7 (by decide),hblank 8 (by decide),hblank 5 (by decide)⟩
      simp only [hblank 3 (by decide),List.length_nil,Nat.sub_self]
    obtain ⟨v',n,hu,hn,he⟩ := restoreInputShift_exec (body := body) hA
      (show [(110 : Fin 303),4,5,0,1,2,3,6,7,8].Nodup by decide) w d (by omega) xs
      (fun z hz => (inputShift_fits p d w hw z (hxs z hz)).1)
      (fun z hz => (inputShift_fits p d w hw z (hxs z hz)).2) v S
      (by simpa only [inputShiftSource,ite_true] using hsrc) (hblank 4 (by decide)) hg
    exact ⟨v',n,hu,hn,by simpa only [inputShiftWordPass,inputShiftResult,ite_true] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
