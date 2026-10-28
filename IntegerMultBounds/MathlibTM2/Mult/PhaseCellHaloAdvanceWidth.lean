module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassLoad

/-! Origin advancement needs geometry bits, independently of coefficient precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloAdvanceWidth (s w : ℕ) : ℕ := Nat.size (s*w+s+w)

theorem haloAdvanceWidth_bounds (s w : ℕ) :
    w < 2^haloAdvanceWidth s w ∧ s < 2^haloAdvanceWidth s w ∧
      s*w < 2^haloAdvanceWidth s w := by
  have h := Nat.lt_size_self (s*w+s+w)
  dsimp only [haloAdvanceWidth]
  omega

theorem haloAdvanceWidth_le (s w : ℕ) : haloAdvanceWidth s w ≤ Nat.size s+Nat.size w := by
  apply Nat.size_le.mpr
  have hs : s+1 ≤ 2^Nat.size s := Nat.lt_size_self s
  have hw : w+1 ≤ 2^Nat.size w := Nat.lt_size_self w
  have h := Nat.mul_le_mul hs hw
  rw [pow_add]
  nlinarith only [h]

/-- One geometry width covers both origin generation and symbol advances. -/
def haloControlWidth (s t band w : ℕ) : ℕ :=
  max (Nat.size (8*(t+1)^2+2*band+8)) (haloAdvanceWidth s w)

theorem haloControlWidth_bounds (s t band w : ℕ) :
    8*(t+1)^2+2*band+8 < 2^haloControlWidth s t band w ∧
    w < 2^haloControlWidth s t band w ∧ s < 2^haloControlWidth s t band w ∧
      s*w < 2^haloControlWidth s t band w := by
  have horigin := (Nat.size_le (m := 8*(t+1)^2+2*band+8)).mp
    (Nat.le_max_left _ (haloAdvanceWidth s w))
  obtain ⟨hw,hs,hvolume⟩ := haloAdvanceWidth_bounds s w
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (Nat.le_max_right (Nat.size (8*(t+1)^2+2*band+8)) (haloAdvanceWidth s w))
  exact ⟨horigin,hw.trans_le hpow,hs.trans_le hpow,hvolume.trans_le hpow⟩

theorem haloControlWidth_le {s t band w : ℕ} (hband : band ≤ t) :
    haloControlWidth s t band w ≤
      max (2*Nat.size (t+1)+5) (Nat.size s+Nat.size w) := by
  have hsmall : Nat.size (8*(t+1)^2+2*band+8) ≤ 2*Nat.size (t+1)+5 := by
    apply Nat.size_le.mpr
    have hsq := Nat.pow_lt_pow_left (Nat.lt_size_self (t+1)) (by decide : 2 ≠ 0)
    have hpow : 2^(2*Nat.size (t+1)+5) = 32*(2^Nat.size (t+1))^2 := by
      rw [pow_add, mul_comm 2 (Nat.size (t+1)), pow_mul]
      ring
    rw [hpow]
    nlinarith only [hsq,hband,Nat.zero_le t]
  exact max_le_max hsmall (haloAdvanceWidth_le s w)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- The actual controller executes at the derived geometry width and restores its inputs. -/
theorem preparedHaloAdvanceControls_compact_exec (w s t band a b L : ℕ)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = haloAdvanceWidth s w) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = haloOriginPackets A (haloAdvanceWidth s w) s t band a b L ++ suffix)
    (hcount : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloAdvanceCost (haloAdvanceWidth s w) s t band a b L w ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91 (haloGatherControls A s t band a b L w ++ S.R 91) := by
  obtain ⟨hwV,hsV,hvolume⟩ := haloAdvanceWidth_bounds s w
  exact preparedHaloAdvanceControls_bounds_exec (body := body)
    (haloAdvanceWidth s w) w s t band a b L hwV hsV hvolume
    hgroup v S suffix hV hw hsrc hcount hblank hfresh

/-- Generate origins at the joint geometry width, releasing the private table bank. -/
theorem preparedHaloClass_compact_exec (s t band a b L w : ℕ)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = haloControlWidth s t band w)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloClassCost s t band a b L (haloControlWidth s t band w) ∧
      Exec body preparedHaloClass (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update S.R 109
        (haloOriginPackets A (haloControlWidth s t band w) s t band a b L ++ S.R 109))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick) := by
  exact preparedHaloClass_width_exec (body := body) (haloControlWidth s t band w)
    s t band a b L (haloControlWidth_bounds s t band w).1
    hs hst hband has hbs hL hLs hA v S hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc
    hV h104 h106 h116 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
