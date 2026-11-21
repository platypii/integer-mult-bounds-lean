module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Initialize the packed directory's unary row clock from the binary modulus and spectator count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback Stack Host Node

def directoryRowClock {T Q A : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) : Pr P T Q A U :=
  ((dimensionPower r 128).seq (toUnary (r 2) (r 9) (r 3) (r 4) (r 5))).seq (uclear (r 2))

def directoryRowClockTime (H J N : ℕ) : ℕ := dimensionTime H J 128+6*N+13*(128*H+J)+8

def directoryRowClockRate : ℕ := 6+6+128*((12+18)*(128+1)+20+26)+6+13*(128+1)+8

/-- Binary dimension arithmetic and unary conversion together cost a fixed
multiple of the row length for all positive dimensions. -/
theorem directoryRowClockTime_linear {M W : ℕ} (hm : 0 < M) (hw : 0 < W) :
    directoryRowClockTime M.size W.size (M^128*W) ≤ directoryRowClockRate*(M^128*W) := by
  let N := M^128*W
  have powBound (j : ℕ) (hj : j ≤ 128) := Nat.pow_le_pow_right hm hj
  have H : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have J : W.size ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
  have hM : M ≤ M^128 := by simpa only [pow_one] using powBound 1 (by decide)
  have scale := Nat.le_mul_of_pos_right (M^128) hw
  have hH : M.size ≤ N := H.trans (hM.trans scale)
  have hJ : W.size ≤ N := J.trans (Nat.le_mul_of_pos_left W (pow_pos hm _))
  have square : M.size*M.size ≤ N := (Nat.mul_le_mul H H).trans
    ((by simpa only [pow_two] using powBound 2 (by decide) : M*M ≤ M^128).trans scale)
  have cross : M.size*W.size ≤ N := Nat.mul_le_mul (H.trans hM) J
  have positive : 1 ≤ N := Nat.mul_pos (pow_pos hm _) hw
  unfold directoryRowClockTime
  have dim := dimensionTime_le M.size W.size 128
  change _ ≤ directoryRowClockRate*N
  dsimp only [directoryRowClockRate]
  change dimensionTime M.size W.size 128+6*N+13*(128*M.size+W.size)+8 ≤ _
  nlinarith only [dim,hH,hJ,square,cross,positive]

theorem directoryRowClock_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U) (r : Fin 10 ↪ Fin T)
    (M W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms M.size M) (seed : S.R (r 1) = binSyms W.size W)
    (free : ∀ i : Fin 10, 2 ≤ i → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ directoryRowClockTime M.size W.size (M^128*W) ∧
      Exec body (directoryRowClock r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 9) (List.replicate (M^128*W) tick)}) := by
  let N := M^128*W
  let L := 128*M.size+W.size
  let B := {S with R := Function.update S.R (r 2) (binSyms L N)}
  obtain ⟨u,m,user,time,power⟩ := dimensionPower_exec body 128 r M.size W.size M W
    (Nat.lt_size_self _) (Nat.lt_size_self _) v S base seed (fun i hi _ => free i hi)
  have fits : N < 2^L := by
    have h := Nat.pow_le_pow_left (Nat.lt_size_self M).le 128
    rw [← pow_mul,Nat.mul_comm M.size 128] at h
    exact (Nat.mul_le_mul_right W h).trans_lt (by
      rw [show 2^L = 2^(128*M.size)*2^W.size from pow_add ..]
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (Nat.two_pow_pos _))
  have fresh (i : Fin 10) (hi : 2 < i) : B.R (r i) = [] := by
    simp [B,r.injective.eq_iff,ne_of_gt hi,free i hi.le]
  obtain ⟨y,k,hy,price,decode⟩ := toUnary_exec_linear body (a := r 2) (z := r 9) (w := r 3) (t := r 4) (t₂ := r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff]) fits u B (by simp [B])
    (fresh 3 (by decide)) (fresh 4 (by decide)) (fresh 5 (by decide))
  rw [fresh 9 (by decide),List.append_nil] at decode
  let C := {B with R := Function.update B.R (r 9) (List.replicate N tick)}
  obtain ⟨z,hz,clear⟩ := uclear_exec body (r 2) y C
  have length : (C.R (r 2)).length = L := by simp [C,B,r.injective.eq_iff,length_binSyms]
  rw [length] at clear
  refine ⟨z,m+k+(2*L+2),hz.trans (hy.trans user),?_,?_⟩
  · change m+k+(2*L+2) ≤ dimensionTime M.size W.size 128+6*N+13*L+8
    omega
  · apply Exec.seq (Exec.seq power decode)
    have restore : Function.update C.R (r 2) [] =
        Function.update (Function.update B.R (r 2) []) (r 9) (List.replicate N tick) :=
      Function.update_comm (r.injective.ne (by decide : (9 : Fin 10) ≠ 2)) ..
    rw [restore] at clear
    simpa only [B,Function.update_idem,← free 2 (by decide),Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.M6.BitNode
