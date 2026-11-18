module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy
public import IntegerMultBounds.Machine.FlatCoordinateSchedule
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! Generate the swap prefix and payload width from the row machine's binary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open FlatCoordinateSchedule (bits bits_value bits_canonical)
variable {T Q A : ℕ} {P U : Type}

def swapPrefix (r : Fin 10 ↪ Fin T) (d : ℕ) : Pr P T Q A U :=
  .seq (dimensionPower r d) (Routing.binaryCanonicalProgram (r 2) (r 3))

theorem swapPrefix_exec (body : P → Pr P T Q A U) (r : Fin 10 ↪ Fin T) (d H M : ℕ)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (base : S.R (r 0) = binSyms H M)
    (one : S.R (r 1) = binSyms 1 1) (free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) ∧
      Exec body (swapPrefix r d) (mk v S) n
        (mk z {S with R := Function.update S.R (r 2) ((bits (M^d)).map bitSymbol)}) := by
  obtain ⟨u,n,hu,hn,run⟩ := dimensionPower_exec body d r H 1 M 1 hm (by decide) v S base one free
  simp only [Nat.mul_one] at run
  let D : Stacks T A := {S with R := Function.update S.R (r 2) (binSyms (d*H+1) (M^d))}
  have bound := Nat.pow_le_pow_left hm.le d
  rw [← pow_mul,Nat.mul_comm H d] at bound
  have fits : M^d < 2^(d*H+1) := by rw [pow_succ]; have := Nat.two_pow_pos (d*H); omega
  obtain ⟨cs,z,hc,hv,_,hz,trim⟩ := Routing.binaryCanonical_exec body (r 2) (r 3)
    (r.injective.ne (by decide)) _ _ fits u D (by simp [D])
    (by simp [D,r.injective.eq_iff,free 3 (by decide) (by decide)])
  have eq := BinaryCanonicalData.value_injective cs (bits (M^d)) hc (bits_canonical _) (hv.trans (bits_value _).symm)
  simp only [eq,D,Function.update_idem] at trim
  exact ⟨z,_,hz.trans hu,Nat.add_le_add_right hn _,Exec.seq run trim⟩

theorem swapWidth_exec (body : P → Pr P T Q A U) (src dst tmp work : Fin T)
    (regs : [src,dst,tmp,work].Nodup) (J W : ℕ) (hw : W < 2^J)
    (v : HS T Q A U) (S : Stacks T A) (width : S.R src = binSyms J W)
    (hd : S.R dst = []) (ht : S.R tmp = []) (hs : S.R work = []) :
    ∃ z, z.user = v.user ∧ Exec body (Routing.binaryCanonicalCopyProgram src dst tmp work)
      (mk v S) (10*J+12) (mk z {S with R := Function.update S.R dst ((bits W).map bitSymbol)}) := by
  obtain ⟨cs,z,hc,hv,_,hz,run⟩ := Routing.binaryCanonicalCopy_exec body src dst tmp work regs
    J W hw v S width hd ht hs
  have eq := BinaryCanonicalData.value_injective cs (bits W) hc (bits_canonical _) (hv.trans (bits_value _).symm)
  exact ⟨z,hz,eq ▸ run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
