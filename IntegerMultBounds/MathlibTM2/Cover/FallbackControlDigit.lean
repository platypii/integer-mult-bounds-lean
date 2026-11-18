module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Read an earlier control coordinate from a physical prefix without permuting fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

/-- Keep one result of binary division and clear its companion register. -/
def divide (quotient : Bool) (r : Fin 11 ↪ Fin T) : Pr P T Q A U :=
  .seq (bdivmod (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10))
    (bclear (if quotient then r 3 else r 2))

private theorem divide_exec (body : P → Pr P T Q A U) (q : Bool) (r : Fin 11 ↪ Fin T)
    (L K x y : ℕ) (hx : x < 2^L) (hy : y < 2^K) (pos : 0 < y)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R (r 0) = binSyms L x)
    (hb : S.R (r 1) = binSyms K y) (blank : ∀ i : Fin 11, 2 ≤ i → i < 10 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ L*(12*K+35)+20*K+38+2*(if q then K else L) ∧
      Exec body (divide q r) (mk v S) n (mk z {S with
        R := Function.update S.R
          (if q then r 2 else r 3) (if q then binSyms L (x/y) else binSyms K (x%y))}) := by
  obtain ⟨u,n,hu,hn,he⟩ := bdivmod_exec body (a := r 0) (b := r 1) (q := r 2) (r := r 3)
    (bw := r 4) (rr := r 5) (t := r 6) (tx := r 7) (ty := r 8) (tz := r 9) (cy := r 10)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    hx hy pos v S ha hb (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide))
    (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide))
    (blank _ (by decide) (by decide)) (blank _ (by decide) (by decide))
  have h2 := blank 2 (by decide) (by decide)
  have h3 := blank 3 (by decide) (by decide)
  simp only [h2,h3,List.append_nil] at he
  let D : Stacks T A := {S with
    R := Function.update (Function.update S.R (r 2) (binSyms L (x/y)))
      (r 3) (binSyms K (x%y))}
  let k := if q then r 3 else r 2
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body k u D
  refine ⟨z,n+(2*(D.R k).length+2),hz.trans hu,?_,?_⟩
  · cases q <;> simp [D,k,r.injective.eq_iff,length_binSyms] <;> omega
  · have final : Function.update D.R k [] = Function.update S.R
          (if q then r 2 else r 3) (if q then binSyms L (x/y) else binSyms K (x%y)) := by
      funext j
      cases q <;> by_cases h : j = r 2 <;> by_cases h' : j = r 3 <;>
        simp_all [D,k,r.injective.eq_iff]
    simpa only [divide,D,final] using Exec.seq he clear

def quotientPorts : Fin 11 ↪ Fin 13 := Fin.castLEEmb (by decide)
def residuePorts : Fin 11 ↪ Fin 13 :=
  ⟨![2,11,12,3,4,5,6,7,8,9,10],by decide⟩

def controlDigit (r : Fin 13 ↪ Fin T) : Pr P T Q A U :=
  .seq (divide true (quotientPorts.trans r))
    (.seq (divide false (residuePorts.trans r)) (bclear (r 2)))

theorem controlDigit_exec (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (L K H x stride M : ℕ) (hx : x < 2^L) (hs : stride < 2^K) (hm : M < 2^H)
    (ps : 0 < stride) (pm : 0 < M) (v : HS T Q A U) (S : Stacks T A)
    (prefixWord : S.R (r 0) = binSyms L x) (gap : S.R (r 1) = binSyms K stride)
    (modulus : S.R (r 11) = binSyms H M)
    (blank : ∀ i : Fin 13, 2 ≤ i → i ≠ 11 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ L*(12*(K+H)+74)+22*K+20*H+78 ∧
      Exec body (controlDigit r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 3) (binSyms H (x/stride%M))}) := by
  obtain ⟨u,n,hu,hn,first⟩ := divide_exec body true (quotientPorts.trans r) L K x stride
    hx hs ps v S prefixWord gap (fun i hi hj => blank (quotientPorts i) hi (by
      intro h; have := congrArg Fin.val h; change i.val = 11 at this; omega))
  let D : Stacks T A := {S with R := Function.update S.R (r 2) (binSyms L (x/stride))}
  have free (i : Fin 11) (hi : 2 ≤ i) (hj : i < 10) : D.R (r (residuePorts i)) = [] := by
    have facts : ∀ i : Fin 11, 2 ≤ i → i < 10 →
        2 ≤ residuePorts i ∧ residuePorts i ≠ 11 ∧ residuePorts i ≠ 2 := by decide
    obtain ⟨ha,hb,hc⟩ := facts i hi hj
    simpa [D,Function.update_of_ne (r.injective.ne hc)] using blank _ ha hb
  obtain ⟨w,m,hw,hm',second⟩ := divide_exec body false (residuePorts.trans r) L H (x/stride) M
    ((Nat.div_le_self _ _).trans_lt hx) hm pm u D (by change D.R (r 2) = _; simp [D])
    (by change D.R (r 11) = _; simpa [D,r.injective.eq_iff] using modulus) free
  let E : Stacks T A := {D with R := Function.update D.R (r 3) (binSyms H (x/stride%M))}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 2) w E
  have len : (E.R (r 2)).length = L := by simp [E,D,r.injective.eq_iff,length_binSyms]
  have final : Function.update E.R (r 2) [] = Function.update S.R (r 3) (binSyms H (x/stride%M)) := by
    funext j
    by_cases h : j = r 2 <;> by_cases h' : j = r 3 <;> simp_all [E,D,r.injective.eq_iff,blank 2 (by decide) (by decide)]
  rw [len,final] at clear
  refine ⟨z,n+(m+(2*L+2)),hz.trans (hw.trans hu),?_,Exec.seq first (Exec.seq second clear)⟩
  simp only [Bool.false_eq_true, ite_false, ite_true] at hn hm'
  nlinarith only [hn,hm']

/-- For an ordered target and control the computed register contains the
coordinate of the original row vector, for any number of intervening fields. -/
theorem earlierControl_exec {d M : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (t k : Fin d) (hk : k < t) (x : Fin d → ZMod M) (L K H : ℕ)
    (hp : FlatCoordinateLayout.prefixIndex x t < 2^L) (hs : M^(t.val-1-k.val) < 2^K)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (prefixWord : S.R (r 0) = binSyms L (FlatCoordinateLayout.prefixIndex x t))
    (gap : S.R (r 1) = binSyms K (M^(t.val-1-k.val))) (modulus : S.R (r 11) = binSyms H M)
    (blank : ∀ i : Fin 13, 2 ≤ i → i ≠ 11 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ L*(12*(K+H)+74)+22*K+20*H+78 ∧
      Exec body (controlDigit r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 3) (binSyms H (x k).val)}) := by
  simpa only [FlatCoordinateLayout.earlier_control x t k hk] using
    controlDigit_exec body r L K H _ _ M hp hs hm (pow_pos (NeZero.pos M) _) (NeZero.pos M)
      v S prefixWord gap modulus blank

end IntegerMultBounds.MathlibTM2.Cover.Fallback
