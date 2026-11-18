module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalCopy
public import IntegerMultBounds.Machine.FlatCoordinateSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalUnaryHeader
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

/-- Temporarily add one tick before converting the clock to the swap exponent. -/
def swapExponent (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (.act (.push (.rt (r 0)) (fun _ => Node.tick) .done))
    (.seq (unaryBinary (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7))
      (.act (Node.dropTop (r 0) .done)))

theorem swapExponent_exec (body : P → Pr P T Q A U) (r : Fin 8 ↪ Fin T)
    (w : ℕ) (v : HS T Q A U) (S : Stacks T A) (clock : (S.R (r 0)).length = w)
    (empty : ∀ i : Fin 8, i ≠ 0 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 21*(w+1)+12 ∧ Exec body (swapExponent r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 1) ((bits (w+1)).map bitSymbol)}) := by
  let D : Stacks T A := {S with R := Function.update S.R (r 0) (Node.tick :: S.R (r 0))}
  have push : Exec body (.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)) (mk v S) 1 (mk v D) := by
    simpa [D,Action.run,update_rt] using Exec.act (body := body)
      (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk v S)
  have free (i : Fin 8) (hi : i ≠ 0) : D.R (r i) = [] :=
    (Function.update_of_ne (r.injective.ne hi) _ _).trans (empty i hi)
  obtain ⟨z,n,hz,hn,convertClock⟩ := unaryBinary_exec (body := body)
    (src := r 0) (dst := r 1) (a := r 2) (h := r 3) (par := r 4) (bits := r 5) (cnt := r 6) (saved := r 7)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (w+1) v D (by simp [D,clock])
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with h|h|h|h|h|h|h <;> subst k <;> apply free <;> decide)
  let count := w+1
  have canon := Mult.PhaseCellToeplitz.binBits_size_canonical count
  have value := Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self count)
  have eq := BinaryCanonicalData.value_injective _ _ canon (bits_canonical count) (value.trans (bits_value count).symm)
  have word : binSyms (A := A) (Nat.size count) count = (bits count).map bitSymbol := by
    simpa [binSyms,binBits,List.map_ofFn,Function.comp_def] using congrArg (List.map (bitSymbol (a := A))) eq
  change Exec body _ _ _ (mk z {D with R := Function.update D.R (r 1) (binSyms (Nat.size count) count)}) at convertClock
  rw [word] at convertClock
  let E := {D with R := Function.update D.R (r 1) ((bits count).map (bitSymbol (a := A)))}
  have pop := Exec.act (body := body) (Node.dropTop (r 0) .done) (mk z E)
  refine ⟨z,1+(n+1),hz,by omega,Exec.seq push (Exec.seq convertClock ?_)⟩
  have restore (word : List (Fin (A+4))) : Function.update (Function.update S.R (r 1) word) (r 0) (S.R (r 0)) = Function.update S.R (r 1) word := by
    funext i
    by_cases h : i = r 0 <;> simp [h,r.injective.eq_iff]
  simpa [E,D,Node.dropTop,Action.run,update_rt,Function.update_comm (r.injective.ne (by decide : (0 : Fin 8) ≠ 1)),
    r.injective.eq_iff,count,restore] using pop

def swapExponentPorts : Fin 8 ↪ Fin 14 := ⟨![12,13,3,4,5,6,7,8],by decide⟩

def swapRuntimeHeaders (r : Fin 14 ↪ Fin T) (d : ℕ) : Pr P T Q A U :=
  .seq (swapPrefix ((Fin.castLEEmb (by decide)).trans r) d)
    (.seq (Routing.binaryCanonicalCopyProgram (r 10) (r 11) (r 3) (r 4))
      (swapExponent (swapExponentPorts.trans r)))

theorem swapRuntimeHeaders_exec (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (d H J M W w : ℕ) (hm : M < 2^H) (hw : W < 2^J) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms H M) (one : S.R (r 1) = binSyms 1 1)
    (width : S.R (r 10) = binSyms J W) (clock : (S.R (r 12)).length = w)
    (free : ∀ i : Fin 14, (2 ≤ i ∧ i < 9) ∨ i = 11 ∨ i = 13 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) ∧
      Exec body (swapRuntimeHeaders r d) (mk v S) n (mk z {S with R := (Function.update
        (Function.update (Function.update S.R (r 2) ((bits (M^d)).map bitSymbol))
          (r 11) ((bits W).map bitSymbol)) (r 13) ((bits (w+1)).map bitSymbol))}) := by
  let ports : Fin 10 ↪ Fin 14 := Fin.castLEEmb (by decide)
  obtain ⟨u,n,hu,hn,prefixRun⟩ := swapPrefix_exec body (ports.trans r) d H M hm v S base one
    (fun i lo hi => free (ports i) (Or.inl ⟨lo,hi⟩))
  let D : Stacks T A := {S with R := Function.update S.R (r 2) ((bits (M^d)).map bitSymbol)}
  have keep (i : Fin 14) (hi : i ≠ 2) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  obtain ⟨y,hy,widthRun⟩ := swapWidth_exec body (r 10) (r 11) (r 3) (r 4)
    (by simp [List.nodup_cons,r.injective.eq_iff]) J W hw u D ((keep 10 (by decide)).trans width)
    ((keep 11 (by decide)).trans (free _ (by decide))) ((keep 3 (by decide)).trans (free _ (by decide)))
    ((keep 4 (by decide)).trans (free _ (by decide)))
  let E : Stacks T A := {D with R := Function.update D.R (r 11) ((bits W).map bitSymbol)}
  have kept (i : Fin 14) (h : i ≠ 11) (h' : i ≠ 2) : E.R (r i) = S.R (r i) :=
    (Function.update_of_ne (r.injective.ne h) _ _).trans (keep i h')
  obtain ⟨z,m,hz,hm',exponentRun⟩ := swapExponent_exec body (swapExponentPorts.trans r) w y E
    ((congrArg List.length (kept 12 (by decide) (by decide))).trans clock)
    (by intro i hi; fin_cases i <;> first | contradiction | exact (kept _ (by decide) (by decide)).trans (free _ (by decide)))
  exact ⟨z,n+((10*J+12)+m),hz.trans (hy.trans hu),by omega,Exec.seq prefixRun (Exec.seq widthRun exponentRun)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
