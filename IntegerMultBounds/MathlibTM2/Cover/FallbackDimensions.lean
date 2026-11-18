module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension

/-! Prepare prefix count, control stride, and suffix block width in one register bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

def extentPorts : Fin 10 ↪ Fin 13 := Fin.castLEEmb (by decide)
def stridePorts : Fin 10 ↪ Fin 13 := ⟨![0,1,10,3,4,5,6,7,8,9],by decide⟩
def blockPorts : Fin 10 ↪ Fin 13 := ⟨![0,11,12,3,4,5,6,7,8,9],by decide⟩

def rowDimensions {d : ℕ} (k t : Fin d) (r : Fin 13 ↪ Fin T) : Pr P T Q A U :=
  .seq (dimensionPower (extentPorts.trans r) t.val)
    (.seq (dimensionPower (stridePorts.trans r) (t.val-1-k.val))
      (dimensionPower (blockPorts.trans r) (d-1-t.val)))

theorem rowDimensions_exec {d : ℕ} (k t : Fin d) (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms H M) (one : S.R (r 1) = binSyms 1 1)
    (width : S.R (r 11) = binSyms J W) (blank : ∀ i : Fin 13, 2 ≤ i → i ≠ 11 → S.R (r i) = []) :
    let g := t.val-1-k.val
    let s := d-1-t.val
    ∃ z n, z.user = v.user ∧ n ≤ dimensionTime H 1 t.val + dimensionTime H 1 g + dimensionTime H J s ∧
      Exec body (rowDimensions k t r) (mk v S) n (mk z {S with
        R := Function.update (Function.update (Function.update S.R (r 2) (binSyms (t.val*H+1) (M^t.val)))
          (r 10) (binSyms (g*H+1) (M^g))) (r 12) (binSyms (s*H+J) (M^s*W))}) := by
  let g := t.val-1-k.val
  let s := d-1-t.val
  have e : ∀ i : Fin 10, 2 ≤ i → i < 9 → 2 ≤ extentPorts i ∧ extentPorts i ≠ 11 := by decide
  obtain ⟨u,n,hu,hn,extent⟩ := dimensionPower_exec body t.val (extentPorts.trans r) H 1 M 1 hm (by decide)
    v S base one (fun i hi hj => blank _ (e i hi hj).1 (e i hi hj).2)
  simp only [Nat.mul_one] at extent
  let D : Stacks T A := {S with R := Function.update S.R (r 2) (binSyms (t.val*H+1) (M^t.val))}
  have keep (i : Fin 13) (hi : i ≠ 2) : D.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne hi) _ _
  have a : ∀ i : Fin 10, 2 ≤ i → i < 9 → 2 ≤ stridePorts i ∧ stridePorts i ≠ 11 ∧ stridePorts i ≠ 2 := by decide
  obtain ⟨w,m,hw',hm',stride⟩ := dimensionPower_exec body g (stridePorts.trans r) H 1 M 1 hm (by decide)
    u D ((keep 0 (by decide)).trans base) ((keep 1 (by decide)).trans one)
    (fun i hi hj => (keep _ (a i hi hj).2.2).trans (blank _ (a i hi hj).1 (a i hi hj).2.1))
  simp only [Nat.mul_one] at stride
  let E : Stacks T A := {D with R := Function.update D.R (r 10) (binSyms (g*H+1) (M^g))}
  have kept (i : Fin 13) (hi : i ≠ 2) (hj : i ≠ 10) : E.R (r i) = S.R (r i) :=
    (Function.update_of_ne (r.injective.ne hj) _ _).trans (keep i hi)
  have b : ∀ i : Fin 10, 2 ≤ i → i < 9 →
      2 ≤ blockPorts i ∧ blockPorts i ≠ 11 ∧ blockPorts i ≠ 2 ∧ blockPorts i ≠ 10 := by decide
  obtain ⟨z,l,hz,hl,block⟩ := dimensionPower_exec body s (blockPorts.trans r) H J M W hm hw
    w E ((kept 0 (by decide) (by decide)).trans base) ((kept 11 (by decide) (by decide)).trans width)
    (fun i hi hj => (kept _ (b i hi hj).2.2.1 (b i hi hj).2.2.2).trans
      (blank _ (b i hi hj).1 (b i hi hj).2.1))
  exact ⟨z,n+(m+l),hz.trans (hw'.trans hu),by dsimp only [s,g] at *; omega,Exec.seq extent (Exec.seq stride block)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
