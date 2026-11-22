module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepChartEntries
public import IntegerMultBounds.MathlibTM2.M6.BitSweepIntegerEntry

/-! Prepend a reduced rational chart entry using its shared inverse of four. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal

theorem sweepQuarterProduct_writes {P U : Type} {T Q A M : ℕ} [NeZero M] (body : P → Pr P T Q A U)
    (r : Fin 13 ↪ Fin T) (q : ℚ) (adm : q.den.Coprime M) (quarter : ∃ z : ℤ, q = (z : ℚ)/4)
    (inv : ZMod M) (inverse : inv*4 = 1) (H : ℕ) (fits : M < 2^H)
    (ok : Regs T A → Prop) (p : Pr P T Q A U) (cost : ℕ)
    (write : Writes body ok (r 0) p (binSyms H (((4*q).num : ℤ) : ZMod M).val) cost) :
    Writes body (fun R => ok R ∧ R (r 0) = [] ∧ R (r 1) = binSyms H inv.val ∧ R (r 2) = binSyms H M ∧
      ∀ i : Fin 13, 4 ≤ i → i < 12 → R (r i) = []) (r 3)
      (.seq p (.seq (Gate.mul.program r) (bclear (r 0)))) (binSyms H (Swap.Modular.ratMod M q).val)
      (cost+Gate.mul.time H+(2*H+2)) := by
  intro v S ⟨ready,empty,invWord,modWord,free⟩
  let x : ZMod M := (4*q).num
  obtain ⟨u,k,hu,hk,prepare⟩ := write v S ready
  rw [empty,List.append_nil] at prepare
  let B := {S with R := Function.update S.R (r 0) (binSyms H x.val)}
  have keep (i : Fin 13) (hi : i ≠ 0) : B.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  have blank (i : Fin 13) (lo : 4 ≤ i) (hi : i < 12) := (keep i (by omega)).trans (free i lo hi)
  obtain ⟨y,l,hy,hl,mul⟩ := bmodmul_exec body (a := r 0) (b := r 1) (m := r 2) (c := r 3)
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10) (tz := r 11) (cy := r 12)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (by simp) (by simp) (by simp)
    (x.val_lt.trans fits) (inv.val_lt.trans fits) fits (NeZero.pos M) u B (Function.update_self ..)
    ((keep 1 (by decide)).trans invWord) ((keep 2 (by decide)).trans modWord)
    (blank 4 (by decide) (by decide)) (blank 5 (by decide) (by decide)) (blank 6 (by decide) (by decide))
    (blank 7 (by decide) (by decide)) (blank 8 (by decide) (by decide)) (blank 9 (by decide) (by decide))
    (blank 10 (by decide) (by decide)) (blank 11 (by decide) (by decide))
  rw [← ZMod.val_mul,← ratMod_quarter adm quarter inv inverse,keep 3 (by decide)] at mul
  let word := binSyms (A := A) H (Swap.Modular.ratMod M q).val ++ S.R (r 3)
  let F := {B with R := Function.update B.R (r 3) word}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 0) y F
  have len : (F.R (r 0)).length = H := by simp [F,B,r.injective.eq_iff,length_binSyms]
  have final : {F with R := Function.update F.R (r 0) []} = {S with R := Function.update S.R (r 3) word} := by
    congr 1
    funext i
    by_cases h : i = r 0
    · subst i; simp [empty]
    · simp [F,B,Function.update_apply,h]
  rw [final,len] at clear
  have bill : l ≤ Gate.mul.time H := by dsimp [Gate.time]; nlinarith only [hl]
  exact ⟨z,k+(l+(2*H+2)),hz.trans (hy.trans hu),by omega,Exec.seq prepare (Exec.seq mul clear)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
