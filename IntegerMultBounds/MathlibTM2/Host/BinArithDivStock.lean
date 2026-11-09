module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDivIterStock
public import IntegerMultBounds.MathlibTM2.Host.EachSymStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth
import Mathlib.Tactic.FinCases

/-! Restoring division shares a linear iteration reserve across all dividend bits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

theorem bdivmod_exec_within {a b q r bw rr t tx ty tz cy : Fin T}
    (hreg : [a, b, q, r, bw, rr, t, tx, ty, tz].Nodup) (hcr : cy ≠ rr) (hcb : cy ≠ bw)
    {La Lb x y : ℕ} (hx : x < 2 ^ La) (hy : y < 2 ^ Lb) (hy0 : 0 < y) (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms La x) (hb : S.R b = binSyms Lb y) (hbw : S.R bw = [])
    (hrr : S.R rr = []) (ht : S.R t = []) (htx : S.R tx = []) (hty : S.R ty = [])
    (htz : S.R tz = []) (depth : ℕ) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ La * (12 * Lb + 35) + 20 * Lb + 36 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (La+200*(Lb+1)+200)) depth (bdivmod a b q r bw rr t tx ty tz cy) (mk v S) m
        (mk v' { S with
          R := Function.update (Function.update S.R q (binSyms La (x / y) ++ S.R q)) r
            (binSyms Lb (x % y) ++ S.R r) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set W := Lb + 1 with hW
  -- `bw := b` with one high zero
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body (a := b) (c := bw) (t₁ := tx) (t₂ := ty)
    (by regs_nodup) v S htx hty
  rw [hb, hbw, List.append_nil, length_binSyms] at he₁
  set R₁ := Function.update S.R bw (binSyms Lb y) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := bpad1_exec body (a := bw) (t := tx) ‹bw ≠ tx› hy v₁ { S with R := R₁ }
    (by simp [hR₁]) (by simp [hR₁, Function.update_of_ne ‹bw ≠ tx›.symm, htx])
  set R₂ := Function.update R₁ bw (binSyms W y) with hR₂
  -- `rr := W` zeros
  obtain ⟨v₃, hu₃, he₃⟩ := bzero_exec body (wR := bw) (c := rr) (t := tx) (by regs_nodup) v₂
    { S with R := R₂ } (by simp [hR₂, hR₁, Function.update_of_ne ‹bw ≠ tx›.symm, htx])
  have h2rr : R₂ rr = [] := by
    simp [hR₂, hR₁, Function.update_of_ne ‹bw ≠ rr›.symm, hrr]
  dsimp only at he₃
  rw [h2rr, List.append_nil, show R₂ bw = binSyms W y by simp [hR₂], length_binSyms] at he₃
  set R₃ := Function.update R₂ rr (binSyms W 0) with hR₃
  -- the dividend, most significant bit on top
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body a t ‹a ≠ t› id v₃ { S with R := R₃ }
  have h3a : R₃ a = binSyms La x := by
    simp [hR₃, hR₂, hR₁, Function.update_of_ne ‹a ≠ rr›, Function.update_of_ne ‹a ≠ bw›, ha]
  have h3t : R₃ t = [] := by
    simp [hR₃, hR₂, hR₁, Function.update_of_ne ‹rr ≠ t›.symm, Function.update_of_ne ‹bw ≠ t›.symm, ht]
  dsimp only at he₄
  rw [h3a, length_binSyms] at he₄
  set R₄ := movedR R₃ a t id (binSyms La x) with hR₄
  have h4t : R₄ t = (binSyms La x).reverse := by simp [hR₄, movedR, h3t]
  have h4a : R₄ a = [] := by simp [hR₄, movedR, Function.update_of_ne ‹a ≠ t›]
  have h4 : ∀ k, k ≠ a → k ≠ t → k ≠ rr → k ≠ bw → R₄ k = S.R k := by
    intro k h1 h2 h3 h4
    simp only [hR₄, hR₃, hR₂, hR₁, movedR, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  have h4rr : R₄ rr = binSyms W 0 := by
    simp [hR₄, hR₃, movedR, Function.update_of_ne ‹a ≠ rr›.symm, Function.update_of_ne ‹rr ≠ t›]
  have h4bw : R₄ bw = binSyms W y := by
    simp [hR₄, hR₃, hR₂, movedR, Function.update_of_ne ‹a ≠ bw›.symm,
      Function.update_of_ne ‹bw ≠ t›, Function.update_of_ne ‹bw ≠ rr›]
  -- the division loop
  let hi : ℕ → ℕ := fun j => x / 2 ^ (La - j)
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update (Function.update R₄ rr (binSyms W (hi j % y))) q
      (binSyms j (hi j / y) ++ S.R q)
  have hp : SymStockSpec (body := body) (divIter rr bw q tx ty tz cy) t a (R₄ t) Ψ (12 * W + 18) := by
    intro j hj w S' hsym hS'
    rw [h4t, List.length_reverse, length_binSyms] at hj
    have hbit : (R₄ t)[j] = bitSymbol (x.testBit (La - 1 - j)) := by
      simp only [h4t, getElem_reverse_binSyms]
    have hhi : hi (j + 1) = 2 * hi j + (x.testBit (La - 1 - j)).toNat := by
      simp only [hi]
      rw [show La - (j + 1) = La - 1 - j by omega, div_two_pow_eq x (La - 1 - j),
        show La - 1 - j + 1 = La - j by omega]
    have hρ : hi j % y < y := Nat.mod_lt _ hy0
    have hpow : 2 ^ W = 2 * 2 ^ Lb := by rw [hW, pow_succ]; ring
    have hbitle := Bool.toNat_le (x.testBit (La - 1 - j))
    have hSq : S'.R q = Ψ j q := hS' q ‹q ≠ t› ‹a ≠ q›.symm
    obtain ⟨w', hw', htrace, hstock⟩ := divIter_exec_within (body := body) (rr := rr) (bw := bw) (q := q) (tx := tx) (ty := ty)
      (tz := tz) (by regs_nodup) hcr hcb (W := W) (ρ := hi j % y) (y := y)
      (x.testBit (La - 1 - j)) (by omega) (by omega) w S' (by rw [hsym, hbit])
      (by rw [hS' rr ‹rr ≠ t› ‹a ≠ rr›.symm]; simp [Ψ, Function.update_of_ne ‹q ≠ rr›.symm])
      (by rw [hS' bw ‹bw ≠ t› ‹a ≠ bw›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›, h4bw])
      (by rw [hS' tx ‹t ≠ tx›.symm ‹a ≠ tx›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ tx›.symm, Function.update_of_ne ‹rr ≠ tx›.symm,
            h4 tx ‹a ≠ tx›.symm ‹t ≠ tx›.symm ‹rr ≠ tx›.symm ‹bw ≠ tx›.symm, htx])
      (by rw [hS' ty ‹t ≠ ty›.symm ‹a ≠ ty›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ ty›.symm, Function.update_of_ne ‹rr ≠ ty›.symm,
            h4 ty ‹a ≠ ty›.symm ‹t ≠ ty›.symm ‹rr ≠ ty›.symm ‹bw ≠ ty›.symm, hty])
      (by rw [hS' tz ‹t ≠ tz›.symm ‹a ≠ tz›.symm]
          simp [Ψ, Function.update_of_ne ‹q ≠ tz›.symm, Function.update_of_ne ‹rr ≠ tz›.symm,
            h4 tz ‹a ≠ tz›.symm ‹t ≠ tz›.symm ‹rr ≠ tz›.symm ‹bw ≠ tz›.symm, htz])
      depth
    have he := htrace.toExec
    obtain ⟨hdiv, hmod⟩ := div_step y (hi j) (x.testBit (La - 1 - j)) hy0
    refine ⟨w', _, _, hw', le_refl _, he, ?_, ?_, ?_, (by change mnSize (mk w S') ≤ _; omega)⟩
    · simp [Function.update_of_ne ‹q ≠ t›.symm, Function.update_of_ne ‹rr ≠ t›.symm]
    · simp [Function.update_of_ne ‹a ≠ q›, Function.update_of_ne ‹a ≠ rr›]
    · intro k hkt hka
      by_cases hkq : k = q
      · subst hkq
        rw [Function.update_self, hSq]
        simp only [Ψ, Function.update_self, hhi, hdiv]
        rw [← List.cons_append, ← binSyms_two_mul_add]
      rw [Function.update_of_ne hkq]
      by_cases hkr : k = rr
      · subst hkr
        rw [Function.update_self]
        simp only [Ψ, Function.update_of_ne hkq, Function.update_self, hhi, hmod]
      rw [Function.update_of_ne hkr, hS' k hkt hka]
      simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkr]
  obtain ⟨v₅, R₅, m₅, hu₅, hm₅, he₅, ht₅, ha₅, hΨ₅⟩ := eachSym_exec_within_final_stock (body := body) ‹a ≠ t›.symm
    (by decide : 1 ≤ 3) (divIter_native ..) v₄
    { S with R := R₄ } hp (fun k hkt hka => by
      dsimp only
      by_cases hkq : k = q
      · subst hkq
        simp [Ψ, binSyms, h4 k ‹a ≠ k›.symm ‹k ≠ t› ‹k ≠ rr› ‹k ≠ bw›]
      by_cases hkr : k = rr
      · subst hkr
        simp only [Ψ, Function.update_of_ne hkq, Function.update_self, hi, Nat.sub_zero,
          Nat.div_eq_of_lt hx, Nat.zero_mod, h4rr]
      simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkr])
    depth
  dsimp only at hm₅ ht₅ ha₅ hΨ₅
  rw [h4t, List.length_reverse, length_binSyms] at hm₅ hΨ₅
  rw [h4t, h4a, List.reverse_reverse, List.append_nil] at ha₅
  have h5rr : R₅ rr = binSyms W (x % y) := by
    rw [hΨ₅ rr ‹rr ≠ t› ‹a ≠ rr›.symm]
    simp [Ψ, hi, Function.update_of_ne ‹q ≠ rr›.symm]
  have h5q : R₅ q = binSyms La (x / y) ++ S.R q := by
    rw [hΨ₅ q ‹q ≠ t› ‹a ≠ q›.symm]
    simp [Ψ, hi]
  -- the remainder without its top bit onto `r`, and clear `bw`
  obtain ⟨v₆, hu₆, he₆⟩ := bmoveLow_exec body (s := rr) (t := tx) (d := r) ‹rr ≠ tx› ‹r ≠ tx› v₅
    { S with R := R₅ } (by
      show R₅ tx = []
      rw [hΨ₅ tx ‹t ≠ tx›.symm ‹a ≠ tx›.symm]
      simp [Ψ, Function.update_of_ne ‹q ≠ tx›.symm, Function.update_of_ne ‹rr ≠ tx›.symm,
        h4 tx ‹a ≠ tx›.symm ‹t ≠ tx›.symm ‹rr ≠ tx›.symm ‹bw ≠ tx›.symm, htx])
  dsimp only at he₆
  rw [h5rr, hW, binSyms_dropLast, length_binSyms] at he₆
  obtain ⟨v₇, hu₇, -, he₇⟩ := bclear_exec body bw v₆
    { S with
      R := Function.update (Function.update R₅ rr []) r
        (binSyms Lb (x % y) ++ Function.update R₅ rr [] r) }
  have h6bw : (Function.update (Function.update R₅ rr []) r
      (binSyms Lb (x % y) ++ Function.update R₅ rr [] r)) bw = binSyms W y := by
    rw [Function.update_of_ne ‹r ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›,
      hΨ₅ bw ‹bw ≠ t› ‹a ≠ bw›.symm]
    simp [Ψ, Function.update_of_ne ‹q ≠ bw›.symm, Function.update_of_ne ‹bw ≠ rr›, h4bw]
  let start : Stacks T A := {S with R := R₄}
  let finish : Stacks T A := {S with R := R₅}
  let roles : Fin 4 → Fin T := ![a,t,rr,q]
  let words : Fin 4 → List (Fin (A+4)) := ![R₅ a,R₅ t,R₅ rr,R₅ q]
  have hroles : Function.Injective roles := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all [roles]
  have hbalance := mn_replace_bank_size roles hroles v₄ v₅ start finish words
    (by intro i; fin_cases i <;> rfl)
    (by
      intro k hk
      have hka := (hk 0).symm
      have hkt := (hk 1).symm
      have hkr := (hk 2).symm
      have hkq := (hk 3).symm
      change k ≠ a at hka
      change k ≠ t at hkt
      change k ≠ rr at hkr
      change k ≠ q at hkq
      change R₅ k = R₄ k
      rw [hΨ₅ k hkt hka]
      simp [Ψ,hkq,hkr]) rfl rfl rfl
  have h4q : R₄ q = S.R q := h4 q ‹a ≠ q›.symm ‹q ≠ t› ‹q ≠ rr› ‹q ≠ bw›
  have hloopSize : mnSize (mk v₅ finish) = mnSize (mk v₄ start)+La := by
    change mnSize (mk v₅ finish)+
      ((R₄ a).length+((R₄ t).length+((R₄ rr).length+(R₄ q).length))) =
      mnSize (mk v₄ start)+
      ((R₅ a).length+((R₅ t).length+((R₅ rr).length+(R₅ q).length))) at hbalance
    rw [ht₅,ha₅,h5rr,h5q,h4a,h4t,h4rr,h4q] at hbalance
    simp only [length_binSyms,List.length_nil,List.length_reverse,List.length_append] at hbalance
    omega
  have hnativeCopy : mnNativePushBound 3 (bcopy (P := P) (Q := Q) (A := A) (U := U) b bw tx ty) := by
    simp [bcopy,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hnativePad : mnNativePushBound 3 (bpad1 (P := P) (Q := Q) (A := A) (U := U) bw tx) := by
    simp [bpad1,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hnativeZero : mnNativePushBound 3 (bzero (P := P) (Q := Q) (A := A) (U := U) bw rr tx) := by
    simp [bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hw₁ := mn_native_exec_within he₁ 3 hnativeCopy depth _ (Nat.le_refl _)
  have hw₂ := mn_native_exec_within he₂ 3 hnativePad depth _ (Nat.le_refl _)
  have hw₃ := mn_native_exec_within he₃ 3 hnativeZero depth _ (Nat.le_refl _)
  have hpre := mn_seq_within_add hw₁ (mn_seq_within_add hw₂ hw₃)
  let pay := 3*(6*Lb+6)+(3*(4*Lb+7)+3*(4*W+4))
  have hpreEnd : mnSize (mk v₃ {S with R := R₃})+depth ≤ mnSize (mk v S)+depth+pay := hpre.final
  have hw₄ := moveR_within a t id he₄ depth (mnSize (mk v S)+depth+pay) hpreEnd
  have hstart : mnSize (mk v₄ start)+depth ≤ mnSize (mk v S)+depth+pay := hw₄.final
  let bound := mnSize (mk v S)+depth+(La+200*(Lb+1)+200)
  have hfirst := hw₁.final
  have hsecond := (mn_seq_within_add hw₁ hw₂).final
  have h1 := hw₁.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    dsimp only [bound,W]
    omega)
  have h2 := hw₂.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₁ {S with R := R₁})+depth+3*(4*Lb+7) at hz
    change mnSize (mk v₁ {S with R := R₁})+depth ≤ mnSize (mk v S)+depth+3*(6*Lb+6) at hfirst
    dsimp only [bound,W]
    omega)
  have h3 := hw₃.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₂ {S with R := R₂})+depth+3*(4*W+4) at hz
    change mnSize (mk v₂ {S with R := R₂})+depth ≤ mnSize (mk v S)+depth+(3*(6*Lb+6)+3*(4*Lb+7)) at hsecond
    dsimp only [bound,W] at *
    omega)
  have hw₄' := hw₄.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    dsimp only [bound,pay,W] at *
    omega)
  have hw₅ := he₅.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₅ finish)+depth+3*(12*W+18+2) at hz
    rw [hloopSize] at hz
    dsimp only [bound,pay,W] at *
    omega)
  have hnativeLow : mnNativePushBound 3 (bmoveLow (P := P) (Q := Q) (A := A) (U := U) rr tx r) := by
    simp [bmoveLow,dropTop,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hw₆ := mn_native_exec_within he₆ 3 hnativeLow depth bound (by
    change mnSize (mk v₅ finish)+depth+3*(2*(Lb+1)+2*((Lb+1)-1)+5) ≤ bound
    rw [hloopSize]
    dsimp only [bound,pay,W] at *
    omega)
  have hw₇ := mn_native_exec_within he₇ 0 (by
    simp [bclear,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth bound
    (by simpa only [Nat.zero_mul,Nat.add_zero] using hw₆.final)
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, (ExecWithin.seq h1 (ExecWithin.seq h2 (ExecWithin.seq h3 (ExecWithin.seq hw₄' (ExecWithin.seq hw₅ (ExecWithin.seq hw₆ hw₇)))))).cast rfl ?_⟩
  · dsimp only
    rw [h6bw, length_binSyms]
    simp only [hW, Nat.add_sub_cancel] at hm₅ ⊢
    nlinarith [hm₅]
  · congr 2
    funext k
    dsimp only
    by_cases hkbw : k = bw
    · subst hkbw
      rw [Function.update_self, Function.update_of_ne ‹r ≠ k›.symm,
        Function.update_of_ne ‹q ≠ k›.symm, hbw]
    rw [Function.update_of_ne hkbw]
    by_cases hkr : k = r
    · subst hkr
      rw [Function.update_self, Function.update_self, Function.update_of_ne ‹k ≠ rr›,
        hΨ₅ k ‹k ≠ t› ‹a ≠ k›.symm]
      simp [Ψ, Function.update_of_ne ‹q ≠ k›.symm, Function.update_of_ne ‹k ≠ rr›,
        h4 k ‹a ≠ k›.symm ‹k ≠ t› ‹k ≠ rr› ‹k ≠ bw›]
    rw [Function.update_of_ne hkr, Function.update_of_ne hkr]
    by_cases hkrr : k = rr
    · subst hkrr
      rw [Function.update_self, Function.update_of_ne ‹q ≠ k›.symm, hrr]
    rw [Function.update_of_ne hkrr]
    by_cases hkq : k = q
    · subst hkq; rw [Function.update_self, h5q]
    rw [Function.update_of_ne hkq]
    by_cases hka : k = a
    · subst hka; rw [ha₅, ha]
    by_cases hkt : k = t
    · subst hkt; rw [ht₅, ht]
    rw [hΨ₅ k hkt hka]
    simp only [Ψ, Function.update_of_ne hkq, Function.update_of_ne hkrr]
    exact h4 k hka hkt hkrr hkbw

end IntegerMultBounds.MathlibTM2.Host
