module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedLayout
public import IntegerMultBounds.MathlibTM2.Cover.LabelPermutation

/-! Rotate the exterior field past the label using equal-width radix exchanges. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume index)
open Shared50ModularControl (prime)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Stage2Machine.Straight (words)
local instance (c : ℕ) : NeZero (prime^c) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

noncomputable def chunkLayout (k c P K : ℕ) : Descriptor := ⟨P,1,prime^(k*c),0,1,K⟩

private theorem chunks_move {k c P K : ℕ} (ps : List (LabelSchedule.Pair k)) {x y}
    (steps : LabelSchedule.Swaps (chunkLayout k c P K) c 1 ps x y) :
    ∀ (a : Fin P) (t : Fin K) (digits : Fin k → ZMod (prime^c)),
      let cell := fun d : Fin k → ZMod (prime^c) =>
        index prime (chunkLayout k c P K) a 0 (FlatCoordinateLayout.rank d).val 0 0 0 t
      y (cell (digits ∘ (ps.map fun p => Equiv.swap p.val.1 p.val.2).prod)) = x (cell digits) := by
  induction ps generalizing x with
  | nil => subst y; intros; rfl
  | cons p ps ih =>
    obtain ⟨z,step,rest⟩ := steps
    intro a t digits cell
    let s := p.val.1
    let u := p.val.2
    have hs : s < u := p.property
    have update : digits ∘ Equiv.swap s u = Function.update (Function.update digits s (digits u)) u (digits s) := by
      funext j
      by_cases h : j = s
      · subst j; simp [Function.update_of_ne hs.ne]
      by_cases h' : j = u
      · subst j; simp
      simp [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne h h',Function.update_of_ne h,Function.update_of_ne h']
    obtain ⟨pre,gap,last,old,new⟩ := LabelColumns.rank_pair_update digits s u hs (digits u) (digits s)
    have radix (n : ℕ) : (prime^c)^n = prime^(n*c) := by rw [← pow_mul,Nat.mul_comm]
    have read := LabelView.swap_cols (h := 0) (d := 0) (B := 1) (v := chunkLayout k c P K)
      (show (chunkLayout k c P K).beforeH = 1*prime^(k*c) by simp [chunkLayout]) hs u.isLt step
      a.isLt (by decide : 0 < 1) (by decide : 0 < 1) (by simpa only [radix] using pre.isLt)
      (ZMod.val_lt (digits u)) (by simpa only [radix] using gap.isLt) (ZMod.val_lt (digits s))
      (by simpa only [radix] using last.isLt) (by simp [chunkLayout]) (by decide : 0 < 1) (by simp [chunkLayout]) t.isLt
    apply (ih rest a t (digits ∘ Equiv.swap s u)).trans
    change z (cell (digits ∘ Equiv.swap s u)) = x (cell digits)
    simp only [cell,update,new,old,LabelView.label,Nat.mul_one,Nat.one_mul,radix]
    simpa only [LabelView.label,Nat.zero_mul,Nat.zero_add] using read

/-- The fixed schedule overhead is absorbed by one nonempty parent volume. -/
theorem borrowedLabel_cost_bound [M8.Machine.Net] (ps : List (LabelSchedule.Pair 263)) :
    ∃ C : ℝ, ∀ (V w : ℕ), 0 < V → 0 < w →
      ((LabelSchedule.countCost ps + 262*(3808274*V + LeafCore.coreCost V (w*16)) : ℕ) : ℝ)
        ≤ C * V * (w : ℝ) ^ M8.Machine.BudgetBound.tau := by
  obtain ⟨C, bound⟩ := scaledRoute_cost_bound (LabelSchedule.countCost ps + 262*3808274) 262 16 (by decide)
  refine ⟨C, fun V w hV hw => le_trans ?_ (bound V w hw)⟩
  exact_mod_cast (show _ ≤ (_ + 262*3808274)*V + 262*LeafCore.coreCost V (w*16) by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    have h := Nat.le_mul_of_pos_right (LabelSchedule.countCost ps) hV
    omega)

/-- A fixed machine moves the seven exterior chunks past the 256 label
chunks. Each chunk has 16 atoms, and every trailing payload bit is preserved. -/
theorem borrowedLabel_runs [M8.Machine.Net] {T : ℕ} (io : Fin T) :
    ∃ ps : List (LabelSchedule.Pair 263), ps.length ≤ 262 ∧
      ∀ (w P K : ℕ), 0 < w → 0 < P → 0 < K →
      let c := w*16
      let v := chunkLayout 263 c P K
      ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
      roles.head io = 0 → roles.tape io = sourceWord x →
      ∃ y : Fin (volume prime v) → ZMod 2,
        GraphContract.Runs (LabelSchedule.schedule io ps)
          (LabelCall.bank roles v (words (LabelSchedule.base v c)))
          (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v (words (LabelSchedule.base v c)))
          (LabelSchedule.countCost ps + 262*(3808274*volume prime v + LeafCore.coreCost (volume prime v) c)) ∧
        ∀ (a : Fin P) (t : Fin K) (e : Fin ((prime^w)^112)) (l : Fin (prime^(64*(w*64)))),
          ext y (((a.val*prime^(64*(w*64))+l.val)*(prime^w)^112+e.val)*K+t.val) =
            ext x (((a.val*(prime^w)^112+e.val)*prime^(64*(w*64))+l.val)*K+t.val) := by
  let π : Equiv.Perm (Fin 263) := (finAddFlip : Fin (256+7) ≃ Fin (7+256))
  obtain ⟨ps,route,count,run⟩ := LabelSchedule.permutation_schedule π io
  refine ⟨ps,count,?_⟩
  intro w P K hw hp hk c v roles x head word
  obtain ⟨y,steps,exec⟩ := run v c 1 (by dsimp [c]; omega) (by decide)
    (by simp [v,chunkLayout]) ⟨hp,Nat.zero_lt_one,pow_pos Shared50ModularControl.prime_prime.pos _,Nat.zero_lt_one,hk⟩ roles x head word
  refine ⟨y,exec,?_⟩
  intro a t exterior label
  have left : (prime^c)^7 = (prime^w)^112 := by rw [← pow_mul,← pow_mul]; congr 1; dsimp [c]; omega
  have right : (prime^c)^256 = prime^(64*(w*64)) := by rw [← pow_mul]; congr 1; dsimp [c]; omega
  let e := FlatCoordinateLayout.coordinates (exterior.cast left.symm)
  let l := FlatCoordinateLayout.coordinates (label.cast right.symm)
  have read := chunks_move ps steps a t (fun j => Fin.addCases (motive := fun _ => ZMod (prime^c)) e l j)
  rw [← route] at read
  have rotate : (fun j => Fin.addCases (motive := fun _ => ZMod (prime^c)) e l j) ∘ π = (fun j : Fin (256+7) => Fin.addCases (motive := fun _ => ZMod (prime^c)) l e j) := by
    funext j
    induction j using Fin.addCases (m := 256) (n := 7) with
    | left j => simp [π]; rw [finAddFlip_apply_castAdd j 7,Fin.addCases_right]
    | right j => simp [π]; rw [finAddFlip_apply_natAdd j 256,Fin.addCases_left]
  simp only [rotate,index,v,chunkLayout,pow_zero,mul_one,add_zero,
    ArbitraryWidthSliceTranspose.rank_append l e,ArbitraryWidthSliceTranspose.rank_append e l,e,l,FlatCoordinateLayout.rank_coordinates,Fin.val_cast] at read
  have width : prime^(263*c) = (prime^c)^7*(prime^c)^256 := by rw [← pow_add,← pow_mul]; congr 1; omega
  refine Eq.trans (congrArg (ext y) ?_) (read.trans (congrArg (ext x) ?_))
  all_goals rw [width,left,right]; ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
