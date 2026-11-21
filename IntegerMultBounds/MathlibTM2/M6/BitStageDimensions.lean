module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank

/-! Compute the width, row and block counters for a restored PR589 target scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

/-- Slots 0–2 receive the three headers. Each power reads its own seed in
slots 3–5, with a common radix in slot 6 and common scratch in slots 7–13. -/
def stagePowerPorts (i : Fin 3) : Fin 10 ↪ Fin 14 :=
  ⟨![6,(i.natAdd 3).castAdd 8,i.castAdd 11,7,8,9,10,11,12,13],(by decide : ∀ i : Fin 3,
    Function.Injective (![6,(i.natAdd 3).castAdd 8,i.castAdd 11,7,8,9,10,11,12,13] : Fin 10 → Fin 14)) i⟩

def stageDegrees : Fin 3 → ℕ := ![112,4096,16]

def stagePowerTime (M seed d : ℕ) :=
  dimensionTime M.size seed.size d + (4*(d*M.size+seed.size)+6)

theorem stagePower_exec (body : P → Pr P T Q prime U) (r : Fin 14 ↪ Fin T) (i : Fin 3)
    (M seed : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (base : S.R (r 6) = binSyms M.size M)
    (word : S.R (r ((i.natAdd 3).castAdd 8)) = binSyms seed.size seed)
    (empty : S.R (r (i.castAdd 11)) = [])
    (scratch : ∀ j : Fin 14, 7 ≤ j.val → S.R (r j) = []) :
    let dst := r (i.castAdd 11)
    let value := M^(stageDegrees i)*seed
    ∃ v t, v.user = u.user ∧ t ≤ stagePowerTime M seed (stageDegrees i) ∧
      Exec body (swapPrefix ((stagePowerPorts i).trans r) (stageDegrees i))
        (mk u S) t (mk v {S with R := Function.update S.R dst (binSyms value.size value)}) := by
  intro dst value
  obtain ⟨v,t,user,paid,run⟩ := scaledPrefix_exec body ((stagePowerPorts i).trans r)
    (stageDegrees i) M.size seed.size M seed (Nat.lt_size_self _) (Nat.lt_size_self _)
    u S base word (fun j lo hi => by
      by_cases h : j = 2
      · subst j; exact empty
      · apply scratch
        exact (by decide : ∀ i : Fin 3, ∀ j : Fin 10, 2 ≤ j → j < 9 → j ≠ 2 →
          7 ≤ (stagePowerPorts i j).val) i j lo hi h)
  rw [canonicalBits_symbols] at run
  exact ⟨v,t,user,paid,run⟩

theorem stagePowerValues (w B W : ℕ) (i : Fin 3) :
    (prime^w)^(stageDegrees i)*(![W,1,B] i) =
      ![(prime^w)^112*W,prime^(64*(w*64)),(prime^w)^16*B] i := by
  fin_cases i
  · rfl
  · change (prime^w)^4096*1 = prime^(64*(w*64))
    rw [Nat.mul_one,← pow_mul]
    congr 1
    omega
  · rfl

/-- All three fixed powers cost at most a constant times the volume.
Two radix factors suffice to pay for binary multiplication. -/
theorem stageDimensionsTime_le (M B W : ℕ) (hm : 0 < M) (hb : 0 < B) (hw : 0 < W) :
    let seed := (![W,1,B] : Fin 3 → ℕ)
    ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i))).sum+2 ≤
      1530000002*(M^2*(B*W)) := by
  intro seed
  let V := M^2*(B*W)
  have pos := Nat.mul_pos hb hw
  have radix : M ≤ M^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right M hm
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have scale : M^2 ≤ V := Nat.le_mul_of_pos_right _ pos
  have h := digits.trans (radix.trans scale)
  have square : M.size*M.size ≤ V := (Nat.mul_le_mul digits digits).trans (by simpa [pow_two] using scale)
  have vpos : 0 < V := Nat.mul_pos (pow_pos hm 2) pos
  have each (i : Fin 3) : stagePowerTime M (seed i) (stageDegrees i) ≤ 510000000*V := by
    have small : seed i ≤ B*W := by
      fin_cases i
      · exact Nat.le_mul_of_pos_left _ hb
      · exact pos
      · exact Nat.le_mul_of_pos_right _ hw
    have width : (seed i).size ≤ B*W := (Nat.size_le.mpr Nat.lt_two_pow_self).trans small
    have tail := width.trans (Nat.le_mul_of_pos_left _ (pow_pos hm 2))
    have cross : M.size*(seed i).size ≤ V := Nat.mul_le_mul (digits.trans radix) width
    have degree : stageDegrees i ≤ 4096 := (by decide : ∀ i, stageDegrees i ≤ 4096) i
    calc
      _ ≤ 6*(seed i).size+6+4096*((12*M.size+18)*(4096*M.size+(seed i).size)+20*M.size+26)+
          (4*(4096*M.size+(seed i).size)+6) := by
            unfold stagePowerTime
            grw [dimensionTime_le,degree]
      _ ≤ _ := by change (seed i).size ≤ V at tail; nlinarith only [tail,h,square,cross,vpos]
  have total := List.sum_le_length_nsmul ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i)))
    (510000000*V) (fun _ hx => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact each i)
  simp only [List.length_map,List.length_finRange,nsmul_eq_mul] at total
  change _ ≤ 1530000002*V
  omega

/-- Compute the counters in their scan order, then put the three heads just
past the separators. Both stacks of every other register are preserved. -/
theorem stageDimensions_exec (body : P → Pr P T Q prime U) (r : Fin 14 ↪ Fin T)
    (w B W : ℕ) (u : HS T Q prime U) (S : Stacks T prime) :
    let M := prime^w
    let seed := (![W,1,B] : Fin 3 → ℕ)
    let values := (![M^112*W,prime^(64*(w*64)),M^16*B] : Fin 3 → ℕ)
    let dst := (Fin.castAddEmb 11 (n := 3)).trans r
    let power := fun i => swapPrefix ((stagePowerPorts i).trans r) (stageDegrees i)
    S.R (r 6) = binSyms M.size M →
    (∀ i : Fin 3, S.R (r ((i.natAdd 3).castAdd 8)) = binSyms (seed i).size (seed i)) →
    (∀ i, S.L (dst i) = [] ∧ S.R (dst i) = []) →
    (∀ j : Fin 14, 7 ≤ j.val → S.R (r j) = []) →
    ∃ v F t, v.user = u.user ∧ t ≤ ((List.finRange 3).map (fun i => stagePowerTime M (seed i) (stageDegrees i))).sum+2 ∧
      Exec body (.seq (Prog.seqList ((List.finRange 3).map power)) (.act (pushMarkers ((List.finRange 3).map dst))))
        (mk u S) t (mk v F) ∧
      (∀ i, F.L (dst i) = [separator] ∧ F.R (dst i) = binSyms (values i).size (values i)) ∧
      ∀ j, (∀ i, dst i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro M seed values dst power base words empty scratch
  have run (is : List (Fin 3)) (nd : is.Nodup) (a : HS T Q prime U) (A : Stacks T prime)
      (ready : ∀ j, (∀ i, dst i ≠ j) → A.R j = S.R j)
      (free : ∀ i ∈ is, A.R (dst i) = []) :
      ∃ v F t, v.user = a.user ∧ t ≤ (is.map (fun i => stagePowerTime M (seed i) (stageDegrees i))).sum+1 ∧
        Exec body (Prog.seqList (is.map power)) (mk a A) t (mk v F) ∧ F.L = A.L ∧
        (∀ i ∈ is, F.R (dst i) = binSyms (values i).size (values i)) ∧
        ∀ j, (∀ i ∈ is, dst i ≠ j) → F.R j = A.R j := by
    induction is generalizing a A with
    | nil => exact ⟨a,A,1,rfl,by simp,Exec.act _ _,rfl,by simp,fun _ _ => rfl⟩
    | cons i is ih =>
      have keep (j : Fin 14) (h : 3 ≤ j.val) := ready (r j) (fun k => r.injective.ne (by
        intro eq
        have val := congrArg Fin.val eq
        change k.val = j.val at val
        omega))
      obtain ⟨b,t,user,paid,first⟩ := stagePower_exec body r i M (seed i) a A
        ((keep 6 (by decide)).trans base) ((keep _ (by change 3 ≤ 3+i.val; omega)).trans (words i))
        (free i (by simp)) (fun j hj => (keep j (by omega)).trans (scratch j hj))
      rw [show M^(stageDegrees i)*seed i = values i from stagePowerValues w B W i] at first
      let C := {A with R := Function.update A.R (dst i) (binSyms (values i).size (values i))}
      have kept (j) (h : dst i ≠ j) : C.R j = A.R j := Function.update_of_ne h.symm _ _
      obtain ⟨v,F,m,same,bill,rest,left,loaded,off⟩ := ih nd.of_cons b C
        (fun j h => (kept j (h i)).trans (ready j h))
        (fun k hk => (kept _ (dst.injective.ne (fun eq => nd.notMem (eq ▸ hk)))).trans
          (free k (List.mem_cons_of_mem _ hk)))
      refine ⟨v,F,t+m,same.trans user,?_,Exec.seq first rest,left,?_,?_⟩
      · simp only [List.map_cons,List.sum_cons]; omega
      · intro k hk
        rcases List.mem_cons.mp hk with eq | hk
        · subst k
          rw [off (dst i) (fun l hl => dst.injective.ne (fun eq : l = i => nd.notMem (eq ▸ hl)))]
          exact Function.update_self ..
        · exact loaded k hk
      · intro j h
        exact (off j (fun k hk => h k (List.mem_cons_of_mem _ hk))).trans (kept j (h i (by simp)))
  obtain ⟨v,A,t,user,paid,exec,left,right,off⟩ := run _ (List.nodup_finRange 3) u S
    (fun _ _ => rfl) (fun i _ => (empty i).2)
  have mark := Exec.act (body := body) (pushMarkers ((List.finRange 3).map dst)) (mk v A)
  rw [pushMarkers_run _ ((List.nodup_finRange 3).map dst.injective)] at mark
  refine ⟨v,_,t+1,user,by omega,Exec.seq exec mark,?_,?_⟩
  · intro i
    exact ⟨by simp [left,(empty i).1,List.mem_finRange],right i (List.mem_finRange i)⟩
  · intro j h
    exact ⟨by simp [left,h],off j (fun i _ => h i)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
