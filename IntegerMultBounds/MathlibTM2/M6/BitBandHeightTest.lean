module

public import IntegerMultBounds.MathlibTM2.M6.BitCanonicalBandRoot

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

def dropBits {T Q : ℕ} {U : Type} (src : Fin T) : ℕ → Act T Q prime U
  | 0 => .done
  | n+1 => .pop (.rt src) (fun u _ => u) (dropBits src n)

private theorem dropBits_run {T Q : ℕ} {U : Type} (src : Fin T) (n : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) :
    (dropBits src n).run (mk u S) = mk u {S with R := Function.update S.R src ((S.R src).drop n)} := by
  induction n generalizing S with
  | zero => simp [dropBits,run_done,Function.update_eq_self]
  | succ n ih =>
    simp [dropBits,Action.run,update_rt,ih,Function.update_idem,← List.drop_one,List.drop_drop,Nat.add_comm]

/-- Test whether the maximum-rank branch is still above cutoff at depth k.
Prefixing the cutoff by six low zeros per level multiplies it by 64^k. -/
noncomputable def bandTest {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) (rank k : ℕ) : Pr P T Q prime U :=
  .seq (.act (Cover.LabelCycle.pushWord (r 1) (List.replicate (6*k) (bitSymbol false)) .done))
    (.seq (ordinaryCutoffTest r (rank*42^k)) (.act (dropBits (r 1) (6*k))))

theorem bandTest_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (rank k w L cutoff : ℕ)
    (fits : ((w+1)*rank).size ≤ L) (cutFits : cutoff < 2^L)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (word : S.R (r 1) = binSyms L cutoff) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    ∃ z t, z.user = u.user ∧ z.scan (r 7) = bitSymbol (decide (cutoff*64^k < (w+1)*rank*42^k)) ∧
      t ≤ 4*w+23*((w+1)*rank*42^k)+22*(6*k+L)+52 ∧
      Exec body (bandTest r rank k) (mk u S) t (mk z S) := by
  let shift := 6*k
  let zeros := List.replicate shift (bitSymbol false : Fin (prime+4))
  let D := {S with R := Function.update S.R (r 1) (zeros ++ S.R (r 1))}
  have scale : 2^shift = 64^k := by dsimp [shift]; rw [pow_mul]; rfl
  have digits : D.R (r 1) = binSyms (shift+L) (2^shift*cutoff) := by
    change Function.update _ _ _ _ = _
    rw [Function.update_self,word,binSyms_append,← binSyms_mod shift (2^shift*cutoff),Nat.mul_mod_right,
      binSyms_zero_eq,Nat.mul_div_cancel_left _ (by positivity)]
  have large : (w+1)*(rank*42^k) < 2^(shift+L) := by
    rw [pow_add,scale,← Nat.mul_assoc,Nat.mul_comm (64^k)]
    exact (Nat.mul_lt_mul_of_pos_right (Nat.size_le.mp fits) (show 0 < 42^k by positivity)).trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) k))
  have cp : 2^shift*cutoff < 2^(shift+L) := by rw [pow_add]; gcongr
  have put := Exec.act (body := body) (Cover.LabelCycle.pushWord (r 1) zeros .done) (mk u S)
  rw [Cover.LabelCycle.pushWord_run,run_done] at put
  obtain ⟨z,t,user,flag,price,run⟩ := ordinaryCutoffTest_exec body r (rank*42^k) w (shift+L)
    (2^shift*cutoff) cp (Nat.size_le.mpr large) u D (by simpa [D] using clock) digits (by
      intro j lo
      have ne : j ≠ 1 := by intro eq; subst j; contradiction
      simpa [D,ne] using empty j lo)
  have erase := Exec.act (body := body) (dropBits (r 1) shift) (mk z D)
  rw [dropBits_run] at erase
  have reset : Function.update D.R (r 1) ((D.R (r 1)).drop shift) = S.R := by
    simp [D,zeros,Function.update_idem,Function.update_eq_self]
  rw [reset] at erase
  refine ⟨z,_,user,?_,?_,Exec.seq put (Exec.seq run erase)⟩
  · simpa only [scale,Nat.mul_comm (64^k),Nat.mul_assoc] using flag
  · dsimp [shift] at price; rw [← Nat.mul_assoc (w+1)] at price; omega

noncomputable def rowWord (k : ℕ) : List (Fin (prime+4)) :=
  let rows := 142080^(k+1)
  binSyms rows.size rows

/-- Scan the possible depths in order, writing the row word at the first stop. -/
noncomputable def selectBandRows {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) (dst : Fin T)
    (rank : ℕ) : ℕ → ℕ → Pr P T Q prime U
  | 0,k => .act (Cover.LabelCycle.pushWord dst (rowWord k) .done)
  | n+1,k => .seq (bandTest r rank k) (.cond (fun z => symBit (z.scan (r 7)))
      (selectBandRows r dst rank n (k+1)) (.act (Cover.LabelCycle.pushWord dst (rowWord k) .done)))

theorem selectBandRows_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (dst : Fin T) (a : ActiveBandRecord) (rank w L : ℕ)
    (width : a.input.node.width = (w+1)*rank) (fits : ((w+1)*rank).size ≤ L)
    (cutFits : a.input.cutoff < 2^L) (u : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (r 0)).length = w) (word : S.R (r 1) = binSyms L a.input.cutoff)
    (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) (fresh : S.R dst = []) :
    let h := bandHeight a.input.node.width a.input.cutoff
    let rows := 142080^(h+1)
    ∃ z t, z.user = u.user ∧ t ≤ 6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1 ∧
      Exec body (selectBandRows r dst rank 6 0) (mk u S) t
        (mk z {S with R := Function.update S.R dst (binSyms rows.size rows)}) := by
  intro h rows
  have spec := bandHeight_spec a.input.w a.input.cutoff a.band
  rw [← a.input.width] at spec
  let cost := 4*w+23*((w+1)*rank*42^5)+22*(30+L)+53
  let F := {S with R := Function.update S.R dst (rowWord h)}
  have put (v : HS T Q prime U) : Exec body (.act (Cover.LabelCycle.pushWord dst (rowWord h) .done))
      (mk v S) 1 (mk v F) := by
    simpa [F,Cover.LabelCycle.pushWord_run,fresh] using Exec.act (body := body)
      (Cover.LabelCycle.pushWord dst (rowWord h) .done) (mk v S)
  have scan (n k : ℕ) (span : k+n = 6) (lo : k ≤ h) (hi : h ≤ k+n) (v : HS T Q prime U) :
      ∃ z t, z.user = v.user ∧ t ≤ n*cost+1 ∧
        Exec body (selectBandRows r dst rank n k) (mk v S) t (mk z F) := by
    induction n generalizing k v with
    | zero =>
      have eq : k = h := by omega
      exact ⟨v,1,rfl,by simp,eq ▸ put v⟩
    | succ n ih =>
      obtain ⟨z,t,user,flag,time,run⟩ := bandTest_exec body r rank k w L a.input.cutoff fits cutFits
        v S clock word empty
      have price : t+1 ≤ cost := by
        have powers : 42^k ≤ 42^5 := Nat.pow_le_pow_right (by decide) (by omega)
        dsimp [cost]
        have clockBound : 6*k ≤ 30 := by omega
        grw [time,powers,clockBound]
        rfl
      by_cases live : a.input.cutoff*64^k < (w+1)*rank*42^k
      · have next : k+1 ≤ h := by
          by_contra! short
          have eq : h = k := by omega
          have stop := spec.1
          change a.input.node.width*42^h ≤ a.input.cutoff*64^h at stop
          rw [eq,width] at stop
          omega
        obtain ⟨y,m,same,paid,child⟩ := ih (k+1) (by omega) next (by omega) z
        refine ⟨y,t+(m+1),same.trans user,?_,Exec.seq run (Exec.cond_true (by simp [mk_var,flag,live]) child)⟩
        rw [Nat.succ_mul]; omega
      · have stop := Nat.le_of_not_gt live
        rw [← width] at stop
        have eq : k = h := Nat.le_antisymm lo (spec.2 k stop)
        refine ⟨z,t+(1+1),user,?_,Exec.seq run (Exec.cond_false (by simp [mk_var,flag,live]) (eq ▸ put z))⟩
        rw [Nat.succ_mul]; omega
  exact scan 6 0 rfl (Nat.zero_le _) (Nat.sub_le 6 _) u

end IntegerMultBounds.MathlibTM2.M6.BitNode
