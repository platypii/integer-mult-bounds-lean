module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildPrepare

/-! The caller owns the two packed weights and the middle-size header. It
allocates them before the recursive call and releases them on return. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm
open HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout
variable {P U : Type} {T Q A d r g W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def goodChildCall (f : P) (host : Fin 58 ↪ Fin T) (b r g : ℕ) : Pr P T Q A U :=
  .seq (.seq (childWeightList b (weights.trans (parentWithWeights.trans host)) (List.finRange r))
    (dimensionPower (middlePorts.trans host) (g+g)))
    (.seq (.call f) (Mult.ShortConv.clearWords [host 55,host 56,host 57]))

theorem goodChildCall_exec (body : P → Pr P T Q A U) (f : P) (host : Fin 58 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (hr : r ≤ d) (g W : ℕ)
    (minor : ∀ j (hj : j < r), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weight inv : Fin d → ZMod M) (inverse : ∀ j, weight j * inv j = 1)
    (hb : b.Prime) (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) (budget : ℕ) (post : Stacks T A → Prop) :
    let bank := parentWithWeights.trans host
    let machine := parent.trans bank
    let c := child.trans (head.trans (adapterBank.trans machine))
    let s := entry.trans (adapterBank.trans machine)
    let stage := stageAt G r hr minor r le_rfl
    let pivot := fun i : Fin r => stage.M (i.castLE hr) (i.castLE hr)
    let pos := (List.ofFn fun i : Fin r => binSyms H (weight (i.castLE hr) * pivot i).val).flatten
    let reciprocalWords := (List.ofFn fun i : Fin r => binSyms H (inv (i.castLE hr) * Ring.inverse (pivot i)).val).flatten
    let middle := binSyms ((g+g)*H+1) (goodChildDescriptor M r g W).between
    let outputs := [host 55,host 56,host 57]
    let prepared := {S with R := Function.update (Function.update (Function.update S.R (host 55) pos) (host 56) reciprocalWords) (host 57) middle}
    S.R (c 19) = (List.ofFn fun j => binSyms H (weight j).val).flatten ++ rest →
    S.R (c 18) = (List.ofFn fun i => binSyms H (pivot i).val).flatten ++ tail →
    S.R (c 4) = binSyms H M → S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (c k) = []) →
    S.R (s 2) = binSyms H M → S.R (s 28) = binSyms 1 1 → (∀ j ∈ headShearWork, S.R (s j) = []) →
    (∀ j ∈ outputs, S.R j = []) →
    (∀ u : HS T Q A U, u.user = v.user → ∃ z F n, z.user = u.user ∧ n ≤ budget ∧
      Exec body (body f) (mk u prepared) n (mk z F) ∧ post F ∧
      ∀ j ∈ outputs, F.R j = prepared.R j) →
    ∃ z F n, z.user = v.user ∧ post F ∧
      n ≤ (((List.finRange r).map fun i => childWeightTime b w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7)) ∧
      Exec body (goodChildCall f host b r g) (mk v S) n
        (mk z {F with R := fun j => if j ∈ outputs then [] else F.R j}) := by
  intro bank machine c s stage pivot pos reciprocal middle outputs prepared packed pivots modulus one clock free
    base seed scratch fresh call
  obtain ⟨u,l,hu,hl,pack⟩ := prepareGoodChild_exec body bank G r hr minor weight inv inverse hb H hm
    v S tail rest packed pivots modulus one clock free
  let D := {S with R := Function.update (Function.update S.R (host 55) pos) (host 56) reciprocal}
  have f55 := fresh (host 55) (by simp [outputs])
  have f56 := fresh (host 56) (by simp [outputs])
  have f57 := fresh (host 57) (by simp [outputs])
  change Exec _ _ _ _ (mk u {S with R := Function.update (Function.update S.R (host 55) (pos ++ S.R (host 55))) (host 56) (reciprocal ++ S.R (host 56))}) at pack
  rw [f55,f56,List.append_nil,List.append_nil] at pack
  have keep (j : Fin 58) (hj : j ≠ 55 ∧ j ≠ 56) : D.R (host j) = S.R (host j) := by
    simp [D,Function.update_of_ne (host.injective.ne hj.1),Function.update_of_ne (host.injective.ne hj.2)]
  obtain ⟨y,t,hy,ht,install⟩ := goodChildMiddle_exec body host r g W H hm u D
    ((keep 2 (by decide)).trans base) ((keep 28 (by decide)).trans seed) ((keep 57 (by decide)).trans f57)
    (fun j hj => (keep _ ((by decide : ∀ i, let k := parentWithWeights (parent (adapterBank (entry i))); k ≠ 55 ∧ k ≠ 56) j)).trans (scratch j hj))
  obtain ⟨z,F,n,hz,hn,run,done,stored⟩ := call y (hy.trans hu)
  obtain ⟨a,ha,clear⟩ := Mult.ShortConv.clearWords_exec (body := body) outputs
    (by simp [outputs,host.injective.eq_iff]) z F
  have len (x : Fin r → ZMod M) : (List.ofFn fun i => binSyms (A := A) H (x i).val).flatten.length = r*H := by
    simp [List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
  have charge : 2*(outputs.map fun j => (F.R j).length).sum+2*outputs.length+1 =
      2*(r*H+r*H+((g+g)*H+1))+7 := by
    simp [outputs,stored _ (by simp [outputs] : host 55 ∈ outputs),stored _ (by simp [outputs] : host 56 ∈ outputs),
      stored _ (by simp [outputs] : host 57 ∈ outputs),prepared,host.injective.eq_iff,pos,reciprocal,middle,len,length_binSyms]
    omega
  rw [charge] at clear
  exact ⟨a,F,_,ha.trans (hz.trans (hy.trans hu)),done,
    Nat.add_le_add (Nat.add_le_add hl ht) (Nat.add_le_add_right (Nat.add_le_add_right hn 2) _),
    Exec.seq (Exec.seq pack install) (Exec.seq (Exec.call run) clear)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
