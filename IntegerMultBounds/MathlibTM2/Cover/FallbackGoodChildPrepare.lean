module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildWeights
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodIncoming

/-! Prepare both child weight vectors directly from the good record's pivot archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm
open HeadPivotLayout HeadWidthLayout CrossWeightLayout
variable {P U : Type} {T Q A d b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

namespace GoodChildLayout
def parent : Fin 55 ↪ Fin 57 := Fin.castLEEmb (by decide)
def weights : Fin 22 ↪ Fin 57 :=
  ⟨fun i => ⟨if i.val < 20 then 29+i.val else 35+i.val,by split <;> omega⟩,
   fun i j eq => Fin.ext (by have := congrArg Fin.val eq; dsimp at this; split_ifs at this <;> omega)⟩

theorem weightPort (i : Fin 20) :
    weights (i.castLE (by decide)) = parent (adapterBank (head (child i))) := by revert i; decide
def parentWithWeights : Fin 57 ↪ Fin 58 := Fin.castLEEmb (by decide)
def middlePorts : Fin 10 ↪ Fin 58 := ⟨![2,28,57,0,1,3,4,5,6,7],by decide⟩

/-- A nested middle-field operation reads its seed from its parent's output.
The child writes the new size into its own private slot 57. -/
def nestedMiddleHost {n : ℕ} (caller : Fin 58 ↪ Fin n) : Fin 58 ↪ Fin (n+58) :=
  (Fin.natAddEmb n).trans
    (Equiv.swap ((28 : Fin 58).natAdd n) ((caller 57).castAdd 58)).toEmbedding

theorem nestedMiddleHost_seed {n : ℕ} (caller : Fin 58 ↪ Fin n) :
    nestedMiddleHost caller 28 = (caller 57).castAdd 58 := by simp [nestedMiddleHost]

theorem nestedMiddleHost_shared {n : ℕ} (caller : Fin 58 ↪ Fin n) (j : Fin 58) (ne : j ≠ 28) :
    nestedMiddleHost caller j = j.natAdd n := by
  apply Equiv.swap_apply_of_ne_of_ne ((Fin.natAddEmb n).injective.ne ne)
  intro eq
  have h := congrArg Fin.val eq
  change n+j.val = (caller 57).val at h
  have := (caller 57).isLt
  omega

end GoodChildLayout

/-- The two words written for a pivot are the value and inverse of one child weight. -/
noncomputable abbrev pivotWeights {R : Type*} [CommRing R] {m r : ℕ} (hr : r ≤ m)
    (parent inv : Fin m → R) (reciprocal : ∀ j, parent j * inv j = 1)
    (pivot : Fin r → R) (unit : ∀ i, IsUnit (pivot i)) (i : Fin r) : Rˣ :=
  let j := i.castLE hr
  let cancel : (parent j*pivot i)*(inv j*Ring.inverse (pivot i)) = 1 := by
    rw [mul_mul_mul_comm,reciprocal,Ring.mul_inverse_cancel _ (unit i),one_mul]
  ⟨parent j*pivot i,inv j*Ring.inverse (pivot i),cancel,(mul_comm ..).trans cancel⟩

theorem prepareGoodChild_exec (body : P → Pr P T Q A U) (host : Fin 57 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (r : ℕ) (hr : r ≤ d)
    (minor : ∀ j (hj : j < r), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weight inv : Fin d → ZMod M) (inverse : ∀ j, weight j * inv j = 1)
    (hb : b.Prime) (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail rest : List (Fin (A+4))) :
    let machine := GoodChildLayout.parent.trans host
    let c := child.trans (head.trans (adapterBank.trans machine))
    let bank := GoodChildLayout.weights.trans host
    let stage := stageAt G r hr minor r le_rfl
    let pivot := fun i : Fin r => stage.M (i.castLE hr) (i.castLE hr)
    S.R (c 19) = (List.ofFn fun j => binSyms H (weight j).val).flatten ++ rest →
    S.R (c 18) = (List.ofFn fun i => binSyms H (pivot i).val).flatten ++ tail →
    S.R (c 4) = binSyms H M → S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 → S.R (c k) = []) →
    let childWeights := pivotWeights hr weight inv inverse pivot (fun i => stage.unit _ i.isLt)
    let pos := (List.ofFn fun i => binSyms H (childWeights i : ZMod M).val).flatten
    let reciprocal := (List.ofFn fun i => binSyms H (childWeights i).inv.val).flatten
    ∃ z t, z.user = v.user ∧ t ≤ ((List.finRange r).map (fun i => childWeightTime b w H i.val)).sum+1 ∧
      Exec body (childWeightList b bank (List.finRange r)) (mk v S) t
        (mk z {S with R := Function.update (Function.update S.R (host 55) (pos ++ S.R (host 55))) (host 56) (reciprocal ++ S.R (host 56))}) := by
  intro machine c bank stage pivot packed pivots modulus one clock scratch childWeights pos reciprocal
  have ports (i : Fin 20) : bank (i.castLE (by decide)) = c i := congrArg host (GoodChildLayout.weightPort i)
  obtain ⟨z,t,hz,ht,run⟩ := childWeightList_exec body bank weight inv pivot hr (List.finRange r) inverse
    (fun i => stage.unit _ i.isLt) hb H hm v S tail rest packed pivots modulus one clock
    (fun k hk => (ports k) ▸ scratch k hk)
  refine ⟨z,t,hz,ht,?_⟩
  simpa only [pos,reciprocal,childWeights,pivotWeights,List.flatMap_def,List.ofFn_eq_map,show bank 20 = host 55 from rfl,show bank 21 = host 56 from rfl] using run

/-- A recursive frame may keep its inherited middle size on a separate tape
from the unit used by the ordinary column. Only the destination is modified. -/
theorem rankDescriptorMiddle_exec {N : ℕ} (body : P → Pr P T Q A U) (ports : Fin 10 ↪ Fin T)
    (parent : RecursiveInterchangeLayout.Descriptor) (r g H J : ℕ) (hm : N < 2^H)
    (fits : parent.between < 2^J) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (ports 0) = binSyms H N) (seed : S.R (ports 1) = binSyms J parent.between)
    (work : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (ports i) = []) :
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H J (g+g) ∧
      Exec body (dimensionPower ports (g+g)) (mk v S) t (mk z {S with R := Function.update S.R (ports 2) (binSyms ((g+g)*H+J) (rankDescriptor N r g parent).between)}) := by
  obtain ⟨z,t,hz,ht,run⟩ := dimensionPower_exec body (g+g) ports H J N parent.between hm fits v S base seed work
  have size : N^(g+g)*parent.between = (rankDescriptor N r g parent).between := by
    simp only [rankDescriptor,pow_add]; ring
  exact ⟨z,t,hz,ht,size ▸ run⟩

/-- Read the inherited size in place and leave every parent and child tape
unchanged except the new child descriptor word. -/
theorem nestedMiddle_exec {n N : ℕ} (caller : Fin 58 ↪ Fin n) (body : P → Pr P (n+58) Q A U)
    (parent : RecursiveInterchangeLayout.Descriptor) (r g H J : ℕ) (hm : N < 2^H)
    (fits : parent.between < 2^J) (v : HS (n+58) Q A U) (S : Stacks (n+58) A)
    (base : S.R ((2 : Fin 58).natAdd n) = binSyms H N)
    (seed : S.R ((caller 57).castAdd 58) = binSyms J parent.between)
    (free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R ((GoodChildLayout.middlePorts i).natAdd n) = []) :
    let ports := GoodChildLayout.middlePorts.trans (GoodChildLayout.nestedMiddleHost caller)
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H J (g+g) ∧
      Exec body (dimensionPower ports (g+g)) (mk v S) t
        (mk z {S with R := Function.update S.R ((57 : Fin 58).natAdd n) (binSyms ((g+g)*H+J) (rankDescriptor N r g parent).between)}) := by
  intro ports
  have shared (i : Fin 10) (ne : GoodChildLayout.middlePorts i ≠ 28) :
      ports i = (GoodChildLayout.middlePorts i).natAdd n := GoodChildLayout.nestedMiddleHost_shared caller _ ne
  have run := rankDescriptorMiddle_exec body ports parent r g H J hm fits v S
    (by rw [shared 0 (by decide)]; exact base)
    (by change S.R (GoodChildLayout.nestedMiddleHost caller 28) = _; rw [GoodChildLayout.nestedMiddleHost_seed]; exact seed)
    (fun i lo hi => by rw [shared i ((by decide : ∀ i : Fin 10, 2 ≤ i → GoodChildLayout.middlePorts i ≠ 28) i lo)]; exact free i lo hi)
  simpa only [shared 2 (by decide),show GoodChildLayout.middlePorts 2 = 57 from rfl] using run

/-- The two inactive slices form one spectator field. Compute its size from
the live modulus and the inherited middle size while preserving the packed child weights. -/
theorem goodChildMiddle_exec {N : ℕ} (body : P → Pr P T Q A U) (host : Fin 58 ↪ Fin T)
    (parent : RecursiveInterchangeLayout.Descriptor) (r g H J : ℕ) (hm : N < 2^H) (fits : parent.between < 2^J) (v : HS T Q A U) (S : Stacks T A)
    (base : S.R (host 2) = binSyms H N) (seed : S.R (host 28) = binSyms J parent.between)
    (free : S.R (host 57) = [])
    (scratch : ∀ j ∈ headShearWork, S.R (host (GoodChildLayout.parentWithWeights
      (GoodChildLayout.parent (adapterBank (entry j))))) = []) :
    let desc := rankDescriptor N r g parent
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H J (g+g) ∧
      Exec body (dimensionPower (GoodChildLayout.middlePorts.trans host) (g+g)) (mk v S) t
        (mk z {S with R := Function.update S.R (host 57) (binSyms ((g+g)*H+J) desc.between)}) := by
  intro desc
  have work : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (host (GoodChildLayout.middlePorts i)) = [] := by
    intro i lo hi
    by_cases eq : i = 2
    · subst i; exact free
    · obtain ⟨j,hj,same⟩ := (by decide : ∀ k : Fin 10, 2 < k → k < 9 → ∃ j ∈ headShearWork,
          GoodChildLayout.middlePorts k = GoodChildLayout.parentWithWeights
            (GoodChildLayout.parent (adapterBank (entry j)))) i (by omega) hi
      rw [same]
      exact scratch j hj
  exact rankDescriptorMiddle_exec body (GoodChildLayout.middlePorts.trans host) parent r g H J hm fits v S base seed work

end IntegerMultBounds.MathlibTM2.Cover.Fallback
