module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseShear

/-! A reverse row addition returns the same physical layout for its successor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

structure ShearReady (bank : Fin 35 ↪ Fin T) (H J : ℕ) (matrix : Matrix (Fin d) (Fin d) (ZMod M))
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (a : Fin (M^d*W) → α) (S : Stacks T A) : Prop where
  modulus : S.R (bank 2) = binSyms H M
  width : S.R (bank 27) = binSyms J W
  one : S.R (bank 28) = binSyms 1 1
  padded : S.R (bank 32) = binSyms H (1 : ZMod M).val
  clock : (S.R (bank 33)).length = w
  archive : S.R (bank 34) = matrixWords A H matrix ++ tail
  scratch : ∀ i ∈ shearWork, S.L (bank i) = [] ∧ S.R (bank i) = []
  src : ∀ z, readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p) =
    RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z)
  dst : ∀ z, readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q) =
    RadixToBinary.binaryEncoding.encode (dest z)

noncomputable def reverseRowTime [Fintype P] (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T)
    (k t col target pivot : Fin d) (b w W H J : ℕ) : ℕ :=
  let row := Equiv.swap col pivot target
  let readTime := fun i : Fin d => 8*((i.val*d+col.val)*H)+14*H+22
  let limit : ℕ := readTime pivot + readTime row + pivotShearTime (W := W) k t b w H J +
      (10*(t.val*H+1)+12+((327*((b^(w+1))^d*W)+2)*13+6))
  4*shearWork.length+1+(1+6*shearWork.length*shearPushBound d b bank body)*limit

/-- The pivot lookup changes setup time only. Every reverse row has the
same volume coefficient, including the cost of cleaning its work tapes. -/
theorem reverseRowTime_eq_setup_add_volume [Fintype P] (body : P → Pr P T 217 A U)
    (bank : Fin 35 ↪ Fin T) (k t col target pivot : Fin d) (b w W H J : ℕ) :
    reverseRowTime body bank k t col target pivot b w W H J =
      reverseRowTime body bank k t col target pivot b w 0 H J +
        ((1 + 6 * shearWork.length * shearPushBound d b bank body) * 9426) *
          ((b^(w+1))^d * W) := by
  have volume := split_volume (Q := b^(w+1)) (W := W) t
  simp only [reverseRowTime, pivotShearTime, suffixSize, Nat.mul_zero] at *
  rw [volume]
  ring

theorem reverseMatrixShear_ready [Fintype P] (k t col target pivot : Fin d) (hk : k < t)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix pivot col))
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (a : Fin (M^d*W) → α)
    (ready : ShearReady bank H J matrix tail sym source dest p q a S) :
    ∃ z F n word, z.user = v.user ∧
      n ≤ reverseRowTime body bank k t col target pivot b w W H J ∧
      Exec body (reverseMatrixShear k t b col target pivot bank) (mk v S) n (mk z F) ∧
      ShearReady bank H J matrix tail sym source dest p q word F ∧
      ∀ x j, word (index ((RowOp.shear k t hk (matrix (Equiv.swap col pivot target) col * Ring.inverse (matrix pivot col))).apply x) j) =
        a (index x j) := by
  have work : ∀ i : Fin 35, i ∈ shearWork ↔
      (i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25) ∨ (29 ≤ i ∧ i ≤ 31) := by decide
  have bankSize : 29 ≤ 35 := by decide
  obtain ⟨u,G,n,z,F,hz,time,run,finish,archive,headers,widthFrame,modulus,free,dst,word,src,effect⟩ :=
    reverseMatrixShear_exec k t b w sym col target hk matrix pivot hb unit body bank H J hm hw hW v S
      ready.modulus ready.one ready.width (ready.scratch 0 (by decide)).2 tail ready.archive
      (ready.scratch 29 (by decide)).2 (ready.scratch 31 (by decide)).2 ready.padded ready.clock
      (ready.scratch 30 (by decide)).2
      (fun i _ hi h2 h24 h25 => (ready.scratch i ((work i).2 (Or.inl ⟨hi,h2,h24,h25⟩))).2)
      (fun i hi => (ready.scratch _ ((by decide +revert : ∀ i : Fin 12, i < 10 →
        (shearTranslation i).castLE bankSize ∈ shearWork) i hi)).1)
      source dest p q a empty (fun z => (ready.src z).symm) (fun z => (ready.dst z).symm)
  refine ⟨z,F,_,word,hz,shear_cleanup_time_of_empty k t b col target pivot bank body run time ?_,finish,
    ⟨modulus.trans ready.modulus,(widthFrame 27 (by decide) (by decide)).trans ready.width,
     (widthFrame 28 (by decide) (by decide)).trans ready.one,(headers 32 (by decide) (by decide)).trans ready.padded,
     (congrArg List.length (headers 33 (by decide) (by decide))).trans ready.clock,archive.trans ready.archive,
     fun i hi => free i ((work i).1 hi),src,dst⟩,effect⟩
  intro j hj
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
  exact ready.scratch i hi

/-- All original payload cells are tracked through one shared machine execution. -/
def ColumnReady (bank : Fin 35 ↪ Fin T) (H J : ℕ) (matrix : Matrix (Fin d) (Fin d) (ZMod M))
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M) (S : Stacks T A) : Prop :=
  ∃ word, ShearReady bank H J matrix tail sym source dest p q word S ∧
    ∀ x j, word (index (addr x) j) = original (index x j)

theorem columnReady_shear [Fintype P] (k t col target pivot : Fin d) (hk : k < t)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix pivot col))
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → α)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (ready : ColumnReady bank H J matrix tail sym source dest p q original addr S) :
    let c := matrix (Equiv.swap col pivot target) col * Ring.inverse (matrix pivot col)
    ∃ z F n, z.user = v.user ∧ n ≤ reverseRowTime body bank k t col target pivot b w W H J ∧
      Exec body (reverseMatrixShear k t b col target pivot bank) (mk v S) n (mk z F) ∧
      ColumnReady bank H J matrix tail sym source dest p q original
        (fun x => Function.update (addr x) t (addr x t + c * addr x k)) F := by
  obtain ⟨a,layout,placed⟩ := ready
  obtain ⟨z,F,n,word,hz,time,run,next,effect⟩ := reverseMatrixShear_ready k t col target pivot hk
    matrix hb unit body bank H J hm hw hW v S tail sym source dest p q empty a layout
  exact ⟨z,F,n,hz,time,run,word,next,fun x j => (effect (addr x) j).trans (placed x j)⟩

def reverseRowAdd (k t pivot : Fin d) (b : ℕ) (bank : Fin 35 ↪ Fin T) (swap : Pr P T 217 A U) : Pr P T 217 A U :=
  if k < t then reverseMatrixShear k t b k t pivot bank else
    .seq swap (.seq (reverseMatrixShear t k b k t pivot bank) swap)

theorem columnReady_add [Fintype P] (k t pivot : Fin d) (ne : t ≠ k)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (hb : b.Prime) (unit : IsUnit (matrix pivot k))
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → α)
    (swap : Pr P T 217 A U) (swapTime : ℕ)
    (exchange : ∀ addr v D, ColumnReady bank H J matrix tail sym source dest p q original addr D →
      ∃ z F n, z.user = v.user ∧ n ≤ swapTime ∧ Exec body swap (mk v D) n (mk z F) ∧
        ColumnReady bank H J matrix tail sym source dest p q original (fun x => addr x ∘ Equiv.swap t k) F)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (ready : ColumnReady bank H J matrix tail sym source dest p q original addr S) :
    let c := matrix (Equiv.swap k pivot t) k * Ring.inverse (matrix pivot k)
    ∃ z F n, z.user = v.user ∧ n ≤ (if k < t then reverseRowTime body bank k t k t pivot b w W H J
      else swapTime + reverseRowTime body bank t k k t pivot b w W H J + swapTime) ∧
      Exec body (reverseRowAdd k t pivot b bank swap) (mk v S) n (mk z F) ∧
      ColumnReady bank H J matrix tail sym source dest p q original
        (fun x => Function.update (addr x) t (addr x t + c * addr x k)) F := by
  intro c
  by_cases hk : k < t
  · simpa only [reverseRowAdd,ite_eq_left hk] using columnReady_shear k t k t pivot hk matrix hb unit
      body bank H J hm hw hW v S tail sym source dest p q empty original addr ready
  have ht : t < k := lt_of_le_of_ne (le_of_not_gt hk) ne
  obtain ⟨u,D,l,hu,hl,first,next⟩ := exchange addr v S ready
  obtain ⟨y,E,m,hy,hm',middle,afterAdd⟩ := columnReady_shear t k k t pivot ht matrix hb unit
    body bank H J hm hw hW u D tail sym source dest p q empty original _ next
  obtain ⟨z,F,n,hz,hn,last,afterSwap⟩ := exchange _ y E afterAdd
  simp only [reverseRowAdd,ite_eq_right hk]
  refine ⟨z,F,l+(m+n),hz.trans (hy.trans hu),by omega,Exec.seq first (Exec.seq middle last),?_⟩
  convert afterSwap using 2
  funext i
  by_cases hit : i = t <;> by_cases control : i = k <;>
    simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne,c]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
