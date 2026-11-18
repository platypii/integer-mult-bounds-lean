module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRowShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimensions
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord


/-! The physical row addition on the original flat array, for arbitrary earlier control. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A M d W : ℕ} [NeZero M] {P U : Type} (k t : Fin d)
local notation "N" => prefixSize (Q := M) t
local notation "B" => suffixSize (Q := M) (W := W) t
local notation "stride" => M^(t.val-1-k.val)

def shearArithmetic : Fin 15 ↪ Fin 29 := Fin.castLEEmb (by decide)
def shearTranslation : Fin 12 ↪ Fin 29 := ⟨![15,16,17,18,19,20,21,22,3,23,24,25],by decide⟩
def shearDimensions : Fin 13 ↪ Fin 29 := ⟨![2,28,1,4,5,6,7,8,9,10,14,27,20],by decide⟩

structure PrefixCopyReady (src dst tmp work : Fin T) (L extent : ℕ) (S : Stacks T A) : Prop where
  fits : extent < 2^L
  count : S.R src = binSyms L extent
  marker : S.L dst = [separator]
  dest : S.R dst = []
  temp : S.R tmp = []
  scratch : S.R work = []

/-- Install the final loop count as a canonical descriptor on the retained separator. -/
theorem installPrefixCount_exec {L extent : ℕ} (body : P → Pr P T 217 A U) (r : Fin 29 ↪ Fin T)
    (v : HS T 217 A U) (S : Stacks T A)
    (ready : PrefixCopyReady (r 13) (r 3) (r 4) (r 5) L extent S) :
    ∃ ps z, GrowingCounterData.Canonical ps ∧ Counter.value ps = extent ∧ z.user = v.user ∧
      let F : Stacks T A := {S with R := Function.update S.R (r 3) (ps.map bitSymbol)}
      Exec body (Routing.binaryCanonicalCopyProgram (r 13) (r 3) (r 4) (r 5))
        (mk v S) (10*L+12) (mk z F) ∧
      ∀ pos, CountedLoopReuseAlphabet.binary ps pos =
        readAt blank (F.L (r 3)) (F.R (r 3)) (pos-1) := by
  obtain ⟨ps,z,canon,value,_,hz,run⟩ := Routing.binaryCanonicalCopy_exec body _ _ _ _
    (by simp [List.nodup_cons,r.injective.eq_iff]) L extent ready.fits v S ready.count ready.dest ready.temp ready.scratch
  refine ⟨ps,z,canon,value,hz,run,?_⟩
  intro pos
  simp only [ready.marker,Function.update_self,readAt_single]
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  exact congrFun (encodedBinary_eq ps) pos

def scheduledShear (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (rowDimensions k t (shearDimensions.trans bank))
    (prefixShear (shearArithmetic.trans bank) (shearTranslation.trans bank) (bank 26))

private theorem powerFits (M H n b J : ℕ) (hm : M < 2^H) (hb : b < 2^J) :
    M^n*b < 2^(n*H+J) := by
  rw [pow_add,Nat.mul_comm n H,pow_mul]
  exact (Nat.mul_le_mul_right b (Nat.pow_le_pow_left hm.le n)).trans_lt
    (Nat.mul_lt_mul_of_pos_left hb (by positivity))

theorem scheduledShear_exec (hk : k < t) (c : ZMod M) (body : P → Pr P T 217 A U)
    (bank : Fin 29 ↪ Fin T) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coef : S.R (bank 0) = binSyms H c.val)
    (free : ∀ i : Fin 29, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank (shearTranslation i)) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → Fin 4)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let g := t.val-1-k.val
    let s := d-1-t.val
    let L := t.val*H+1
    let K := g*H+1
    let V := s*H+J
    ∃ z F n, z.user = v.user ∧
      n ≤ dimensionTime H 1 t.val + dimensionTime H 1 g + dimensionTime H J s +
        (6*N+17*L+4*V+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2) ∧
      Exec body (scheduledShear k t bank) (mk v S) n (mk z F) ∧
      PrefixCopyReady (bank 13) (bank 3) (bank 4) (bank 5) (t.val*H+1) (prefixSize (Q := M) t) F ∧
      ShearCounters (suffixSize (Q := M) (W := W) t) M (bank ∘ shearTranslation) F ∧
      (∀ pos : ℤ, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-(p+(M^d*W : ℕ))) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) pos)) ∧
      (∀ pos : ℤ, pos < q ∨ q+(M^d*W : ℕ) ≤ pos →
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-(q+(M^d*W : ℕ))) =
          RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∀ (x : Fin d → ZMod M) (j : Fin W),
        let y := (RowOp.shear k t hk c).apply x
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (((index y j).val : ℤ) - (M^d*W : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index x j)) := by
  let g := t.val-1-k.val
  let s := d-1-t.val
  obtain ⟨u,m,hu,hcost,prep⟩ := rowDimensions_exec k t body (shearDimensions.trans bank) H J M W
    hm hw v S base one width (by
      intro i hi hj
      fin_cases i <;> first | contradiction | exact free _ (by decide) (by decide) (by decide) (by decide) (by decide))
  let D : Stacks T A := {S with
    R := Function.update (Function.update (Function.update S.R (bank 1) (binSyms (t.val*H+1) N))
      (bank 14) (binSyms (g*H+1) stride)) (bank 20) (binSyms (s*H+J) B)}
  have keep (i : Fin 29) (a : i ≠ 1) (b : i ≠ 14) (c : i ≠ 20) : D.R (bank i) = S.R (bank i) := by
    simp [D,Function.update_of_ne (bank.injective.ne a),Function.update_of_ne (bank.injective.ne b),
      Function.update_of_ne (bank.injective.ne c)]
  have clean (i : Fin 29) (lo : 3 ≤ i) (hi : i ≤ 26) (a : i ≠ 14) (b : i ≠ 20)
      (c : i ≠ 24) (d : i ≠ 25) : D.R (bank i) = [] :=
    (keep i (by omega) a b).trans (free i (by omega) hi (by omega) c d)
  have ar : ∀ i : Fin 15, 3 ≤ i → i ≤ 12 → 3 ≤ shearArithmetic i ∧ shearArithmetic i ≤ 12 := by decide
  have tr : ∀ i : Fin 12, i < 10 → i ≠ 5 →
      3 ≤ shearTranslation i ∧ shearTranslation i ≤ 23 ∧ shearTranslation i ≠ 14 ∧ shearTranslation i ≠ 20 := by decide
  obtain ⟨z,F,n,hz,hn,run,_,ready,result⟩ := rowShear_exec k t hk c body (shearArithmetic.trans bank)
    (shearTranslation.trans bank) rfl
    (fun i hi j => bank.injective.ne ((by decide : ∀ i : Fin 15, i ≠ 3 → ∀ j, shearTranslation j ≠ shearArithmetic i) i hi j))
    (bank 26) (fun i => bank.injective.ne ((by decide : ∀ i, shearArithmetic i ≠ 26) i))
    (fun i => bank.injective.ne ((by decide : ∀ i, shearTranslation i ≠ 26) i))
    _ _ H _ (by simpa [prefixSize] using powerFits M H t.val 1 1 hm (by decide))
    (by simpa using powerFits M H g 1 1 hm (by decide)) hm (powerFits M H s W J hm hw) hW u D
    (by change D.R (bank 1) = _; simp [D,bank.injective.eq_iff])
    ((keep 13 (by decide) (by decide) (by decide)).trans (free _ (by decide) (by decide) (by decide) (by decide) (by decide)))
    (by change D.R (bank 14) = _; simp [D,bank.injective.eq_iff])
    ((keep 0 (by decide) (by decide) (by decide)).trans coef)
    ((keep 2 (by decide) (by decide) (by decide)).trans base)
    (by
      intro i hi hj
      obtain ⟨lo,up⟩ := ar i hi hj
      exact clean (shearArithmetic i) lo (by omega) (by omega) (by omega) (by omega) (by omega))
    source dest p q a ((keep 26 (by decide) (by decide) (by decide)).trans
      (free _ (by decide) (by decide) (by decide) (by decide) (by decide))) left
    (by
      intro i hi
      by_cases eqn : i = 5
      · subst i; change D.R (bank 20) = _; simp [D]
      · obtain ⟨lo,up,a,b⟩ := tr i hi eqn
        simpa [eqn] using clean (shearTranslation i) lo (by omega) a b (by omega) (by omega))
    (by change ∀ z, _ = readAt blank (S.L (bank 24)) (D.R (bank 24)) _; rw [keep 24 (by decide) (by decide) (by decide)]; exact src)
    (by change ∀ z, _ = readAt blank (S.L (bank 25)) (D.R (bank 25)) _; rw [keep 25 (by decide) (by decide) (by decide)]; exact dst)
  exact ⟨z,F,m+n,hz.trans hu,Nat.add_le_add hcost hn,Exec.seq prep run,⟨by simpa [prefixSize] using powerFits M H t.val 1 1 hm (by decide),
    ready.counter,ready.marker,ready.empty 3 (by decide) (by decide) (by decide),
    ready.empty 4 (by decide) (by decide) (by decide),ready.empty 5 (by decide) (by decide) (by decide)⟩,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
