module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Size

/-! Small scalar programs used to select inverse geometry and precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblRootSuccessor : TblCode 4 :=
  .seq (tblBlock 4 [.zero 3,.zero 2,.copy 0 1] (.inc 1))
    (.loop 3 1 (tblBlock 4 [.inc 2] (.mul 2 2 3)))

def rootSuccessorValues (x : ℕ) : Fin 4 → ℕ :=
  ![x,x+1,Nat.sqrt x+1,(Nat.sqrt x+1)^2]

theorem tblRootSuccessor_do {A W e : ℕ} (st : TblSt 4 A) (x : ℕ)
    (hx : st.val 0 = x) (hroom : 4*(x+1) < 2^W) :
    TblDo A W e tblRootSuccessor st
      (fun z => z.val = rootSuccessorValues x ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (4*(Nat.sqrt x+1)+6) := by
  let N := Nat.sqrt x+1
  have hN2 : N^2 ≤ 4*(x+1) := by
    dsimp [N]
    nlinarith [Nat.sqrt_le' x,Nat.sqrt_le_self x]
  have hN : N < 2^W := (by nlinarith [Nat.le_mul_self N] : N ≤ 4*(x+1)).trans_lt hroom
  let st₁ : TblSt 4 A := ⟨Function.update (Function.update (Function.update st.val 3 0) 2 0) 1 (x+1),st.acc⟩
  have hinit : TblDo A W e (tblBlock 4 [.zero 3,.zero 2,.copy 0 1] (.inc 1)) st
      (fun z => z = st₁) 4 := TblDo.block _ _
    (by simp [tblFitsList,TblIns.fits,TblIns.exact,hx]; omega)
    (by simp [tblExactList,TblIns.exact,st₁,hx])
  let Inv := fun j (z : TblSt 4 A) =>
    z.val 0 = x ∧ z.val 1 = x+1 ∧ z.val 2 = j ∧ z.val 3 = j^2 ∧ z.acc = st.acc
  have hloop : TblDo A W e (.loop 3 1 (tblBlock 4 [.inc 2] (.mul 2 2 3))) st₁
      (Inv N) (N*4+2) := by
    apply TblDo.loop Inv N 2
    · simp [Inv,st₁,hx]
    · intro j hj z ⟨h0,h1,h2,h3,ha⟩
      have hjroot : j ≤ Nat.sqrt x := by dsimp [N] at hj; omega
      have hj2 : j^2 ≤ x := (Nat.pow_le_pow_left hjroot _).trans (Nat.sqrt_le' x)
      have hjN : j+1 ≤ N := by omega
      have hjW : (j+1)^2 < 2^W := (Nat.pow_le_pow_left hjN _).trans_lt (hN2.trans_lt hroom)
      refine ⟨by rw [h3,h1]; omega,TblDo.block _ _ ?_ ?_⟩
      · simp [tblFitsList,TblIns.fits,TblIns.exact,h2]
        exact ⟨by omega,by simpa only [pow_two] using hjW⟩
      · simp [Inv,tblExactList,TblIns.exact,h0,h1,h2,ha,pow_two]
    · intro z hz
      refine ⟨?_,hz⟩
      rcases hz with ⟨_,h1,_,h3,_⟩
      rw [h3,h1]
      have hh := Nat.lt_succ_sqrt' x
      change x < (Nat.sqrt x+1)^2 at hh
      dsimp [N]
      omega
  have hr := hinit.seq (fun z hz => by cases hz; exact hloop)
  exact hr.mono (fun z ⟨h0,h1,h2,h3,ha⟩ => ⟨by
    funext i
    fin_cases i <;> simp [rootSuccessorValues,h0,h1,h2,h3,N],ha,by
      intro i
      fin_cases i <;> simp [h0,h1,h2,h3]
      · omega
      · omega
      · exact hN
      · exact hN2.trans_lt hroom⟩) (by omega)

def tblBitCount : TblCode 4 :=
  .seq (tblBlock 4 [.copy 0 1,.inc 1,.zero 2,.inc 2] (.zero 3))
    (.loop 2 1 (tblBlock 4 [.add 2 2 2] (.inc 3)))

def bitCountValues (x : ℕ) : Fin 4 → ℕ := ![x,x+1,2^Nat.size x,Nat.size x]

theorem tblBitCount_do {A W e : ℕ} (st : TblSt 4 A) (x : ℕ)
    (hx : st.val 0 = x) (hroom : 2*(x+1) < 2^W) :
    TblDo A W e tblBitCount st
      (fun z => z.val = bitCountValues x ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (4*Nat.size x+7) := by
  have hW : W ≠ 0 := by intro he; subst W; norm_num at hroom
  let n := Nat.size x
  have hn : n ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have hpow : 2^n ≤ 2*(x+1) := by
    by_cases hn0 : n = 0
    · simp only [hn0,pow_zero]; omega
    have hlower : 2^(n-1) ≤ x := by
      have hh : ¬Nat.size x ≤ n-1 := by change ¬n ≤ n-1; omega
      have hh' : ¬x < 2^(n-1) := fun he => hh (Nat.size_le.mpr he)
      omega
    have he : n = (n-1)+1 := by omega
    rw [he,pow_succ]
    omega
  let st₁ : TblSt 4 A := ⟨Function.update (Function.update (Function.update st.val 1 (x+1)) 2 1) 3 0,st.acc⟩
  have hinit : TblDo A W e (tblBlock 4 [.copy 0 1,.inc 1,.zero 2,.inc 2] (.zero 3)) st
      (fun z => z = st₁) 5 := TblDo.block _ _
    (by simp [tblFitsList,TblIns.fits,TblIns.exact,hx]; omega)
    (by simp [tblExactList,TblIns.exact,st₁,hx])
  let Inv := fun j (z : TblSt 4 A) =>
    z.val 0 = x ∧ z.val 1 = x+1 ∧ z.val 2 = 2^j ∧ z.val 3 = j ∧ z.acc = st.acc
  have hloop : TblDo A W e (.loop 2 1 (tblBlock 4 [.add 2 2 2] (.inc 3))) st₁
      (Inv n) (n*4+2) := by
    apply TblDo.loop Inv n 2
    · simp [Inv,st₁,hx]
    · intro j hj z ⟨h0,h1,h2,h3,ha⟩
      have hjpow : 2^j ≤ x := by
        have hh : ¬x < 2^j := fun he => Nat.not_le_of_lt hj (Nat.size_le.mpr he)
        omega
      refine ⟨by rw [h2,h1]; omega,TblDo.block _ _ ?_ ?_⟩
      · simp [tblFitsList,TblIns.fits,TblIns.exact,h2,h3]
        constructor <;> omega
      · refine ⟨?_,?_,?_,?_,?_⟩
        · simpa [tblExactList,TblIns.exact] using h0
        · simpa [tblExactList,TblIns.exact] using h1
        · simp [tblExactList,TblIns.exact,h2,pow_succ]; ring
        · simp [tblExactList,TblIns.exact,h3]
        · simpa [tblExactList,TblIns.exact] using ha
    · intro z hz
      refine ⟨?_,hz⟩
      rcases hz with ⟨_,h1,h2,_,_⟩
      rw [h2,h1]
      have hh : x < 2^n := Nat.lt_size_self x
      omega
  have hr := hinit.seq (fun z hz => by cases hz; exact hloop)
  exact hr.mono (fun z ⟨h0,h1,h2,h3,ha⟩ => ⟨by
    funext i
    fin_cases i <;> simp [bitCountValues,h0,h1,h2,h3,n],ha,by
      intro i
      fin_cases i <;> simp [h0,h1,h2,h3]
      · omega
      · omega
      · exact hpow.trans_lt hroom
      · omega⟩) (by omega)

/-- Count bits in any four distinct registers, retaining the source and every spectator. -/
theorem tblBitCount_at {n A W e : ℕ} (f : Fin 4 → Fin n) (hf : Function.Injective f)
    (st : TblSt n A) (x : ℕ) (hx : st.val (f 0) = x) (hroom : 2*(x+1) < 2^W)
    (hfit : ∀ i, st.val i < 2^W) :
    TblDo A W e (tblBitCount.rename f) st
      (fun z => z.val (f 3) = Nat.size x ∧ z.acc = st.acc ∧
        (∀ i, i ≠ f 1 → i ≠ f 2 → i ≠ f 3 → z.val i = st.val i) ∧
        ∀ i, z.val i < 2^W) (4*Nat.size x+7) := by
  have h := (tblBitCount_do (A := A) (W := W) (e := e) (st.restrict f) x hx hroom).rename hf
  exact h.mono (fun z ⟨⟨hv,ha,hvfit⟩,hoff⟩ => by
    refine ⟨congrFun hv 3,ha,?_,?_⟩
    · intro i h1 h2 h3
      by_cases h0 : i = f 0
      · subst i
        exact (congrFun hv 0).trans hx.symm
      · exact hoff i (by intro j; fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3)
    · intro i
      by_cases hi : ∃ j, f j = i
      · obtain ⟨j,rfl⟩ := hi
        exact hvfit j
      · rw [hoff i (by intro j he; exact hi ⟨j,he⟩)]
        exact hfit i) (le_refl _)

/-- Binary table execution preserves the word bound, including untouched variables. -/
theorem tblDo_with_fits {n A W e K : ℕ} {c : TblCode n} {st : TblSt n A}
    {Post : TblSt n A → Prop} (h : TblDo A W e c st Post K) (hfit : ∀ i, st.val i < 2^W) :
    TblDo A W e c st (fun z => Post z ∧ ∀ i, z.val i < 2^W) K := by
  obtain ⟨z,k,hbig,hpost,hcost⟩ := h
  exact ⟨z,k,hbig,⟨hpost,hbig.lt hfit⟩,hcost⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
