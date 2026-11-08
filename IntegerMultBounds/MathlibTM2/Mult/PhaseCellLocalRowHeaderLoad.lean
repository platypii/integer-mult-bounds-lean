module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowCode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableBank

/-! Load the local row selector from ordinary binary s,t,a,origin,n headers.
The zero source is shared and empty; all source headers are retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def localRowSource (i : Fin 16) : Fin 117 :=
  if i = 0 then 32 else if i = 1 then 33 else if i = 2 then 34 else
    if i = 3 then 35 else if i = 15 then 36 else 37

def localRowValue (s t a origin n : ℕ) (k : Fin 117) :=
  if k = 32 then s else if k = 33 then t else if k = 34 then a else
    if k = 35 then origin else if k = 36 then n else 0

def localRowBits (W : ℕ) (k : Fin 117) := if k = 37 then 0 else W

def localRowTable (A s t a origin n : ℕ) : TblSt 16 A :=
  ⟨fun i => localRowValue s t a origin n (localRowSource i),[]⟩

def loadLocalRowHeaders : Pr P 117 Q A U := chirpBankLoad originReg localRowSource 114 115

theorem localRowSource_off (i : Fin 16) (r : TblR 16) : originReg r ≠ localRowSource i := by
  have hh := originReg_range r
  simp only [localRowSource]
  split_ifs <;> intro he <;> rw [he] at hh <;> norm_num at hh

theorem localRowHeader_fit (s t a origin n W : ℕ) (hn : 0 < n)
    (hleft : origin ≤ nearestNatural s t a)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W) :
    ∀ i, localRowValue s t a origin n (localRowSource i) <
      2^localRowBits W (localRowSource i) := by
  have hmul : t ≤ t*(a+n) := Nat.le_mul_of_pos_right t (by omega)
  have hmono := Nat.mul_le_mul_left (2*t) (show a ≤ a+n by omega)
  have hnear : nearestNatural s t a ≤ 2*t*a+s := Nat.div_le_self _ _
  have hs : s < 2^W := by omega
  have ht : t < 2^W := by nlinarith
  have ha : a < 2^W := by omega
  have ho : origin < 2^W := by omega
  have hn' : n < 2^W := by omega
  intro i
  simp only [localRowSource]
  split_ifs <;> simp [localRowValue,localRowBits] <;> assumption

theorem loadLocalRowHeaders_cost (W V : ℕ) :
    chirpBankLoadCost originReg localRowSource W V (localRowBits W) = 110*W+4*V+137 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,localRowSource,
    localRowBits,List.ofFn_succ]
  ring

theorem loadLocalRowHeaders_exec (W V s t a origin n : ℕ) (hn : 0 < n)
    (hleft : origin ≤ nearestNatural s t a) (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hW : (S.R 114).length = W) (hV : (S.R 115).length = V)
    (hs : S.R 32 = binSyms W s) (ht : S.R 33 = binSyms W t)
    (ha : S.R 34 = binSyms W a) (ho : S.R 35 = binSyms W origin)
    (hc : S.R 36 = binSyms W n) (hz : S.R 37 = [])
    (hb : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    let B := {S with R := chirpBankLoadR originReg localRowSource W V (localRowValue s t a origin n) S.R}
    ∃ v', v'.user = v.user ∧ Exec body loadLocalRowHeaders (mk v S) (110*W+4*V+137) (mk v' B) ∧
      tblHolds originReg B (tblRho W (List.replicate W tick) (List.replicate V tick)
        (localRowTable A s t a origin n)) ∧ ∀ k, 31 ≤ k.val → B.R k = S.R k := by
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hh := originReg_range r
    rw [he] at hh
    omega
  have hbits : ∀ i, localRowBits W (localRowSource i) ≤ W := by
    intro i; simp [localRowBits]; split_ifs <;> omega
  have hsrc : ∀ i, S.R (localRowSource i) = binSyms (localRowBits W (localRowSource i))
      (localRowValue s t a origin n (localRowSource i)) := by
    intro i
    simp only [localRowSource]
    split_ifs <;> simp [localRowBits,localRowValue,hs,ht,ha,ho,hc,hz,binSyms]
  have hblank : ∀ r, S.R (originReg r) = [] := fun r => hb _ (originReg_range r)
  obtain ⟨v',hu,he⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective localRowSource
    114 115 (hoff 114 (by decide)) (hoff 115 (by decide)) localRowSource_off W V
    (localRowBits W) (localRowValue s t a origin n) (localRowHeader_fit s t a origin n W hn hleft hwide)
    hbits v S hW hV hsrc hblank
  refine ⟨v',hu,he.cast (loadLocalRowHeaders_cost W V) rfl,
    chirpBankLoad_holds originReg originReg_injective localRowSource W V _ S hblank,?_⟩
  intro k hk
  exact chirpBankLoad_off originReg localRowSource W V _ S.R k (fun r => (hoff k hk r).symm)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
