module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalHeaderList
public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack

def replicaKeyHeaderFields {T : ℕ} (src dst : Fin 5 → Fin T) : List (Fin T × Fin T) :=
  List.ofFn fun i => (src i,dst i)

/-- Canonical binary fields for an arbitrary rectangular interchange. -/
def interchangeHeaderBits (outerCount middleCount blockWidth h d : ℕ) (i : Fin 5) : List Bool :=
  binBits (Nat.size (swapValues outerCount middleCount blockWidth h d i)) (swapValues outerCount middleCount blockWidth h d i)

def interchangeHeaderVolume (outerCount middleCount blockWidth h d : ℕ) : ℕ :=
  (List.ofFn fun k : Fin 5 => (interchangeHeaderBits outerCount middleCount blockWidth h d k).length+1).sum

theorem interchangeHeaderVolume_le (outerCount middleCount blockWidth h d : ℕ) :
    interchangeHeaderVolume outerCount middleCount blockWidth h d ≤
      outerCount+middleCount+blockWidth+h+d+5 := by
  have hs (n : ℕ) : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₁ := hs outerCount
  have h₂ := hs middleCount
  have h₃ := hs blockWidth
  have h₄ := hs h
  have h₅ := hs d
  simp only [interchangeHeaderVolume,interchangeHeaderBits,length_binBits]
  simp [List.ofFn_succ,swapValues]
  omega

def replicaKeyHeaderBits (W h d : ℕ) : Fin 5 → List Bool := interchangeHeaderBits 1 1 W h d

/-- Total physical length of the five generated binary headers, separators included. -/
def replicaKeyHeaderVolume (W h d : ℕ) : ℕ :=
  (List.ofFn fun k : Fin 5 => (replicaKeyHeaderBits W h d k).length+1).sum

def replicaKeyHeaders {T Q A : ℕ} {P U : Type} (src dst : Fin 5 → Fin T)
    (a half par bits cnt saved : Fin T) : Pr P T Q A U :=
  canonicalHeaderList a half par bits cnt saved (replicaKeyHeaderFields src dst)

/-- Generate all five interchange headers once from borrowed unary dimensions.
Sources may coincide (the two constant-one fields can share one master). -/
theorem interchangeHeaders_exec {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (src dst : Fin 5 → Fin T) (hdst : Function.Injective dst)
    (a half par bits cnt saved : Fin T)
    (hreg : ∀ i, [src i,dst i,a,half,par,bits,cnt,saved].Nodup)
    (hdisjoint : ∀ i j, dst i ≠ src j)
    (outerCount middleCount blockWidth h d : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (src i)).length = swapValues outerCount middleCount blockWidth h d i)
    (hblank : ∀ i, S.R (dst i) = [])
    (hfresh : ∀ i ∈ [a,half,par,bits,cnt,saved], S.R i = []) :
    let R := canonicalHeaderListR (fun i => (S.R i).length) (replicaKeyHeaderFields src dst) S.R
    ∃ v' n, v'.user = v.user ∧ n ≤ 21*(outerCount+middleCount+blockWidth+h+d)+56 ∧
      Exec body (replicaKeyHeaders src dst a half par bits cnt saved) (mk v S) n (mk v' {S with R := R}) ∧
      (∀ i, R (dst i) = separator::(interchangeHeaderBits outerCount middleCount blockWidth h d i).map bitSymbol) ∧
      (∀ j, (∀ i, dst i ≠ j) → R j = S.R j) ∧
      (∀ i, Counter.value (interchangeHeaderBits outerCount middleCount blockWidth h d i) = swapValues outerCount middleCount blockWidth h d i) ∧
      (∀ i, GrowingCounterData.Canonical (interchangeHeaderBits outerCount middleCount blockWidth h d i)) := by
  dsimp only
  let rs := replicaKeyHeaderFields src dst
  have hnd : (rs.map Prod.snd).Nodup := by
    simpa only [rs,replicaKeyHeaderFields,List.map_ofFn,Function.comp_def] using List.nodup_ofFn_ofInjective hdst
  obtain ⟨v',n,hu,hn,he⟩ := canonicalHeaderList_exec (body := body) a half par bits cnt saved
    (fun i => (S.R i).length) rs
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact hreg i) hnd
    (by intro r hr s hs; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs; exact hdisjoint i j)
    v S (by intros; rfl)
    (by intro r hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact hblank i) hfresh
  have hcost : (rs.map (fun r => 21*(S.R r.1).length+11)).sum+1 = 21*(outerCount+middleCount+blockWidth+h+d)+56 := by
    simp only [rs,replicaKeyHeaderFields,List.map_ofFn,Function.comp_def,hvalues]
    simp [List.ofFn_succ,swapValues]
    omega
  refine ⟨v',n,hu,by omega,he,?_,?_,?_,?_⟩
  · intro i
    have hh := canonicalHeaderListR_get (fun i => (S.R i).length) rs hnd S.R (src i,dst i)
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [canonicalHeaderWord,hvalues,interchangeHeaderBits] using hh
  · intro j hj
    apply canonicalHeaderListR_off
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact hj i
  · intro i
    exact Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _)
  · intro i
    exact binBits_size_canonical _


/-- Generate all five interchange headers once from borrowed unary dimensions.
Sources may coincide (the two constant-one fields can share one master). -/
theorem replicaKeyHeaders_exec {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (src dst : Fin 5 → Fin T) (hdst : Function.Injective dst)
    (a half par bits cnt saved : Fin T)
    (hreg : ∀ i, [src i,dst i,a,half,par,bits,cnt,saved].Nodup)
    (hdisjoint : ∀ i j, dst i ≠ src j)
    (W h d : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (src i)).length = swapValues 1 1 W h d i)
    (hblank : ∀ i, S.R (dst i) = [])
    (hfresh : ∀ i ∈ [a,half,par,bits,cnt,saved], S.R i = []) :
    let R := canonicalHeaderListR (fun i => (S.R i).length) (replicaKeyHeaderFields src dst) S.R
    ∃ v' n, v'.user = v.user ∧ n ≤ 21*(W+h+d+2)+56 ∧
      Exec body (replicaKeyHeaders src dst a half par bits cnt saved) (mk v S) n (mk v' {S with R := R}) ∧
      (∀ i, R (dst i) = separator::(replicaKeyHeaderBits W h d i).map bitSymbol) ∧
      (∀ j, (∀ i, dst i ≠ j) → R j = S.R j) ∧
      (∀ i, Counter.value (replicaKeyHeaderBits W h d i) = swapValues 1 1 W h d i) ∧
      (∀ i, GrowingCounterData.Canonical (replicaKeyHeaderBits W h d i)) := by
  simpa only [replicaKeyHeaderBits,Nat.one_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    interchangeHeaders_exec src dst hdst a half par bits cnt saved hreg hdisjoint
      1 1 W h d v S hvalues hblank hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
