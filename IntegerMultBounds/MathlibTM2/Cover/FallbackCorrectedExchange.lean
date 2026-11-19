module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairExchange
public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorLayout

/-! A weighted coordinate exchange with its sign corrected on private tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local notation "T" => fun (k : Fin (d+1)) => (N+1)+(22+fieldSignSlots k)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem correctedChildExchange_exec {m r Q : ℕ} (k t : Fin (d+1)) (capacity : columnCapacity ≤ Q)
    (signCapacity : (fieldSignProgram k true).1 ≤ Q) (hk : k < t) (parent : Fin m → ZMod M)
    (j : Fin m) (inv : ZMod M) (reciprocal : parent j * inv = 1) (pivot : Fin r → ZMod M)
    (i : Fin r) (unit : IsUnit (pivot i)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (T k) Q prime U) (v : HS (T k) Q prime U) (S : Stacks (T k) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M) :
    let slots := fieldSignSlots k
    let host := Fin.castAddEmb (n := N+1) (22+slots)
    let sign := extendSignBank columnBank slots
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ tail
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h).val).flatten ++ rest
    let ready := fun y (D : Stacks (T k) prime) =>
      ColumnRecordReady (columnBank.trans host) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (host (columnPorts h)) = [] ∧ D.R (host (columnPorts h)) = []) ∧ D.R (host (Fin.last N)) = weights
    let shearCost := fun neg => 1 + cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) prime j.val i.val k t neg w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) k t w W H J
    ready addr S →
    (∀ a : Fin (22+slots), a.val ≠ 17 → S.L (Fin.natAdd (N+1) a) = [] ∧ S.R (Fin.natAdd (N+1) a) = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+(2*shearCost false + shearCost true + 2*swapCost) + ((10*J+12)+(21*(w+1)+12)+1 +
        (1+(AtomSegment.chainConst (fieldSignOps k true)*(M^(d+1)*W)*(22+slots+5)+6))) ∧
      Exec body (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange j.val i.val k t))
        (.seq (installFieldHeaders ((installerPorts slots).trans sign))
          (placedFieldNeg k ((signPorts slots).trans sign) signCapacity))) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k ((inv * Ring.inverse (pivot i))*addr x t))
        t ((parent j * pivot i)*addr x k)) F := by
  intro slots host sign record weights ready shearCost swapCost before aux
  obtain ⟨u,D,n,hu,hn,exchange,next,outside⟩ := placedChildExchange_exec host capacity k t hk parent j inv reciprocal pivot i unit
    H J hm hw hW body v S tail rest dest q empty original addr before
  obtain ⟨z,F,l,hz,hl,neg,correct,saved⟩ := extendedFieldNeg_exec k columnBank signCapacity H J hw hW record dest q
    original _ body u D next.1 (by
      intro a ha
      have keep := outside (Fin.natAdd (N+1) a) (by
        intro b eq
        have val := congrArg Fin.val eq
        change b.val = (N+1)+a.val at val
        omega)
      exact ⟨keep.1.trans (aux a ha).1,keep.2.trans (aux a ha).2⟩)
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add hn hl,Exec.seq exchange neg,?_,?_,?_⟩
  · convert correct using 2
    funext a
    by_cases e : a = k <;> by_cases f : a = t <;> simp_all [Function.update]
  · intro a ha
    have keep := saved (columnPorts a) (by
      intro b eq
      have val := congrArg Fin.val eq
      change b.val = a.val at val
      omega)
    exact ⟨keep.1.trans (next.2.1 a ha).1,keep.2.trans (next.2.1 a ha).2⟩
  · apply Eq.trans _ next.2.2
    apply (saved _ _).2
    intro b eq
    have val := congrArg Fin.val eq
    change b.val = N at val
    omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
