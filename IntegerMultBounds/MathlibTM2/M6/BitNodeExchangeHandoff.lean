module

public import IntegerMultBounds.MathlibTM2.M6.BitNineStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitBankRun

/-! The final exchange changes which owner ports the caller reads. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

def extendPermutation {k : ℕ} (p : Equiv.Perm (Fin k)) (n : ℕ) : Equiv.Perm (Fin (k+n)) :=
  finSumFinEquiv.symm.trans ((p.sumCongr (Equiv.refl (Fin n))).trans finSumFinEquiv)

theorem extendLeft {k n} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    extendPermutation p n (i.castAdd n) = (p i).castAdd n := by simp [extendPermutation]

theorem extendRight {k n} (p : Equiv.Perm (Fin k)) (i : Fin n) :
    extendPermutation p n (i.natAdd k) = i.natAdd k := by simp [extendPermutation]

private theorem permuteFan {k t V : ℕ} (p : Equiv.Perm (Fin k)) (fan : Fin (k+2) ↪ Fin t)
    (x : Fin k → Fin V → ZMod 2) (S : Stacks t prime) (live : HelperFan fan x S) :
    HelperFan ((extendPermutation p 2).toEmbedding.trans fan) (x ∘ p) S := by
  intro j z
  induction j using Fin.addCases with
  | left i =>
    have enc : SparseRoleCircuit.encoded (a := prime) (x ∘ p) i = SparseRoleCircuit.encoded x (p i) := rfl
    simpa [extendPermutation,PointwiseRoleGate.bank,Tapes.append,embStk,enc]
      using live ((p i).castAdd 2) z
  | right i =>
    simpa [extendPermutation,PointwiseRoleGate.bank,Tapes.append,embStk]
      using live (i.natAdd k) z

private theorem sideIndex (b : Fin 8) :
    let swap := fun n : ℕ => (if n%2 = 0 then n+1 else n-1)%8
    swap (swap b.val) = b.val := by revert b; decide

theorem twiceOtherSide (r : Role) : otherSide (otherSide r) = r := by
  rcases r with ⟨a,b,c,d⟩
  unfold otherSide withBank
  congr 1
  apply Fin.ext
  exact sideIndex b

def sideExchange : Equiv.Perm Role :=
  ⟨otherSide,otherSide,twiceOtherSide,twiceOtherSide⟩

noncomputable def exchangeOwner : Equiv.Perm (Fin 142081) :=
  let index := (Fintype.equivFin Role).trans (finCongr card_role)
  extendPermutation (index.symm.trans (sideExchange.trans index)) 1

theorem exchangeOwner_role (r : Role) :
    exchangeOwner (bankTape r.bank (r.replica,r.port,r.cls)) =
      bankTape (otherSide r).bank (r.replica,r.port,r.cls) := by
  change exchangeOwner ((Fin.cast card_role ((Fintype.equivFin Role) r)).castAdd 1) = _
  let index := (Fintype.equivFin Role).trans (finCongr card_role)
  change extendPermutation _ 1 ((index r).castAdd 1) = (index (otherSide r)).castAdd 1
  rw [extendLeft]
  change (index (otherSide (index.symm (index r)))).castAdd 1 = _
  rw [Equiv.symm_apply_apply]

theorem exchangeOwner_scratch : exchangeOwner (Fin.last 142080) = Fin.last 142080 := by
  change exchangeOwner ((0 : Fin 1).natAdd 142080) = _
  exact extendRight _ _

/-- Read the other side of every pair at the output port. A single host
instruction leaves the stacks and user state intact. -/
theorem exchangeSidesHandoff {P U : Type} {t q : ℕ} (w B tail : ℕ)
    (body : P → Pr P t q prime U) (fan : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime) :
    ∃ code dst, PieceHandoff w B tail (fun x y => y = x ∘ exchangeOwner) body code fan dst prepared 1 := by
  let p := extendPermutation exchangeOwner 2
  refine ⟨.act .done,p.toEmbedding.trans fan,?_⟩
  intro x u S live _
  refine ⟨u,S,1,x ∘ exchangeOwner,Exec.act .done _,le_rfl,rfl,?_,rfl⟩
  let entry := singleLabelBank (B := B) (K := (prime^w)^112*tail) (firstRowLabel w)
  have perm : entry (x ∘ exchangeOwner) = entry x ∘ exchangeOwner := by
    funext i j
    simp only [entry,singleLabelBank,Function.comp_apply]
  change HelperFan _ (entry (x ∘ exchangeOwner)) S
  rw [perm]
  exact permuteFan exchangeOwner fan (entry x) S live

/-- Supply the terminal exchange when assembling the full node. Its price is
one host step for every positive or zero word volume. -/
theorem nodeHandoffsWithExchange {U : Type} {q : ℕ} (w B tail : ℕ)
    (effect : Piece → OwnerArray w B tail → OwnerArray w B tail → Prop) (price : Piece → ℕ)
    (available : ∀ i ∈ nodeProgram, i ≠ .exchangeSides →
      ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
        (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
        PieceHandoff w B tail (effect i) body code src dst prepared (price i)) :
    let run := Function.update effect .exchangeSides (fun x y => y = x ∘ exchangeOwner)
    let cost := Function.update price .exchangeSides 1
    ∃ (P : Type) (t : ℕ) (body : P → Pr P t q prime U) (code : Pr P t q prime U)
      (src dst : Fin (142081+2) ↪ Fin t) (prepared : Stacks t prime),
      PieceHandoff w B tail (fun x y => nodeProgram.foldr (fun i cont a => ∃ b, run i a b ∧ cont b)
        (fun a => a = y) x) body code src dst prepared (nodeProgram.map cost).sum := by
  intro run cost
  apply nodeHandoffs w B tail run cost
  intro i mem
  by_cases eq : i = .exchangeSides
  · subst i
    let prepared : Stacks (142081+2) prime := ⟨[],[],fun _ => [],fun _ => []⟩
    obtain ⟨code,dst,exec⟩ := exchangeSidesHandoff (P := Empty) (U := U) (q := q) w B tail
      Empty.elim (Function.Embedding.refl _) prepared
    exact ⟨Empty,_,_,code,_,dst,prepared,by simpa only [run,cost,Function.update_self] using exec⟩
  · simpa only [run,cost,Function.update_of_ne eq] using available i mem eq

end IntegerMultBounds.MathlibTM2.M6.BitNode
