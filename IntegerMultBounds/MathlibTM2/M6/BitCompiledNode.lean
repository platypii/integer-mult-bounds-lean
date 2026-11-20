module

public import IntegerMultBounds.MathlibTM2.M6.BitBankRun

/-! Compilation and join costs for the ordered PR589 owner-tape schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)

abbrev OwnerStage (V : ℕ) := SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))

/-- Only the final idle has no child. -/
noncomputable def physicalPiece {V : ℕ} (inv idle : Fin 9 → OwnerStage V)
    (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V) : Piece → OwnerStage V
  | .stage n => inv n
  | .remainder i => if h : i < 9 then idle ⟨i,h⟩ else SharedBankStage.identity _ (by decide)
  | .bridge d s => bridge d s
  | .exchangeSides => exchange

open IntegerMultBounds.Networks.Certificates.PR589.Nine BitHosting in
/-- Both endpoints of the last idle are at level nine. Its logical action
agrees with the halt used for this entry of the compiled schedule. -/
theorem terminalIdle_run (X : State) : (Piece.remainder 9).run X = X := by
  funext ρ
  have empty (k : ℕ) : interval (63+k) 63 = 0 := by
    rw [interval, ← Matrix.diagonal_zero]
    congr 1
    funext p
    simp only [ite_eq_right_iff]
    omega
  have span : remainderSpan 9 ρ = 0 := by
    change (port ρ.port.val).span (63+_) 63 = 0
    rw [PortCertificate.span,empty,Matrix.mul_zero,Matrix.zero_mul]
  simp only [Piece.run,span,exchange_zero,along_one,ite_self]

noncomputable def compiledNode {V : ℕ} (inv idle : Fin 9 → OwnerStage V)
    (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V) : OwnerStage V :=
  SharedBankStage.compile _ (by decide) (nodeProgram.map (physicalPiece inv idle bridge exchange))

theorem compiledNode_transform {V : ℕ} (inv idle : Fin 9 → OwnerStage V)
    (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V) (data) :
    (compiledNode inv idle bridge exchange).transform data =
      nodeProgram.foldl (fun x p => (physicalPiece inv idle bridge exchange p).transform x) data := by
  simp only [compiledNode,SharedBankStage.compile_transform,SharedBankStage.execute,List.foldl_map]

def bridgeEdges : List (ℕ × ℕ) := nodeProgram.filterMap fun p =>
  match p with
  | .bridge d s => some (d,s)
  | _ => none

private def pieceBill (a b : Fin 9 → ℕ) (c : ℕ → ℕ → ℕ) (e : ℕ) : Piece → ℕ
  | .stage n => a n
  | .remainder i => if h : i < 9 then b ⟨i,h⟩ else 0
  | .bridge d s => c d s
  | .exchangeSides => e

private theorem scheduleBill (a b : Fin 9 → ℕ) (c : ℕ → ℕ → ℕ) (e : ℕ) :
    (nodeProgram.map (pieceBill a b c e)).sum =
      (∑ n, a n) + (∑ i, b i) + (bridgeEdges.map (fun p => c p.1 p.2)).sum + e := by
  let ns := List.finRange 9
  have perm : nodeProgram.Perm (ns.map Piece.stage ++ ns.map (fun i => Piece.remainder i.val) ++
      bridgeEdges.map (fun p => Piece.bridge p.1 p.2) ++ [.remainder 9,.exchangeSides]) := by decide +kernel
  rw [(perm.map (pieceBill a b c e)).sum_eq]
  have ranks (f : Fin 9 → ℕ) : (ns.map f).sum = ∑ i, f i := by
    simpa only [ns,List.ofFn_eq_map] using (List.sum_ofFn : (List.ofFn f).sum = _)
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,pieceBill,dite_eq_left (Fin.isLt _),Fin.eta,
    dite_eq_right (by decide : ¬9 < 9),ranks,add_zero,zero_add]

theorem compiledNode_cost {V : ℕ} (inv idle : Fin 9 → OwnerStage V)
    (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V) :
    (compiledNode inv idle bridge exchange).cost =
      (∑ n, (inv n).cost) + (∑ i, (idle i).cost) +
        (bridgeEdges.map (fun e => (bridge e.1 e.2).cost)).sum + exchange.cost + 29 := by
  rw [compiledNode,SharedBankStage.compile_cost]
  have bill (p : Piece) : (physicalPiece inv idle bridge exchange p).cost =
      pieceBill (fun n => (inv n).cost) (fun i => (idle i).cost)
        (fun d s => (bridge d s).cost) exchange.cost p := by
    cases p with
    | remainder i => by_cases h : i < 9 <;> simp [physicalPiece,pieceBill,h,SharedBankStage.identity]
    | _ => rfl
  simp only [List.map_map,Function.comp_def,bill,List.length_map,scheduleBill,
    show nodeProgram.length = 29 from rfl]

def BankActions {V : ℕ} (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V) : Prop :=
  (∀ e ∈ bridgeEdges, ∀ data, let d := e.1; let s := e.2
        let tape := fun b : ℕ => bankTape (Fin.ofNat 8 b)
        (∀ x i, (bridge d s).transform data (tape (2*d) x) i =
          data (tape (2*d) x) i + data (tape (2*s) x) i) ∧
        (∀ x i, (bridge d s).transform data (tape (2*s+1) x) i =
          data (tape (2*s+1) x) i + data (tape (2*d+1) x) i) ∧
        ∀ j, (∀ x, tape (2*d) x ≠ j) → (∀ x, tape (2*s+1) x ≠ j) →
          (bridge d s).transform data j = data j) ∧
      ∀ data, let tape := fun ρ : Role => bankTape ρ.bank (ρ.replica,ρ.port,ρ.cls)
        (∀ ρ, exchange.transform data (tape ρ) = data (tape (otherSide ρ))) ∧
        exchange.transform data (Fin.last 142080) = data (Fin.last 142080)

open IntegerMultBounds.Networks.Certificates.PR589.Nine

/-- Read each role at the same physical address for a given logical coordinate. -/
noncomputable def readRoles {V : ℕ} (address : (Axis ⊕ Axis → ℚ) → Fin V)
    (data : Fin 142081 → Fin V → ZMod 2) : State :=
  fun ρ z => data (bankTape ρ.bank (ρ.replica,ρ.port,ρ.cls)) (address z)

theorem BankActions.bridge_read {V : ℕ} {bridge : ℕ → ℕ → OwnerStage V} {exchange}
    (acts : BankActions bridge exchange) {d s : ℕ} (scheduled : (d,s) ∈ bridgeEdges)
    (address) (data) : readRoles address ((bridge d s).transform data) =
      (Piece.bridge d s).run (readRoles address data) := by
  have bounds : ∀ e ∈ bridgeEdges, e.1 < 4 ∧ e.2 < 4 := by decide
  obtain ⟨hd,hs⟩ := bounds _ scheduled
  change d < 4 at hd
  change s < 4 at hs
  obtain ⟨even,odd,off⟩ := acts.1 _ scheduled data
  funext ρ z
  let x : BankLane := (ρ.replica,ρ.port,ρ.cls)
  have bank (n : ℕ) (h : ρ.bank.val = n) : ρ.bank = Fin.ofNat 8 n := by
    subst n; exact Fin.ext (Nat.mod_eq_of_lt ρ.bank.isLt).symm
  by_cases a : ρ.bank.val = 2*d
  · simp only [Piece.run,ite_eq_left a,Pi.add_apply,readRoles,withBank]
    simpa only [bank _ a,x,Fin.ofNat] using even x (address z)
  by_cases b : ρ.bank.val = 2*s+1
  · simp only [Piece.run,ite_eq_right a,ite_eq_left b,Pi.add_apply,readRoles,withBank]
    simpa only [bank _ b,x,Fin.ofNat] using odd x (address z)
  · simp only [Piece.run,a,b,ite_false,readRoles]
    apply congrFun (off _ _ _) (address z)
    all_goals
      intro y h
      have eq := congrArg Fin.val (bankTape_eq.mp h).1
      simp only [Fin.val_ofNat] at eq
      omega

theorem BankActions.exchange_read {V : ℕ} {bridge : ℕ → ℕ → OwnerStage V} {exchange}
    (acts : BankActions bridge exchange) (address) (data) :
    readRoles address (exchange.transform data) = Piece.exchangeSides.run (readRoles address data) := by
  funext ρ z
  exact congrFun ((acts.2 data).1 ρ) (address z)

/-- For a fixed address interpretation, correctness of the complete schedule reduces
to the nine invocation and nine nonempty idle reads. -/
theorem compiledNode_read {V : ℕ} (inv idle : Fin 9 → OwnerStage V)
    {bridge : ℕ → ℕ → OwnerStage V} {exchange} (acts : BankActions bridge exchange)
    (address : (Axis ⊕ Axis → ℚ) → Fin V)
    (sweep : ∀ n data, readRoles address ((inv n).transform data) =
      (Piece.stage n).run (readRoles address data))
    (rest : ∀ i : Fin 9, ∀ data, readRoles address ((idle i).transform data) =
      (Piece.remainder i.val).run (readRoles address data)) (data) :
    readRoles address ((compiledNode inv idle bridge exchange).transform data) =
      runNode (readRoles address data) := by
  have piece (p) (hp : p ∈ nodeProgram) (y) :
      readRoles address ((physicalPiece inv idle bridge exchange p).transform y) =
        p.run (readRoles address y) := by
    cases p with
    | stage n => exact sweep n y
    | exchangeSides => exact acts.exchange_read address y
    | bridge d s =>
      apply acts.bridge_read
      apply List.mem_filterMap.mpr
      exact ⟨.bridge d s,hp,rfl⟩
    | remainder i =>
      by_cases hi : i < 9
      · simpa only [physicalPiece,dite_eq_left hi] using rest ⟨i,hi⟩ y
      · have last : i = 9 := by simp [nodeProgram] at hp; omega
        subst i
        exact (terminalIdle_run _).symm
  have go (ps : List Piece) (inside : ∀ p ∈ ps, p ∈ nodeProgram) (y) :
      readRoles address (ps.foldl (fun x p => (physicalPiece inv idle bridge exchange p).transform x) y) =
        runPieces ps (readRoles address y) := by
    induction ps generalizing y with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.foldl_cons,runPieces]
      rw [← piece p (inside p List.mem_cons_self) y]
      exact ih (fun q h => inside q (List.mem_cons_of_mem _ h)) _
  rw [compiledNode_transform]
  exact go _ (fun _ h => h) _

/-- Fill all nine bridge occurrences and the final exchange with owner-tape programs.
Only the invocation and remainder stages contribute recursive charges. -/
theorem compiledNode_linear {V : ℕ} (positive : 0 < V) (inv idle : Fin 9 → OwnerStage V) :
    ∃ (bridge : ℕ → ℕ → OwnerStage V) (exchange : OwnerStage V),
      (compiledNode inv idle bridge exchange).cost ≤
        (∑ n, (inv n).cost) + (∑ i, (idle i).cost) +
          9*(2*(76*17760*V)+1) + (4*(3*(76*17760*V)+2)+3) + 29 ∧
      BankActions bridge exchange := by
  classical
  have valid : ∀ e ∈ bridgeEdges, e.1 < 4 ∧ e.2 < 4 ∧ e.1 ≠ e.2 := by decide
  have built (e : ℕ × ℕ) (h : e ∈ bridgeEdges) := bridge_stage
    ⟨e.1,(valid e h).1⟩ ⟨e.2,(valid e h).2.1⟩ (fun eq => (valid e h).2.2 (congrArg Fin.val eq)) positive
  let bridge := fun d s => if h : (d,s) ∈ bridgeEdges then (built (d,s) h).choose
    else SharedBankStage.identity _ (by decide)
  obtain ⟨exchange,bill,action⟩ := exchangeSides_roles positive
  refine ⟨bridge,exchange,?_,?_,action⟩
  · have prices (e) (h : e ∈ bridgeEdges) : (bridge e.1 e.2).cost ≤ 2*(76*17760*V)+1 := by
      simpa only [bridge,dite_eq_left h] using ((built e h).choose_spec).1
    have total := List.sum_le_sum (l := bridgeEdges) prices
    rw [compiledNode_cost]
    simp only [List.map_const',List.sum_replicate,smul_eq_mul,show bridgeEdges.length = 9 from rfl] at total
    omega
  · intro e h data
    have small (n : ℕ) (hn : n < 8) : Fin.ofNat 8 n = ⟨n,hn⟩ := Fin.ext (Nat.mod_eq_of_lt hn)
    obtain ⟨hd,hs,_⟩ := valid e h
    simpa only [bridge,dite_eq_left h,small _ (by omega : 2*e.1 < 8),
      small _ (by omega : 2*e.2 < 8),small _ (by omega : 2*e.1+1 < 8),
      small _ (by omega : 2*e.2+1 < 8)] using ((built e h).choose_spec).2 data

end IntegerMultBounds.MathlibTM2.M6.BitNode
