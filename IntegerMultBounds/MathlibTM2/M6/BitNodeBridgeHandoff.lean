module

public import IntegerMultBounds.MathlibTM2.M6.BitNineStageHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Directed XOR bridges on the single occupied label row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)
open Certificates.PR589.Nine

private noncomputable def roleIndex := (Fintype.equivFin Role).trans (finCongr card_role)
private noncomputable def portOf (r : Role) := bankTape r.bank (r.replica,r.port,r.cls)

/-- Apply both directed additions of a bridge at one physical address. -/
noncomputable def bridgeColumn (d s : ℕ) (x : Fin 142081 → ZMod 2) : Fin 142081 → ZMod 2 :=
  Fin.lastCases (x (Fin.last 142080)) fun j =>
    let r := ((Fintype.equivFin Role).trans (finCongr card_role)).symm j
    if r.bank.val = 2*d then x j.castSucc + x (bankTape (withBank r (2*s)).bank (r.replica,r.port,r.cls))
    else if r.bank.val = 2*s+1 then x j.castSucc + x (bankTape (withBank r (2*d+1)).bank (r.replica,r.port,r.cls))
    else x j.castSucc

private theorem column_zero (d s : ℕ) (j) : bridgeColumn d s (fun _ => 0) j = 0 := by
  induction j using Fin.lastCases with
  | last => exact Fin.lastCases_last ..
  | cast j => simp [bridgeColumn]

private theorem row_bridge {w B K : ℕ} (label : Cover.LabelPadding.Label 64 w)
    (d s : ℕ) (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) j z :
    singleLabelBank label (fun j i => bridgeColumn d s (fun l => x l i) j) j z =
      bridgeColumn d s (fun l => singleLabelBank (B := B) (K := K) label x l z) j := by
  dsimp only [singleLabelBank]
  split
  · rfl
  · exact (column_zero ..).symm

private theorem column_read {V : ℕ} (d s : ℕ) (x y : Fin 142081 → Fin V → ZMod 2)
    (read : ∀ address, readLanes address y = (Piece.bridge d s).run (readLanes address x))
    (scratch : y (Fin.last 142080) = x (Fin.last 142080)) (j z) :
    y j z = bridgeColumn d s (fun l => x l z) j := by
  induction j using Fin.lastCases with
  | last => simpa only [bridgeColumn,Fin.lastCases_last] using congrFun scratch z
  | cast j =>
    let r := roleIndex.symm j
    have atRole := congrFun (congrFun (read (fun _ _ => z)) r) (fun _ => 0)
    have idx : portOf r = j.castSucc := congrArg Fin.castSucc (roleIndex.apply_symm_apply j)
    change y (portOf r) z = _ at atRole
    simp only [bridgeColumn,Fin.lastCases_castSucc]
    change y j.castSucc z = if r.bank.val = 2*d then _ else if r.bank.val = 2*s+1 then _ else _
    rw [← idx]
    have parity : 2*s+1 ≠ 2*d := by omega
    by_cases even : r.bank.val = 2*d <;> by_cases odd : r.bank.val = 2*s+1 <;>
      simp only [Piece.run,even,odd,parity,↓reduceIte,Pi.add_apply] at atRole ⊢ <;> exact atRole

/-- Every scheduled directed bridge executes both additions on the owner's
occupied row and restores the count controls for the next piece. -/
theorem bridgeHandoff (d s : ℕ) (scheduled : Piece.bridge d s ∈ nodeProgram) :
    ∃ states : ℕ, ∀ {t q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin t)
      (body : P → Pr P t q prime U), states ≤ q → ∃ code, ∀ w B tail : ℕ,
      let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*tail))
      0 < V → ∀ prepared, PieceHandoff w B tail
        (fun x y => y = fun j z => bridgeColumn d s (fun l => x l z) j)
        body code fan fan prepared (2*(76*17760*V*(142081+7)+6)+1) := by
  obtain ⟨states,build⟩ := nodeBankPiece_host (.bridge d s) scheduled (Or.inl ⟨d,s,rfl⟩)
  refine ⟨states,?_⟩
  intro t q P U fan body fits
  obtain ⟨code,run⟩ := build fan body fits
  refine ⟨code,?_⟩
  intro w B tail V pos prepared x u S live _
  let label := firstRowLabel w
  let entry := singleLabelBank (B := B) (K := (prime^w)^112*tail) label
  obtain ⟨v,D,steps,out,ran,bill,user,ready,read,scratch,_⟩ := run pos (entry x) u S live
  let y := fun j z => bridgeColumn d s (fun l => x l z) j
  have eq : entry y = out := by
    funext j z
    exact (row_bridge label d s x j z).trans (column_read d s _ _ read scratch j z).symm
  refine ⟨v,D,steps,y,ran,bill,user,?_,rfl⟩
  change HelperFan fan (entry y) D
  rw [eq]
  exact ready

end IntegerMultBounds.MathlibTM2.M6.BitNode
