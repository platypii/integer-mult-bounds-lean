module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.DeriveFintype

/-! A finite caller header bank outside the reusable numerical bank. Ownership
constructors prove separation; no table of pairwise address checks is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds.MathlibTM2.Fast.TableVM

inductive Role where
  | scalar (i : Fin 11)
  | geometry (format : Fin 3) (i : Fin 3)
  | ruler (format : Fin 3)
  | core | halo
  | haloFormat (format : Fin 3)
  | publication (i : Fin 7)
  | tableValue (i : Fin 12)
  | tableWidth | tableUnary | tableAcc
  | tableScratch (i : Fin 12)
  | zero | replicas | word | volume | input | output
  deriving DecidableEq, Fintype

def headerCount : ℕ := Fintype.card Role

noncomputable def header (T : ℕ) (r : Role) : Fin (T+headerCount) :=
  Fin.natAdd T (Fintype.equivFin Role r)

def bank {T : ℕ} {κ : Type} (b : κ → Fin T) : κ → Fin (T+headerCount) :=
  Fin.castAdd headerCount ∘ b

theorem header_injective (T : ℕ) : Function.Injective (header T) :=
  (Fin.natAdd_injective _ _).comp (Fintype.equivFin Role).injective

theorem bank_injective {T : ℕ} {κ : Type} (b : κ → Fin T) (hb : Function.Injective b) :
    Function.Injective (bank b) := (Fin.castAdd_injective _ _).comp hb

theorem header_ne_bank {T : ℕ} {κ : Type} (b : κ → Fin T) (r : Role) (k : κ) :
    header T r ≠ bank b k := by
  intro heq
  have hh := congrArg (fun j : Fin (T+headerCount) => j.val) heq
  have hk := (b k).isLt
  change T+(Fintype.equivFin Role r).val = (b k).val at hh
  omega

def tableRole : TblR 12 → Role
  | .v i => .tableValue i
  | .wr => .tableWidth
  | .wn => .tableUnary
  | .acc => .tableAcc
  | .z i => .tableScratch i

theorem tableRole_injective : Function.Injective tableRole := by
  intro x y h
  cases x <;> cases y <;> simp_all [tableRole]

def isTable : Role → Bool
  | .tableValue _ | .tableWidth | .tableUnary | .tableAcc | .tableScratch _ => true
  | _ => false

theorem tableRole_isTable (r : TblR 12) : isTable (tableRole r) = true := by
  cases r <;> rfl

theorem tableRole_ne (r : TblR 12) (k : Role) (hk : isTable k = false) : tableRole r ≠ k := by
  intro heq
  have hh := congrArg isTable heq
  rw [tableRole_isTable,hk] at hh
  contradiction

def masterRole (i : Fin 12) : Role :=
  if h : i.val < 10 then .scalar ⟨i.val,by omega⟩ else if i = 10 then .core else .halo

private theorem indexed_injective {α : Type} {n : ℕ} (f : Fin n → α) (index : α → Option ℕ)
    (hindex : ∀ i, index (f i) = some i.val) : Function.Injective f := by
  intro i j h
  apply Fin.ext
  simpa only [hindex,Option.some.injEq] using congrArg index h

private theorem indexed_ne {α : Type} {n : ℕ} (f : Fin n → α) (index : α → Option ℕ)
    (hindex : ∀ i, index (f i) = some i.val) (i : Fin n) (k : α) (hk : index k = none) : f i ≠ k := by
  intro h
  have hh := congrArg index h
  simp only [hindex,hk,reduceCtorEq] at hh

private def masterIndex : Role → Option ℕ
  | .scalar i => some i.val
  | .core => some 10
  | .halo => some 11
  | _ => none

private theorem masterIndex_masterRole (i : Fin 12) : masterIndex (masterRole i) = some i.val := by
  by_cases hi : i.val < 10
  · simp [masterRole,hi,masterIndex]
  by_cases h10 : i = 10
  · subst i; rfl
  have h11 : i.val = 11 := by
    have := i.isLt
    have h10' : i.val ≠ 10 := by intro h; exact h10 (Fin.ext h)
    omega
  simp [masterRole,h10,masterIndex,h11]

theorem masterRole_injective : Function.Injective masterRole :=
  indexed_injective masterRole masterIndex masterIndex_masterRole

theorem masterRole_not_table (i : Fin 12) : isTable (masterRole i) = false := by
  unfold masterRole
  split_ifs <;> rfl

def publicationRole : Fin 10 → Role :=
  ![.publication 0,.publication 1,.publication 2,.replicas,.publication 3,
    .word,.publication 4,.ruler 2,.publication 5,.publication 6]

private def publicationIndex : Role → Option ℕ
  | .publication i => some (![0,1,2,4,6,8,9] i)
  | .replicas => some 3
  | .word => some 5
  | .ruler _ => some 7
  | _ => none

private theorem publicationIndex_publicationRole (i : Fin 10) :
    publicationIndex (publicationRole i) = some i.val := by
  fin_cases i <;> rfl

theorem publicationRole_injective : Function.Injective publicationRole :=
  indexed_injective publicationRole publicationIndex publicationIndex_publicationRole

theorem publicationRole_not_table (i : Fin 10) : isTable (publicationRole i) = false := by
  fin_cases i <;> rfl

def geometryRole (format : Fin 3) : Fin 4 → Role :=
  ![.geometry format 0,.geometry format 1,.geometry format 2,.haloFormat format]

def exposureRole : Fin 8 → Role :=
  ![.geometry 1 0,.geometry 1 1,.geometry 1 2,.haloFormat 1,.ruler 1,.word,.volume,.replicas]

def routingRole : Fin 7 → Role :=
  ![.geometry 2 0,.geometry 2 1,.geometry 2 2,.haloFormat 2,.ruler 2,.word,.replicas]

def originRole : Fin 7 → Role :=
  ![routingRole 0,routingRole 1,routingRole 2,routingRole 3,routingRole 4,
    publicationRole 9,publicationRole 6]

private def originIndex : Role → Option ℕ
  | .geometry _ i => some i.val
  | .haloFormat _ => some 3
  | .ruler _ => some 4
  | .publication i => if i = 6 then some 5 else if i = 4 then some 6 else none
  | _ => none

private theorem originIndex_originRole (i : Fin 7) : originIndex (originRole i) = some i.val := by
  fin_cases i <;> rfl

theorem originRole_injective : Function.Injective originRole :=
  indexed_injective originRole originIndex originIndex_originRole

theorem publicationRole_ne_output (i : Fin 10) : publicationRole i ≠ .output :=
  indexed_ne publicationRole publicationIndex publicationIndex_publicationRole i .output rfl

theorem masterRole_ne_output (i : Fin 12) : masterRole i ≠ .output :=
  indexed_ne masterRole masterIndex masterIndex_masterRole i .output rfl

def tableRoles : List Role :=
  [.tableWidth,.tableUnary,.tableAcc]++List.ofFn Role.tableValue++List.ofFn Role.tableScratch

theorem tableRole_mem (r : TblR 12) : tableRole r ∈ tableRoles := by
  cases r with
  | v i => exact List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  | wr => simp [tableRole,tableRoles]
  | wn => simp [tableRole,tableRoles]
  | acc => simp [tableRole,tableRoles]
  | z i => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

def ownedRoles : List Role := [.core,.halo]++List.ofFn Role.haloFormat

theorem core_mem_owned : Role.core ∈ ownedRoles := by simp [ownedRoles]
theorem halo_mem_owned : Role.halo ∈ ownedRoles := by simp [ownedRoles]
theorem format_mem_owned (i : Fin 3) : Role.haloFormat i ∈ ownedRoles :=
  List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

noncomputable def masters (T : ℕ) : Fin 12 → Fin (T+headerCount) := header T ∘ masterRole
noncomputable def table (T : ℕ) : TblR 12 → Fin (T+headerCount) := header T ∘ tableRole
noncomputable def geometry (T : ℕ) (format : Fin 3) : Fin 4 → Fin (T+headerCount) := header T ∘ geometryRole format
noncomputable def exposure (T : ℕ) : Fin 8 → Fin (T+headerCount) := header T ∘ exposureRole
noncomputable def routing (T : ℕ) : Fin 7 → Fin (T+headerCount) := header T ∘ routingRole
noncomputable def publication (T : ℕ) : Fin 10 → Fin (T+headerCount) := header T ∘ publicationRole
noncomputable def origins (T : ℕ) : Fin 7 → Fin (T+headerCount) := header T ∘ originRole

theorem masters_injective (T : ℕ) : Function.Injective (masters T) :=
  (header_injective T).comp masterRole_injective

theorem table_injective (T : ℕ) : Function.Injective (table T) :=
  (header_injective T).comp tableRole_injective

theorem publication_injective (T : ℕ) : Function.Injective (publication T) :=
  (header_injective T).comp publicationRole_injective

theorem origins_injective (T : ℕ) : Function.Injective (origins T) :=
  (header_injective T).comp originRole_injective

def isOwned : Role → Bool
  | .core | .halo | .haloFormat _ => true
  | _ => false

theorem ownedRole_isOwned (r : Role) (hr : r ∈ ownedRoles) : isOwned r = true := by
  simp only [ownedRoles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at hr
  rcases hr with (rfl | rfl) | ⟨i,rfl⟩ <;> rfl

theorem retained_ne_owned (r : Role) (hr : isOwned r = false) (k : Role) (hk : k ∈ ownedRoles) : r ≠ k := by
  intro heq
  have hh := congrArg isOwned heq
  rw [hr,ownedRole_isOwned k hk] at hh
  contradiction

theorem tableRole_not_owned (r : TblR 12) : isOwned (tableRole r) = false := by cases r <;> rfl

theorem geometryRole_not_table (f : Fin 3) (i : Fin 4) : isTable (geometryRole f i) = false := by
  fin_cases i <;> rfl

theorem exposureRole_not_table (i : Fin 8) : isTable (exposureRole i) = false := by fin_cases i <;> rfl

theorem routingRole_not_table (i : Fin 7) : isTable (routingRole i) = false := by fin_cases i <;> rfl

theorem publicationRole_not_owned (i : Fin 10) : isOwned (publicationRole i) = false := by fin_cases i <;> rfl

theorem exposureRole_not_owned (i : Fin 8) (hi : i ≠ 3) : isOwned (exposureRole i) = false := by
  fin_cases i <;> first | rfl | exact False.elim (hi rfl)

theorem routingRole_not_owned (i : Fin 7) (hi : i ≠ 3) : isOwned (routingRole i) = false := by
  fin_cases i <;> first | rfl | exact False.elim (hi rfl)

theorem table_ne_header (T : ℕ) (r : TblR 12) (k : Role) (hk : isTable k = false) :
    table T r ≠ header T k := (header_injective T).ne (tableRole_ne r k hk)

theorem header_ne_owned (T : ℕ) (r : Role) (hr : isOwned r = false) (k : Role) (hk : k ∈ ownedRoles) :
    header T r ≠ header T k := (header_injective T).ne (retained_ne_owned r hr k hk)

theorem header_ne_portset (T : ℕ) (r : Role) (rs : List Role) (tag : Role → Bool)
    (hr : tag r = false) (hs : ∀ k ∈ rs, tag k = true)
    (output : Fin (T+headerCount)) (ho : output ∈ rs.map (header T)) : header T r ≠ output := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ho
  apply (header_injective T).ne
  intro heq
  have hh := congrArg tag heq
  rw [hr,hs k hk] at hh
  contradiction

theorem tableRoles_isTable (r : Role) (hr : r ∈ tableRoles) : isTable r = true := by
  simp only [tableRoles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨i,rfl⟩) | ⟨i,rfl⟩ <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
