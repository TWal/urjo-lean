/-
  This file contains the specification of the Urjo game:
  - definition of (partially filled) grids
  - validity predicate for (complete) grids
  - structure containing unique solution for (partally filled) grids
-/

inductive Color where
  | red: Color
  | blue: Color
deriving DecidableEq

structure Cell where
  color: Option Color := none
  number: Option Nat := none
deriving DecidableEq

structure Grid (n m: Nat) where
  grid: Vector (Vector Cell n) m

structure GridIndex (n m: Nat) where
  x: Fin n
  y: Fin m
deriving
  Repr,
  DecidableEq

instance {n m: Nat}: GetElem (Grid n m) (GridIndex n m) Cell (fun _ _ => True) where
  getElem := fun grid {x, y} _ => grid.grid[y.val][x.val]

def Grid.set {n m: Nat} (grid: Grid n m) (idx: GridIndex n m) (color: Color): Grid n m where
  grid := grid.grid.set idx.y.val (grid.grid[idx.y.val].set idx.x.val { color := some color, number := grid.grid[idx.y.val][idx.x.val].number } )

instance (n m: Nat): LE (Grid n m) where
  le g1 g2 :=
    ∀ idx: GridIndex n m,
      g1[idx].number = g2[idx].number ∧
      (
        g1[idx].color = none ∨
        g1[idx].color = g2[idx].color
      )

def shift {n m: Nat} (from_ to pt: Nat × Nat): Option (GridIndex n m) :=
  let xInBounds := from_.fst ≤ pt.fst + to.fst ∧ pt.fst + to.fst - from_.fst < n
  let yInBounds := from_.snd ≤ pt.snd + to.snd ∧ pt.snd + to.snd - from_.snd < m
  if h: xInBounds ∧ yInBounds then
    some {
      x :=  Fin.mk (pt.fst + to.fst - from_.fst) (by grind)
      y :=  Fin.mk (pt.snd + to.snd - from_.snd) (by grind)
    }
  else
    none

-- from batteries
def product (l₁ : List α) (l₂ : List β) : List (α × β) := l₁.flatMap fun a => l₂.map (Prod.mk a)

-- This function has tests in Urjo.Test
def makeGridIndices {n m: Nat} (size from_ to: Nat × Nat): List (GridIndex n m) :=
  (product (List.range size.fst) (List.range size.snd)).filterMap (shift from_ to)

structure Area where
  size: Nat × Nat
  from_: Nat × Nat

def Area.square33: Area where
  size := (3, 3)
  from_ := (1, 1)

def Area.row (n: Nat): Area where
  size := (n, 1)
  from_ := (0, 0)

def Area.column (m: Nat): Area where
  size := (1, m)
  from_ := (0, 0)

def Grid.getArea {n m: Nat} (grid: Grid n m) (area: Area) (to: Nat × Nat): List (Option Color) :=
  (makeGridIndices area.size area.from_ to).map (fun (idx: GridIndex n m) =>
    grid[idx].color
  )

-- TODO: use getArea, but that makes proofs a bit more nasty
def Grid.countArea {n m: Nat} (grid: Grid n m) (area: Area) (col: Color) (to: Nat × Nat): Nat :=
  (makeGridIndices area.size area.from_ to).countP (fun (idx: GridIndex n m) =>
    grid[idx].color = some col
  )

instance decidableForallGridIndex
  {n m: Nat}
  (P : GridIndex n m → Prop) [DecidablePred P]
: Decidable (∀ idx, P idx) :=
  decidable_of_iff (∀ x y, P {x, y}) ⟨ fun h idx => h idx.x idx.y, fun h x y => h {x, y}⟩

def Grid.IsComplete {n m: Nat} (grid: Grid n m): Prop :=
  ∀ idx: GridIndex n m, grid[idx].color ≠ none
deriving Decidable

def Grid.RowGood {n m: Nat} (grid: Grid n m) (y: Fin m): Prop :=
  grid.countArea (.row n) .blue (0, y.val) =
  grid.countArea (.row n) .red  (0, y.val)
deriving Decidable

def Grid.ColumnGood {n m: Nat} (grid: Grid n m) (x: Fin n): Prop :=
  grid.countArea (.column m) .blue (x.val, 0) =
  grid.countArea (.column m) .red  (x.val, 0)
deriving Decidable

def Grid.NumberGood {n m: Nat} (grid: Grid n m) (idx: GridIndex n m): Prop :=
  match grid[idx] with
  | { color := some col, number := some num } =>
    grid.countArea (.square33) col (idx.x.val, idx.y.val) = num+1
  | _ => True

instance {n m: Nat} (grid: Grid n m) (idx: GridIndex n m): Decidable (grid.NumberGood idx) :=
  by
    unfold Grid.NumberGood
    split <;>
    infer_instance

def Grid.ConsecutiveRowGood {n m: Nat} (grid: Grid n m) (y: Fin (m-1)): Prop :=
  grid.getArea (.row n) (0, y.val) ≠
  grid.getArea (.row n) (0, y.val+1)
deriving Decidable

def Grid.IsValid {n m: Nat} (grid: Grid n m): Prop :=
  grid.IsComplete ∧
  (∀ y, grid.RowGood y) ∧
  (∀ x, grid.ColumnGood x) ∧
  (∀ idx, grid.NumberGood idx) ∧
  (∀ y, grid.ConsecutiveRowGood y)
deriving Decidable

def Grid.IsSolutionFor {n m: Nat} (solution grid: Grid n m): Prop :=
  grid ≤ solution ∧
  solution.IsValid

structure UniqueSolutionFor {n m: Nat} (grid: Grid n m) where
  solution: Grid n m
  solution_good: solution.IsSolutionFor grid
  solution_unique:
    ∀ solution', solution'.IsSolutionFor grid → solution' = solution
