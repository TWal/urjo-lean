import Urjo.Specification

/-
  This file contains proof techniques for the Urjo game,
  that is, techniques to find the unique solution
  corresponding to a partially filled grid.
  The main workhorse is Grid.tactic,
  a lemma that sets a color on a grid
  provided you prove the opposite color leads to an impossible grid.
  Later, we provide several lemmas to prove that a grid is impossible,
  which are of the form `P grid → grid.Impossible`,
  where `P grid` is decidable.
-/

section RandomLemmas

@[ext, grind ext]
theorem Grid.ext
  {n m: Nat}
  (g1 g2: Grid n m)
  (h: ∀ (idx: GridIndex n m), g1[idx] = g2[idx])
  : g1 = g2
:= by
  cases g1
  cases g2
  simp only [Grid.mk.injEq]
  ext y h_y x h_x
  exact h { x := (Fin.mk x h_x), y := (Fin.mk y h_y) }

@[ext, grind ext]
theorem Cell.ext
  (c1 c2: Cell)
  (h1: c1.color = c2.color)
  (h2: c1.number = c2.number)
  : c1 = c2
:= by
  cases c1
  cases c2
  simp_all

instance (n m: Nat): Std.IsPartialOrder (Grid n m) where
  le_refl := by
    simp [LE.le]
  le_trans := by
    simp [LE.le]
    grind
  le_antisymm := by
    simp [LE.le]
    grind

theorem Grid.set_le
  {n m: Nat}
  (grid: Grid n m)
  (idx: GridIndex n m)
  (color: Color)
  : grid[idx].color = none →
    grid ≤ grid.set idx color
:= by
  simp only [Grid.set, LE.le]
  grind [getElem, instGetElemGridGridIndexCellTrue]

theorem Grid.set_get_color
  {n m: Nat}
  (grid: Grid n m)
  (idx: GridIndex n m)
  (col: Color)
  (idx': GridIndex n m)
  : (grid.set idx col)[idx'].color = (if idx = idx' then some col else grid[idx'].color)
:= by
  cases idx
  cases idx'
  simp only [Grid.set]
  grind [getElem, instGetElemGridGridIndexCellTrue]

theorem Grid.set_get_number
  {n m: Nat}
  (grid: Grid n m)
  (idx: GridIndex n m)
  (col: Color)
  (idx': GridIndex n m)
  : (grid.set idx col)[idx'].number = grid[idx'].number
:= by
  simp only [Grid.set]
  grind [getElem, instGetElemGridGridIndexCellTrue]

theorem Grid.set_get_color_same
  {n m: Nat}
  (grid: Grid n m)
  (idx: GridIndex n m)
  (col: Color)
  : (grid.set idx col)[idx].color = some col
:= by
  have := Grid.set_get_color grid idx col idx
  grind

theorem Grid.set_le_left
  {n m: Nat}
  (g1 g2: Grid n m)
  (idx: GridIndex n m)
  (col: Color)
  : g1 ≤ g2 →
    g2[idx].color = some col →
    g1.set idx col ≤ g2
:= by
  simp only [LE.le]
  have := Grid.set_get_color g1 idx col
  have := Grid.set_get_number g1 idx col
  grind

theorem Grid.isComplete_le
  {n m: Nat}
  (g1 g2: Grid n m)
  : g1.IsComplete → g1 ≤ g2 → g1 = g2
:= by
  simp only [Grid.IsComplete, LE.le]
  intro h_complete h_le
  grind

-- grid is only useful to unify `n` and `m`
-- on the other hand, `grind` has to inspect the definitino
-- to deduce that the value does not depend on the grid
-- TODO: use Grid.getArea, but might make proof a bit more nasty
def Grid.areaSize {n m: Nat} (_grid: Grid n m) (area: Area) (to: Nat × Nat): Nat :=
  (@makeGridIndices n m area.size area.from_ to).length

theorem Grid.countArea_le
  {n m: Nat}
  (g1 g2: Grid n m)
  (area: Area) (col: Color) (to: Nat × Nat)
  : g1 ≤ g2 →
    g1.countArea area col to ≤ g2.countArea area col to
:= by
  intro h_le
  apply List.countP_mono_left
  simp_all only [LE.le]
  grind

theorem Grid.complete_countArea
  {n m: Nat}
  (grid: Grid n m)
  (area: Area) (to: Nat × Nat)
  : grid.IsComplete →
    grid.countArea area .red to + grid.countArea area .blue to = grid.areaSize area to
:= by
  intro h_complete
  simp only [Grid.countArea, Grid.areaSize]
  have: ∀ idx: GridIndex n m, ((grid[idx].color = some Color.blue) = ¬ (grid[idx].color = some Color.red)) := by
    simp_all only [Grid.IsComplete]
    -- why grind doesn't work?
    fail_if_success grind [cases Option, cases Color]
    intro idx
    have := h_complete idx
    revert this
    match grid[idx].color with
    | none => grind
    | some .red => grind
    | some .blue => grind
  grind [List.length_eq_countP_add_countP]

end RandomLemmas

section MainTheorems

def Color.flip (col: Color): Color :=
  match col with
  | .red => .blue
  | .blue => .red

def Grid.Impossible {n m: Nat} (grid: Grid n m): Prop :=
  ∀ solution,
    grid ≤ solution →
    ¬ solution.IsValid

def Grid.tactic
  {n m: Nat}
  {grid: Grid n m}
  (idx: GridIndex n m)
  (col: Color)
  (h_unset: grid[idx].color = none)
  (h_contra: (grid.set idx col.flip).Impossible)
  (h_next: UniqueSolutionFor (grid.set idx col))
  : UniqueSolutionFor grid
where
  solution := h_next.solution
  solution_good := by
    have := h_next.solution_good
    have := Grid.set_le grid idx col
    grind [IsSolutionFor]
  solution_unique := by
    have h_next_i_j_col : h_next.solution[idx].color = col := by
      have := h_next.solution_good
      have := Grid.set_get_color_same grid idx col
      simp_all only [IsSolutionFor, LE.le]
      grind
    intro other_solution h_other_solution
    by_cases h_next.solution[idx].color = other_solution[idx].color
    · apply h_next.solution_unique
      grind [IsSolutionFor, set_le_left]
    · rename_i h_eq
      have : other_solution[idx].color = col.flip := by
        have : other_solution[idx].color ≠ none := by grind [Grid.IsSolutionFor, Grid.IsValid, Grid.IsComplete]
        revert h_eq this
        generalize other_solution[idx].color = other_col
        grind [cases Option, cases Color, Color.flip]
      exfalso
      apply h_contra other_solution
      · apply Grid.set_le_left <;> grind [Grid.IsSolutionFor]
      · grind [Grid.IsSolutionFor, Grid.IsValid]

def Grid.finish_tactic
  {n m: Nat}
  {grid: Grid n m}
  (h_valid: grid.IsValid)
  (h_complete: grid.IsComplete)
  : UniqueSolutionFor grid
where
  solution := grid
  solution_good := by
    simp [Grid.IsSolutionFor]
    grind
  solution_unique := by
    intro solution'
    have := Grid.isComplete_le grid solution'
    grind [IsSolutionFor]

theorem Grid.impossible_split
  {n m: Nat}
  {grid: Grid n m}
  (idx: GridIndex n m) (col: Color)
  : (grid.set idx col).Impossible →
    (grid.set idx col.flip).Impossible →
    grid.Impossible
:= by
  intro h_col h_flip solution h_le h_valid
  by_cases solution[idx].color = col <;> rename_i h_eq
  · apply h_col solution <;>
    grind [Grid.set_le_left]
  · apply h_flip solution
    · refine Grid.set_le_left _ _ _ _ (by assumption) ?_
      -- why grind doesn't work?
      fail_if_success grind [Grid.IsValid, Color.flip, cases Option, cases Color]
      have h_complete: solution.IsComplete := by grind [Grid.IsValid]
      have := h_complete idx
      revert this h_eq
      match solution[idx].color with
      | none => grind
      | some .blue =>
        grind [cases Color, Color.flip]
      | some .red =>
        grind [cases Color, Color.flip]
    · grind

end MainTheorems

section ImpossibleTheorems

def Grid.RowBad {n m: Nat} (grid: Grid n m) (y: Fin m) (col: Color): Prop :=
  (grid.areaSize (.row n) (0, y.val)) < 2*(grid.countArea (.row n) col (0, y.val))
deriving Decidable

theorem Grid.rowBad_imp_impossible
  {n m: Nat}
  {grid: Grid n m}
  (y: Fin m) (col: Color)
  : grid.RowBad y col → grid.Impossible
:= by
  intro h_bad solution h_le
  suffices solution.IsComplete → ¬ solution.RowGood y by
    grind [Grid.IsValid]
  intro h_complete
  simp_all only [LE.le, Grid.IsComplete, Grid.RowGood, Grid.RowBad]
  have := Grid.countArea_le grid solution (.row n) col (0, y.val) h_le
  have := Grid.complete_countArea solution (.row n) (0, y.val) h_complete
  grind [cases Color, Grid.areaSize]

def Grid.ColumnBad {n m: Nat} (grid: Grid n m) (x: Fin n) (col: Color): Prop :=
  (grid.areaSize (.column m) (x.val, 0)) < 2*(grid.countArea (.column m) col (x.val, 0))
deriving Decidable

theorem Grid.columnBad_imp_impossible
  {n m: Nat}
  {grid: Grid n m}
  (x: Fin n) (col: Color)
  : grid.ColumnBad x col → grid.Impossible
:= by
  intro h_bad solution h_le
  suffices solution.IsComplete → ¬ solution.ColumnGood x by
    grind [Grid.IsValid]
  intro h_complete
  simp_all only [LE.le, Grid.IsComplete, Grid.ColumnGood, Grid.ColumnBad]
  have := Grid.countArea_le grid solution (.column m) col (x.val, 0) h_le
  have := Grid.complete_countArea solution (.column m) (x.val, 0) h_complete
  grind [cases Color, Grid.areaSize]

def Grid.NumberBad {n m: Nat} (grid: Grid n m) (idx: GridIndex n m): Prop :=
  let areaSize := grid.areaSize (.square33) (idx.x.val, idx.y.val)
  match grid[idx] with
  | { color := some col, number := some num } =>
    num + 1 < (grid.countArea (.square33) col (idx.x.val, idx.y.val)) ∨
    areaSize < num + 1 + (grid.countArea (.square33) col.flip (idx.x.val, idx.y.val))
  | _ => False

instance {n m: Nat} (grid: Grid n m) (idx: GridIndex n m): Decidable (grid.NumberBad idx) := by
  unfold Grid.NumberBad
  split <;> infer_instance

theorem Grid.numberBad_imp_impossible
  {n m: Nat}
  {grid: Grid n m}
  (idx: GridIndex n m)
  : grid.NumberBad idx → grid.Impossible
:= by
  intro h_bad solution h_le
  suffices solution.IsComplete → ¬ solution.NumberGood idx by
    grind [Grid.IsValid]
  intro h_complete
  simp_all only [LE.le, Grid.IsComplete, Grid.NumberGood, Grid.NumberBad]
  have := Grid.countArea_le grid solution (.square33) .blue (idx.x.val, idx.y.val) h_le
  have := Grid.countArea_le grid solution (.square33) .red (idx.x.val, idx.y.val) h_le
  have := Grid.complete_countArea solution (.square33) (idx.x.val, idx.y.val) h_complete
  split
  all_goals
    simp_all
    grind [cases Color, Grid.areaSize, Color.flip]

def Grid.AreaIsComplete {n m: Nat} (grid: Grid n m) (area: Area) (to: Nat × Nat): Prop :=
  ∀ color, color ∈ grid.getArea area to → color ≠ none
deriving Decidable

theorem Grid.areaIsComplete_getArea_le
  {n m: Nat}
  (g1 g2: Grid n m)
  (area: Area) (to: Nat × Nat)
  : g1 ≤ g2 →
    g1.AreaIsComplete area to →
    g1.getArea area to = g2.getArea area to
:= by
  simp only [Grid.getArea, Grid.AreaIsComplete, LE.le]
  intro h_le h_complete
  ext
  simp
  grind

def Grid.ConsecutiveRowBad {n m: Nat} (grid: Grid n m) (y: Fin (m-1)): Prop :=
  grid.AreaIsComplete (.row n) (0, y.val) ∧
  grid.AreaIsComplete (.row n) (0, y.val+1) ∧
  grid.getArea (.row n) (0, y.val) =
  grid.getArea (.row n) (0, y.val+1)
deriving Decidable

theorem Grid.consecutiveRowBad_imp_impossible
  {n m: Nat}
  {grid: Grid n m}
  (y: Fin (m-1))
  : grid.ConsecutiveRowBad y → grid.Impossible
:= by
  intro h_bad solution h_le
  suffices solution.IsComplete → ¬ solution.ConsecutiveRowGood y by
    grind [Grid.IsValid]
  intro h_complete
  simp_all [ConsecutiveRowGood, ConsecutiveRowBad]
  have := Grid.areaIsComplete_getArea_le grid solution (.row n) (0, y.val) (by grind) (by grind)
  have := Grid.areaIsComplete_getArea_le grid solution (.row n) (0, y.val+1) (by grind) (by grind)
  grind

def Grid.ConsecutiveColumnBad {n m: Nat} (grid: Grid n m) (x: Fin (n-1)): Prop :=
  grid.AreaIsComplete (.column m) (x.val, 0) ∧
  grid.AreaIsComplete (.column m) (x.val+1, 0) ∧
  grid.getArea (.column m) (x.val, 0) =
  grid.getArea (.column m) (x.val+1, 0)
deriving Decidable

theorem Grid.consecutiveColumnBad_imp_impossible
  {n m: Nat}
  {grid: Grid n m}
  (x: Fin (n-1))
  : grid.ConsecutiveColumnBad x → grid.Impossible
:= by
  intro h_bad solution h_le
  suffices solution.IsComplete → ¬ solution.ConsecutiveColumnGood x by
    grind [Grid.IsValid]
  intro h_complete
  simp_all [ConsecutiveColumnGood, ConsecutiveColumnBad]
  have := Grid.areaIsComplete_getArea_le grid solution (.column m) (x.val, 0) (by grind) (by grind)
  have := Grid.areaIsComplete_getArea_le grid solution (.column m) (x.val+1, 0) (by grind) (by grind)
  grind

end ImpossibleTheorems

section Tactics

syntax "simp_grid_set": tactic

macro_rules
  | `(tactic| simp_grid_set) =>
    `(tactic| simp only [Color.flip, Grid.set, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Vector.set_mk, List.set_toArray, List.set_cons_zero, List.set_cons_succ])

syntax "put" term " at " " (" num ", " num ") " " by " tacticSeq : tactic

macro_rules
  | `(tactic| put $col:term at ( $x:num , $y:num ) by $tac:tacticSeq) =>
    `(tactic|
      apply Grid.tactic {x := (Fin.mk $x (by grind)), y := (Fin.mk $y (by grind))} $col rfl <;>
      simp_grid_set;
      focus $tac
    )

syntax "split_color" term " at " " (" num ", " num ") " : tactic

macro_rules
  | `(tactic| split_color $col:term at ( $x:num , $y:num )) =>
    `(tactic|
      apply Grid.impossible_split {x := (Fin.mk $x (by grind)), y := (Fin.mk $y (by grind))} $col <;>
      simp_grid_set
    )

syntax "solved" : tactic
macro_rules
  | `(tactic| solved) =>
    `(tactic| apply Grid.finish_tactic <;> decide)

syntax "bad_column" "at"  num "with" term : tactic

macro_rules
  | `(tactic| bad_column at $x:num with $col:term ) =>
    `(tactic|
      apply Grid.columnBad_imp_impossible $x $col;
      decide
    )

syntax "bad_row" "at"  num "with" term : tactic

macro_rules
  | `(tactic| bad_row at $x:num with $col:term ) =>
    `(tactic|
      apply Grid.rowBad_imp_impossible $x $col;
      decide
    )

syntax "bad_num" "at" " (" num ", " num ") " : tactic

macro_rules
  | `(tactic| bad_num at ($x:num, $y:num)) =>
    `(tactic|
      apply Grid.numberBad_imp_impossible {x := (Fin.mk $x (by grind)), y := (Fin.mk $y (by grind))};
      decide
    )

syntax "consecutive_row" "at" num : tactic

macro_rules
  | `(tactic| consecutive_row at $y:num) =>
    `(tactic|
      apply Grid.consecutiveRowBad_imp_impossible $y;
      decide
    )

syntax "consecutive_column" "at" num : tactic

macro_rules
  | `(tactic| consecutive_column at $x:num) =>
    `(tactic|
      apply Grid.consecutiveColumnBad_imp_impossible $x;
      decide
    )

end Tactics
