import Urjo.Proof

/-
  This file contains a proof for the tutorial of the Urjo game.
-/

def tutorialGrid: Grid 4 4 where
  grid := #v[
    #v[{color := some .red},                    {},                  {}, {}],
    #v[{color := some .red,  number := some 2}, {},                  {}, {}],
    #v[{color := some .blue},                   {number := some 4} , {}, {color := some .blue}],
    #v[{},                                      {},                  {}, {}],
  ]

-- It seems that Lean does not provide incremental proofs when the example type is not in `Prop`.
-- To work around this we use `Nonempty`
example: Nonempty (UniqueSolutionFor tutorialGrid) := by
  apply Nonempty.intro
  unfold tutorialGrid

  put .blue at (0, 3) by
    apply Grid.columnBad_imp_impossible 0 .red
    decide

  put .red at (1, 2) by
    apply Grid.lineBad_imp_impossible 2 .blue
    decide

  put .red at (2, 2) by
    apply Grid.lineBad_imp_impossible 2 .blue
    decide

  put .blue at (1, 0) by
    apply Grid.numberBad_imp_impossible {x := (Fin.mk 0 (by grind)), y := (Fin.mk 1 (by grind))}
    decide

  put .blue at (1, 1) by
    apply Grid.numberBad_imp_impossible {x := (Fin.mk 0 (by grind)), y := (Fin.mk 1 (by grind))}
    decide

  put .red at (1, 3) by
    apply Grid.columnBad_imp_impossible 1 .blue
    decide

  put .blue at (2, 3) by
    split_color .red at (3, 3)
    · apply Grid.lineBad_imp_impossible 3 .red
      decide
    · apply Grid.consecutiveLineBad_imp_impossible 2
      decide

  put .red at (3, 3) by
    apply Grid.lineBad_imp_impossible 3 .blue
    decide

  put .red at (2, 1) by
    apply Grid.numberBad_imp_impossible {x := (Fin.mk 1 (by grind)), y := (Fin.mk 2 (by grind))}
    decide

  put .blue at (2, 0) by
    apply Grid.columnBad_imp_impossible 2 .red
    decide

  put .red at (3, 0) by
    apply Grid.lineBad_imp_impossible 0 .blue
    decide

  put .blue at (3, 1) by
    apply Grid.columnBad_imp_impossible 3 .red
    decide

  solved
