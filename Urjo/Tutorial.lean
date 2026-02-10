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

  put .blue at (0, 3) by bad_column at 0 with .red
  put .red at (1, 2) by bad_row at 2 with .blue
  put .red at (2, 2) by bad_row at 2 with .blue
  put .blue at (1, 0) by bad_num at (0, 1)
  put .blue at (1, 1) by bad_num at (0, 1)
  put .red at (1, 3) by bad_column at 1 with .blue

  put .blue at (2, 3) by
    split_color .red at (3, 3)
    · bad_row at 3 with .red
    · consecutive_row at 2

  put .red at (3, 3) by bad_row at 3 with .blue
  put .red at (2, 1) by bad_num at (1, 2)
  put .blue at (2, 0) by bad_column at 2 with .red
  put .red at (3, 0) by bad_row at 0 with .blue
  put .blue at (3, 1) by bad_column at 3 with .red
  solved
