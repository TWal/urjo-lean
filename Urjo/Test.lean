import Urjo.Specification

/--
info: [{ x := 0, y := 0 }, { x := 0, y := 1 }, { x := 1, y := 0 }, { x := 1, y := 1 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (3, 3) (1, 1) (0, 0)

/--
info: [{ x := 1, y := 0 }, { x := 1, y := 1 }, { x := 2, y := 0 }, { x := 2, y := 1 }, { x := 3, y := 0 }, { x := 3, y := 1 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (3, 3) (1, 1) (2, 0)

/--
info: [{ x := 0, y := 1 }, { x := 0, y := 2 }, { x := 0, y := 3 }, { x := 1, y := 1 }, { x := 1, y := 2 }, { x := 1, y := 3 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (3, 3) (1, 1) (0, 2)

/--
info: [{ x := 4, y := 4 }, { x := 4, y := 5 }, { x := 5, y := 4 }, { x := 5, y := 5 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (3, 3) (1, 1) (5, 5)

/--
info: [{ x := 1, y := 1 },
 { x := 1, y := 2 },
 { x := 1, y := 3 },
 { x := 2, y := 1 },
 { x := 2, y := 2 },
 { x := 2, y := 3 },
 { x := 3, y := 1 },
 { x := 3, y := 2 },
 { x := 3, y := 3 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (3, 3) (1, 1) (2, 2)

/--
info: [{ x := 0, y := 0 }, { x := 0, y := 1 }, { x := 0, y := 2 }, { x := 0, y := 3 }, { x := 0, y := 4 }, { x := 0, y := 5 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (1, 6) (0, 0) (0, 0)

/--
info: [{ x := 0, y := 0 }, { x := 1, y := 0 }, { x := 2, y := 0 }, { x := 3, y := 0 }, { x := 4, y := 0 }, { x := 5, y := 0 }]
-/
#guard_msgs in
#eval @makeGridIndices 6 6 (6, 1) (0, 0) (0, 0)

