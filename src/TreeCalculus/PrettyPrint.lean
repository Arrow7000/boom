/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus.Term

/-!
# Pretty printing `Term`

Display only: nothing here affects the calculus.

* The infoview and hovers show `Term.term [a, b]` as `△ ⬝ a ⬝ b`.
* `#eval` shows terms the same way, using `Repr`.
-/

section PrettyPrinting

/-- Pretty-print constructor form as `△ ⬝ …`. `Term.apply` is reducible, so
reduced terms are `Term.term […]` and the `⬝` unexpander never fires on them. -/
@[app_unexpander Term.term]
def Term.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ []) => `(△)
  | `($_ [$args,*]) => do
    let r ← args.getElems.foldlM (init := (← `(△) : Lean.Term)) fun acc arg =>
      `($acc ⬝ $arg)
    return r
  | _ => throw ()

/-- Parenthesize nested applications; leaves stay `△`. -/
def Term.toFormat : Term → Std.Format
  | .term [] => "△"
  | .term cs =>
    cs.foldl (init := Std.Format.text "△") fun acc c =>
      acc ++ " ⬝ " ++
        match c with
        | .term [] => "△"
        | _ => .paren c.toFormat

instance : Repr Term where
  reprPrec t _ := t.toFormat

end PrettyPrinting
