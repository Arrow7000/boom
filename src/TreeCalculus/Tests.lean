/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus

/-! # Regression checks for the widget's executable stepping -/

#guard (Term.ofJson? combΩ.treeJson).toOption == some combΩ
#guard ((combI ⬝ (△ ⬝ △)).runOutermost 100 1000).1 == △ ⬝ △
#guard (combΩ.runOutermost 50 100000).1.firstRedex?.isSome
