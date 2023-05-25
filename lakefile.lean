import Lake
open Lake DSL

package lemmas {
  -- add package configuration options here
}

lean_lib Lemmas {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lemmas {
  root := `Main
}
