import Lake
open Lake DSL

package notes {
  -- add package configuration options here
}

lean_lib Notes {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe notes {
  root := `Main
}
