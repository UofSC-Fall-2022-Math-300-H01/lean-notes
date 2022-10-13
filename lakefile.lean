import Lake
open Lake DSL

require aesop from git "https://github.com/JLimperg/aesop"
require std from git "https://github.com/leanprover/std4" @ "main"

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
