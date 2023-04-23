import Lake
open Lake DSL

package «abaplot» {
  -- add package configuration options here
}

lean_lib «Abaplot» {
  -- add library configuration options here
}

@[default_target]
lean_exe «abaplot» {
  root := `Main
}


require std from git "https://github.com/leanprover/std4" @ "da029e9bd189bd4df3c4d4fcfd8510f774f58fe0"