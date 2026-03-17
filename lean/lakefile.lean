import Lake
open Lake DSL

package "HackSafety" where
  -- add package configuration options here

lean_lib «HackSafety» where
  -- add library configuration options here

@[default_target]
lean_exe "hacksafety" where
  root := `Main
