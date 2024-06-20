import Lake
open Lake DSL

package «Cpa» where
  -- add package configuration options here

@[default_target]
lean_lib Cpa

@[default_target]
lean_exe defaultExe {
  root := `Main
}
