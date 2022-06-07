import Lake
open Lake DSL

package WildGeo {
  -- add configuration options here
    dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"
  }]
}
