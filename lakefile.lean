import Lake
open Lake DSL

package «p-vs-np» where
  name := "p-vs-np"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

lean_lib Towers where
  roots := #[`Towers.PvsNP.Complexity,
             `Towers.PvsNP.Hierarchy,
             `Towers.PvsNP.CircuitComplexity,
             `Towers.PvsNP.Barriers,
             `Towers.PvsNP.ClayStatement,
             `Towers.PvsNP.PvsNPCollection,
             `Towers.PvsNP.PvsNPCertificate]
