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
             `Towers.PvsNP.PolynomialHierarchy,
             `Towers.PvsNP.DescriptiveComplexity,
             `Towers.PvsNP.KarpLipton,
             `Towers.PvsNP.CountingComplexity,
             `Towers.PvsNP.FaginFragment,
             `Towers.PvsNP.ImmermanVardi,
             `Towers.PvsNP.PvsNPCollection,
             `Towers.PvsNP.PvsNPCertificate,
             `Towers.Continuum.CardinalBounds,
             `Towers.Continuum.ContinuumHypothesis,
             `Towers.Continuum.KonigTheorem,
             `Towers.Continuum.KonigInequality,
             `Towers.Continuum.ContinuumCollection,
             `Towers.Computability.Computability,
             `Towers.Computability.ArithmeticalHierarchy,
             `Towers.Computability.ComputabilityCollection,
             `Towers.ZFC.IndependenceFramework,
             `Towers.ZFC.ZFCCollection,
             `Towers.ZProtocol.ZProtocolFramework,
             `Towers.ZProtocol.ZProtocolCollection]
