import LeanSpec.Logic.Demo.Theme
import LeanSpec.Logic.Demo.TempConverter
import LeanSpec.Logic.Demo.Lru
import LeanSpec.Spec.Target

/-- Print the demo requirement statements. -/
def main : IO UInt32 := do
  IO.println "# LeanSpec.Logic.Demo.Theme.statement"
  IO.print LeanSpec.Logic.Demo.Theme.statement.render
  IO.println ""
  IO.println "# LeanSpec.Logic.Demo.TempConverter.statement"
  IO.print LeanSpec.Logic.Demo.TempConverter.statement.render
  IO.println ""
  IO.println "# LeanSpec.Logic.Demo.Lru.statement"
  IO.print LeanSpec.Logic.Demo.Lru.statement.render
  IO.println ""
  IO.println "# LeanSpec.Spec.Target.statement"
  IO.print LeanSpec.Spec.Target.statement.render
  return 0
