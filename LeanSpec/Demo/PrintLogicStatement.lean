import LeanSpec.Logic.Demo.Theme
import LeanSpec.Logic.Demo.TempConverter
import LeanSpec.Logic.Demo.Lru

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
  return 0
