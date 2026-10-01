import LeanSpec.Demo.Verification

/-- Print the demo verification statements. Each block is one canonical artefact. -/
def main : IO UInt32 := do
  IO.println "# LeanSpec.Demo.Verification.themeVerified"
  IO.print LeanSpec.Demo.Verification.themeVerifiedSource
  IO.println ""
  IO.println "# LeanSpec.Demo.Verification.archivedVerified"
  IO.print LeanSpec.Demo.Verification.archivedVerifiedSource
  return 0
