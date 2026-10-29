module

public import LeanKb.Kb
public import LeanKb.Determination
public import LeanKb.WikiAccess
public import LeanSpec.Wiki
public import LeanSpec.WikiStore
public import LeanSpec.Codec.Reflection
public import LeanSpec.KbAdapter.Wiki

/-!
Root of the `LeanSpecKb` library: the assurance-indexed knowledge core, defeasible
determination, the agent Wiki, its store and its access rules. Lake names a
library's native initializer after this module, so a downstream package that
precompiles its modules can load the library as a plugin.
-/
