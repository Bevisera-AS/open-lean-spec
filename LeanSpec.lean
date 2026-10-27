import LeanSpec.Core
import LeanSpec.Logic.Core

/-!
The spec library an agent imports. Requirements are `Prop`s (`LeanSpec.Logic`);
examples, the JSON runner, structural checks and the `spec` CLI are
`LeanSpec.Core`. Nothing else: the process layer is `LeanSpecProcess` and the
knowledge layer is `LeanSpecKb`, each with its own root module.
-/
