import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

elab "assert_standard_axioms " declaration:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declaration
  let axioms ← Lean.collectAxioms name
  let forbidden := axioms.filter fun axiomName =>
    !(#[``propext, ``Classical.choice, ``Quot.sound].contains axiomName)
  unless forbidden.isEmpty do
    throwError "{name} depends on forbidden axioms: {forbidden}"
