import RiemannStieltjes
open Lean Meta Elab Command

-- Report every axiom used by a declaration of the `RiemannStieltjes` modules, beyond
-- `propext`, `Classical.choice` and `Quot.sound`.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`RiemannStieltjes).isPrefixOf mod do continue
    n := n + 1
    let axs ← liftCoreM <| collectAxioms c
    let extra := axs.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do bad := bad.push (c, extra)
  logInfo m!"{n} declarations checked; {bad.size} with other axioms: {bad.toList.take 20}"
