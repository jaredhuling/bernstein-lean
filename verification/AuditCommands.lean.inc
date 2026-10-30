open Lean Meta Elab Command

meta def bernsteinAudit (requested : Name) (captureProof : Bool) : CommandElabM Unit := do
  liftTermElabM do
    let env ← getEnv
    let actual ← if env.contains requested then pure requested else do
      let candidates := env.constants.toList.filter fun (n, _) =>
        n.toString.startsWith "_private." && n.toString.endsWith ("." ++ requested.toString)
      match candidates with
      | [(n, _)] => pure n
      | _ => throwError "Expected exactly one private declaration for {requested}, found {candidates.length}"
    let info ← getConstInfo actual
    let axioms ← Lean.collectAxioms actual
    unless axioms.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
      throwError "Unexpected axioms for {requested}: {axioms}"
    let edges ← if captureProof then do
      let some value := info.value? true | throwError "Missing proof for {requested}"
      pure (toJson (value.getUsedConstants.toList.map Name.toString))
    else pure Json.null
    let fullType := (← ppExpr info.type).pretty
    let canonical ← withOptions (fun o =>
        (o.setBool `pp.fullNames true).setBool `pp.notation false) do
      pure (← ppExpr info.type).pretty
    forallTelescope info.type fun xs conclusion => do
      let mut binders : Array Json := #[]
      for i in [:xs.size] do
        let decl ← xs[i]!.fvarId!.getDecl
        let kind := match decl.binderInfo with
          | .default => "explicit"
          | .implicit => "implicit"
          | .strictImplicit => "strict-implicit"
          | .instImplicit => "instance"
        binders := binders.push (Json.mkObj [
          ("index", toJson i), ("name", toJson decl.userName.toString),
          ("kind", toJson kind), ("is_proposition", toJson (← isProp decl.type)),
          ("type", toJson (← ppExpr decl.type).pretty)])
      logInfo m!"AUDIT_DECLARATION {(Json.mkObj [
        ("declaration", toJson requested.toString), ("kernel_name", toJson actual.toString),
        ("elaborated_type", toJson fullType), ("canonical_type", toJson canonical),
        ("binders", toJson binders), ("conclusion", toJson (← ppExpr conclusion).pretty),
        ("axioms", toJson (axioms.toList.map Name.toString)),
        ("direct_proof_dependencies", edges)]).compress}"

elab "audit_decl " name:ident : command => bernsteinAudit name.getId false
elab "audit_source_decl " name:ident : command => bernsteinAudit name.getId true
