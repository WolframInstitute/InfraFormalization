/-
Inventory of every declaration of the `InfraFormalization` library.

Run by `scripts/inventory.sh` after `lake build`. Writes two files:

* `INVENTORY_OUT`: one tab-separated line per declaration:
  kind, name, module, flags, library constants in the type,
  library constants in the value (defs) or constructor types (inductives).
* `INVENTORY_AXIOMS`: a Lean file with one `#print axioms` command per
  theorem, which `scripts/inventory.sh` runs to classify the axioms.

kind: `theorem`, `def`, `propdef` (a def whose type ends in `Prop`),
`structure`, `inductive`, `structure-prop`, `inductive-prop`, `axiom`, `opaque`.

flags:
- `concl-true`: the conclusion of a theorem, after its binders, is `True`.
- `proof-trivial`: the proof term of a theorem is `trivial`, `True.intro`,
  `Iff.rfl`, `Iff.refl _`, `rfl` or `Eq.refl _` after its lambdas.
- `body-true`: a Prop-valued def is `True` after its lambdas.
- `unused-arg:<i>`: explicit argument i (from 0) of a Prop-valued def does
  not occur in its body.
- `holds-for-all`: `∀ args, D args` for a Prop-valued def or Prop-valued
  structure D closes, after unfolding D, by one of `trivial`, `simp`,
  `⟨0, by simp⟩`, `⟨fun _ => 0, by simp⟩`, `⟨[], by simp⟩`,
  `constructor <;> simp`, each within 50000 heartbeats.
-/
import InfraFormalization

open Lean Meta Elab Term Tactic Command

namespace Inventory

def ours (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    if m.getRoot == `InfraFormalization then some m else none
  | none => none

partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ e => stripLams e
  | e => e

def proofTrivial (v : Expr) : Bool :=
  let f := (stripLams v).getAppFn
  f.isConstOf ``trivial || f.isConstOf ``True.intro || f.isConstOf ``Iff.rfl ||
    f.isConstOf ``Iff.refl || f.isConstOf ``rfl || f.isConstOf ``Eq.refl

def conclTrue (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ c => do
    return (← whnfR c).isConstOf ``True

partial def unusedArgs (v : Expr) : List Nat :=
  let rec go (e : Expr) (i : Nat) : List Nat :=
    match e with
    | .lam _ _ b bi =>
      let rest := go b (i + 1)
      if bi.isExplicit && !b.hasLooseBVar 0 then i :: rest else rest
    | .mdata _ e => go e i
    | _ => []
  go v 0

def tryClose (goal : Expr) (tac : Syntax) : TermElabM Bool := do
  let saved ← saveState
  let r ← tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context ({· with maxHeartbeats := 50000000}) do
      let mv ← mkFreshExprMVar goal
      let rest ← Tactic.run mv.mvarId! (evalTactic tac)
      return rest.isEmpty && !(← instantiateMVars mv).hasSorry)
    (fun _ => pure false)
  saved.restore
  return r

def holdsForAll (n : Name) (ty : Expr) : TermElabM Bool := do
  let some ci := (← getEnv).find? n | return false
  let goal ← forallTelescopeReducing ty fun xs _ => do
    mkForallFVars xs (mkAppN (.const n (ci.levelParams.map Level.param)) xs)
  let goal ← deltaExpand goal (· == n)
  let tacs : List Syntax := [
    ← `(tactic| (intros; trivial)),
    ← `(tactic| (intros; simp; done)),
    ← `(tactic| (intros; exact ⟨0, by simp⟩)),
    ← `(tactic| (intros; exact ⟨fun _ => 0, by simp⟩)),
    ← `(tactic| (intros; exact ⟨[], by simp⟩)),
    ← `(tactic| (intros; constructor <;> (intros; simp; done)))]
  for t in tacs do
    if ← tryClose goal t then return true
  return false

def isPropValued (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ c => return c.isProp

def skipName (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
    (match n with
     | .str _ s => s.startsWith "match_" || s.startsWith "proof_" ||
        s.startsWith "eq_" || s == "eq_def" ||
        s == "rec" || s == "recOn" || s == "casesOn" || s == "noConfusion" ||
        s == "noConfusionType" || s == "below" || s == "brecOn" || s == "binductionOn" ||
        s == "ibelow" || s == "mk" || s == "sizeOf_spec" || s == "inj" || s == "injEq" ||
        s.startsWith "_" || s == "ext" || s == "ext_iff" || s == "ctorIdx"
     | _ => false)

def oursIn (env : Environment) (e : Expr) : String :=
  ",".intercalate ((e.getUsedConstants.filter (fun c => (ours env c).isSome &&
    !skipName c)).toList.map toString)

end Inventory

open Inventory in
set_option maxHeartbeats 0 in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let out := (← IO.getEnv "INVENTORY_OUT").getD "inventory.tsv"
  let axOut := (← IO.getEnv "INVENTORY_AXIOMS").getD "inventory_axioms.lean"
  let h ← IO.FS.Handle.mk out .write
  let ha ← IO.FS.Handle.mk axOut .write
  ha.putStrLn "import InfraFormalization"
  let mut items : Array (Name × Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some m := ours env n then
      if !skipName n && !(ci matches .ctorInfo _) && !(ci matches .recInfo _) then
        items := items.push (n, m, ci)
  for (n, m, ci) in items do
    let tyC := oursIn env ci.type
    let line ← liftTermElabM do
      match ci with
      | .thmInfo t =>
        let mut flags : Array String := #[]
        if ← conclTrue t.type then flags := flags.push "concl-true"
        if proofTrivial t.value then flags := flags.push "proof-trivial"
        return s!"theorem\t{n}\t{m}\t{",".intercalate flags.toList}\t{tyC}\t"
      | .defnInfo d =>
        if ← isPropValued d.type then
          let mut flags : Array String := #[]
          if (stripLams d.value).isConstOf ``True then flags := flags.push "body-true"
          for i in unusedArgs d.value do flags := flags.push s!"unused-arg:{i}"
          if ← holdsForAll n d.type then flags := flags.push "holds-for-all"
          return s!"propdef\t{n}\t{m}\t{",".intercalate flags.toList}\t{tyC}\t{oursIn env d.value}"
        else
          return s!"def\t{n}\t{m}\t\t{tyC}\t{oursIn env d.value}"
      | .inductInfo t =>
        let k := if isStructure env n then "structure" else "inductive"
        let ctorTys := t.ctors.foldl (fun acc c => match env.find? c with
          | some cc => acc ++ "," ++ oursIn env cc.type | none => acc) ""
        if ← isPropValued t.type then
          let flags := if ← holdsForAll n t.type then "holds-for-all" else ""
          return s!"{k}-prop\t{n}\t{m}\t{flags}\t{tyC}\t{ctorTys}"
        return s!"{k}\t{n}\t{m}\t\t{tyC}\t{ctorTys}"
      | .axiomInfo _ => return s!"axiom\t{n}\t{m}\t\t{tyC}\t"
      | .opaqueInfo _ => return s!"opaque\t{n}\t{m}\t\t{tyC}\t"
      | _ => return ""
    if line != "" then
      h.putStrLn line
      h.flush
    if ci matches .thmInfo _ then
      ha.putStrLn s!"#print axioms {n}"
  ha.flush
