import JinagaSpec.Syntax

/-!
# Text form

Prints a specification in the text form of `describeSpecification`
(`src/specification/description.ts`), so a vector can be read, and so a port
can check its own printer against this one. Composite components print sorted
by name, as the TypeScript does.
-/
namespace JinagaSpec

def indentOf (depth : Nat) : String :=
  String.join (List.replicate depth "    ")

def describeRoles (roles : List Role) : String :=
  String.join (roles.map fun r => s!"->{r.name}: {r.predecessorType}")

mutual
  def describeMatches (depth : Nat) : List Match → String
    | [] => ""
    | m :: ms => describeMatch depth m ++ describeMatches depth ms

  def describeMatch (depth : Nat) : Match → String
    | .mk unknown conditions =>
      s!"{indentOf depth}{unknown.name}: {unknown.type} [\n" ++
        describeConditions unknown.name (depth + 1) conditions ++
        s!"{indentOf depth}]\n"

  def describeConditions (unknown : Name) (depth : Nat) : List Condition → String
    | [] => ""
    | c :: cs => describeCondition unknown depth c ++ describeConditions unknown depth cs

  def describeCondition (unknown : Name) (depth : Nat) : Condition → String
    | .path c =>
      s!"{indentOf depth}{unknown}{describeRoles c.rolesLeft} = {c.labelRight}{describeRoles c.rolesRight}\n"
    | .existential e ms =>
      s!"{indentOf depth}{if e then "" else "!"}E \{\n" ++
        describeMatches (depth + 1) ms ++
        s!"{indentOf depth}}\n"
end

def describeProjection (depth : Nat) : Projection → String
  | .fact label => label
  | .composite components =>
    let sorted := components.mergeSort fun a b => a.name ≤ b.name
    "{\n" ++ String.join (sorted.map fun c => s!"    {indentOf depth}{c.name} = {c.label}\n") ++
      s!"{indentOf depth}}"

def describeSpecification (s : Specification) (depth : Nat := 0) : String :=
  let given := ", ".intercalate (s.given.map fun l => s!"{l.name}: {l.type}")
  let projection :=
    match s.projection with
    | .composite [] => ""
    | p => " => " ++ describeProjection depth p
  s!"{indentOf depth}({given}) \{\n" ++ describeMatches (depth + 1) s.matchList ++
    s!"{indentOf depth}}{projection}\n"

end JinagaSpec
