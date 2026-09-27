import JinagaSpec.Syntax

/-!
# Authoring helpers

Short constructors so that a specification in a test or a vector reads close
to Jinaga's text form. `path [] "p1" [role "office" "Office"]` in the match for
`u1` is `u1 = p1->office: Office`.
-/
namespace JinagaSpec.Build

def role (name type : Name) : Role := { name := name, predecessorType := type }

def path (left : List Role) (labelRight : Name) (right : List Role := []) : Condition :=
  .path { rolesLeft := left, labelRight := labelRight, rolesRight := right }

def exists' (matchList : List Match) : Condition := .existential true matchList
def notExists (matchList : List Match) : Condition := .existential false matchList

def unknown (name type : Name) (conditions : List Condition) : Match :=
  .mk { name := name, type := type } conditions

def givens (given : List (Name × Name)) : List Label :=
  given.map fun (name, type) => { name := name, type := type }

def spec (given : List (Name × Name)) (matchList : List Match) (projection : Projection) : Specification :=
  { given := givens given, matchList := matchList, projection := projection }

def fact (label : Name) : Projection := .fact label

end JinagaSpec.Build
