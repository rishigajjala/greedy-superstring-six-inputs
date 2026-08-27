import GreedySuperstring.Checker

open GreedySuperstring

private def pathsFromArgs (args : List String) : IO (System.FilePath × System.FilePath) :=
  match args with
  | [] => pure ("Lean/Data/five.cert", "Lean/Data/six.cert")
  | [five, six] => pure (five, six)
  | _ => throw <| IO.userError "usage: checkCertificates [FIVE_CERT SIX_CERT]"

def main (args : List String) : IO Unit := do
  let (fivePath, sixPath) ← pathsFromArgs args
  match ← Checker.checkAllFiles fivePath sixPath with
  | .error message => throw <| IO.userError message
  | .ok (fiveCount, sixCount) =>
      IO.println "Lean exact certificate replay passed"
      IO.println s!"  five-input cases: {fiveCount}"
      IO.println s!"  six-input representatives: {sixCount}"
      IO.println "  six-input cases covered by involution: 86400"
