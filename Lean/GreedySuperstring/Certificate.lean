import Std

/-!
# Compact exact-certificate format

The JSON/gzip converter is outside the trusted proof boundary.  This module
parses its small integer-only stream.  Subsequent Lean code must rebuild the
LP row system and validate every value before a certificate is accepted.
-/

namespace GreedySuperstring.Certificate

structure Header where
  kind : String
  n : Nat
  count : Nat
  sourceSha256 : String
deriving Repr, BEq

structure SparseEntry where
  index : Nat
  value : Int
deriving Repr, BEq

structure Record where
  scale : Int
  z : Int
  bound : Int
  y : Array SparseEntry
  lower : Array SparseEntry
  upper : Array SparseEntry
deriving Repr, BEq

private def words (line : String) : List String :=
  (line.splitToList (· = ' ')).filter (· ≠ "")

def parseHeader (line : String) : Except String Header := do
  match words line with
  | [magic, kind, nRaw, countRaw, hash] =>
      if magic ≠ "GSCERT1" then
        throw s!"unexpected certificate magic {magic}"
      let some n := nRaw.toNat?
        | throw s!"invalid header dimension {nRaw}"
      let some count := countRaw.toNat?
        | throw s!"invalid header count {countRaw}"
      if hash.length ≠ 64 then
        throw "source SHA-256 does not have 64 hexadecimal characters"
      pure { kind, n, count, sourceSha256 := hash }
  | _ => throw "malformed certificate header"

private abbrev Parser := StateT (List Int) (Except String)

private def takeInt : Parser Int := do
  match ← get with
  | [] => throw "truncated certificate record"
  | value :: rest =>
      set rest
      pure value

private def takeNat (name : String) : Parser Nat := do
  let value ← takeInt
  if value < 0 then
    throw s!"negative {name}"
  pure value.toNat

private def parseSparse (name : String) : Parser (Array SparseEntry) := do
  let count ← takeNat s!"{name} count"
  let rec loop (remaining : Nat) (previous : Option Nat)
      (entries : Array SparseEntry) : Parser (Array SparseEntry) := do
    if remaining = 0 then
      pure entries
    else
      let index ← takeNat s!"{name} index"
      let value ← takeInt
      if value = 0 then
        throw s!"zero stored in sparse section {name}"
      match previous with
      | some old =>
          if index ≤ old then
            throw s!"non-increasing sparse indices in section {name}"
      | none => pure ()
      loop (remaining - 1) (some index) (entries.push { index, value })
  loop count none #[]

def parseRecord (line : String) : Except String Record := do
  let tokens ← (words line).mapM fun token =>
    match token.toInt? with
    | some value => pure value
    | none => throw s!"noninteger certificate token {token}"
  let parser : Parser Record := do
    let scale ← takeInt
    let z ← takeInt
    let bound ← takeInt
    let y ← parseSparse "y"
    let lower ← parseSparse "lower"
    let upper ← parseSparse "upper"
    pure { scale, z, bound, y, lower, upper }
  let (record, trailing) ← parser.run tokens
  if !trailing.isEmpty then
    throw "trailing certificate tokens"
  if record.scale ≤ 0 then
    throw "nonpositive certificate scale"
  pure record

def load (path : System.FilePath) : IO (Except String (Header × Array Record)) := do
  let content ← IO.FS.readFile path
  match content.splitOn "\n" with
  | [] => pure (.error "empty certificate file")
  | headerLine :: recordLines =>
      let records := recordLines.filter (· ≠ "")
      pure do
        let header ← parseHeader headerLine
        if records.length ≠ header.count then
          throw s!"header promises {header.count} records, found {records.length}"
        let decoded ← records.mapM parseRecord
        pure (header, decoded.toArray)

end GreedySuperstring.Certificate
