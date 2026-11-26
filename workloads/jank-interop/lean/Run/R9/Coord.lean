import Jank.R9.Coord.Shell

/-! Round 9, coordinator (`jank9-coord`): jank.shell's arguments through boost's split
(`Jank.R9.Coord.Shell`, U88). Prints the child's argv for a few argument lists, stock and with U88,
and counts, over every list of up to three arguments of up to three characters from {a, space, ",
\}, how many reach the child changed. -/

open Jank.R9.Coord.Shell

def show1 (args : List (List Char)) : String :=
  toString ((stockArgv args).map String.ofList)

def alphabet : List Char := ['a', ' ', '"', '\\']

def strs : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => strs n ++ ((strs n).filter (·.length == n)).flatMap (fun s => alphabet.map (s ++ [·]))

def lists (k : Nat) (pool : List (List Char)) : List (List (List Char)) :=
  match k with
  | 0 => [[]]
  | k + 1 => lists k pool ++ ((lists k pool).filter (·.length == k)).flatMap (fun l => pool.map (l ++ [·]))

def main : IO Unit := do
  for a in [[ "echo", "a\" b"], ["echo", "5\" wide"], ["a\"b\"c"], ["a\"", "b"], ["x y", "z"], ["", "q"]] do
    let args := a.map String.toList
    IO.println s!"{a} -> {show1 args}"
  let pool := (strs 3).filter (·.length ≥ 1)
  let ls := (lists 3 pool).filter (·.length ≥ 1)
  let mut total := 0
  let mut changed := 0
  let mut changedNoQuote := 0
  for l in ls do
    total := total + 1
    if stockArgv l != l then
      changed := changed + 1
      if l.all (fun s => !s.contains '"') then changedNoQuote := changedNoQuote + 1
  IO.println s!"lists {total} (1-3 arguments of 1-3 chars over a, space, quote, backslash): {changed} reach the child changed, {changedNoQuote} of them without a quote"
