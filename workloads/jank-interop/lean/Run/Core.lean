import Jank.CoreSearch

def main (args : List String) : IO UInt32 := do
  Jank.CoreSearch.searches args
  return 0
