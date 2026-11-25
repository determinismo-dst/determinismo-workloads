import Jank.StringsSearch

def main (args : List String) : IO UInt32 := do
  Jank.StringsSearch.searches args
  return 0
