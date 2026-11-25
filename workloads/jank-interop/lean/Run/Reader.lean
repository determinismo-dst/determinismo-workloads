import Jank.ReaderSearch

def main (args : List String) : IO UInt32 := do
  Jank.ReaderSearch.searches args
  return 0
