import C0deine
import C0deine.Top
import Cli

def main (args : List String) : IO UInt32 :=
  C0deine.Top.topCmd.validate args 
