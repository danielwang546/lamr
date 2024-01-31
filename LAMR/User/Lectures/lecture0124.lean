/-
Notes:

We set up Piazza.

Always open the main LAMR project folder in VS Code. Opening any other folder will confuse Lean.

To read the lectures, drop them in the `User` folder (or any subfolder thereof.)

The extension that shows errors inline is "Error Lens."

I'll turn off Copilot.
-/

def hanoi (numDisks start finish aux: Nat) : IO Unit :=
  match numDisks with
  | 0 => pure ()
  | (n + 1) => do
    hanoi n start aux finish
    IO.println s!"move disk {n+1} from {start} to {finish}"
    hanoi n aux finish start

#eval hanoi 10 1 3 2

def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then
    false
  else
    for i in [2:n] do
      if n % i = 0 then
        return false
      if i * i > n then
        return true
    true

-- add length
#eval (List.range 10000).filter isPrime

def primes (n : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [2:n] do
    if isPrime i then
      result := result.push i
  result

#eval (primes 10000).size
#eval primes 10000

def bar (n? : Option Nat) : IO Unit := do
  let some n := n? |
    IO.println "oops"
  IO.println n

#eval bar (some 2)
#eval bar none

def mulTable : Array (Array Nat) := Id.run do
  let mut table := #[]
  for i in [:10] do
    let mut row := #[]
    for j in [:10] do
      row := row.push ((i + 1) * (j + 1))
    table := table.push row
  table

#eval mulTable

def mulTable' : Array (Array Nat) := Id.run do
  let mut s : Array (Array Nat) := mkArray 10 (mkArray 10 0)
  for i in [:10] do
    for j in [:10] do
      s := s.set! i $ s[i]!.set! j ((i + 1) * (j + 1))
  s

#eval show IO Unit from do
  for i in [:10] do
    for j in [:10] do
      let numstr := toString (mulTable[i]!)[j]!
      -- print 1-3 spaces
      IO.print <| " ".pushn ' ' (3 - numstr.length)
      IO.print numstr
    IO.println ""
