/- The Lean kernel's own answer to each `xhci` call, for the xHCI simulator (test/xhci-sim/sim.c).

The simulator runs the USB driver's xHCI code on the host. Each `xhci(cap, op, x, y, z)` it
makes comes here, one per line as `x CAP OP X Y Z` (the words as arch/kmain.c passes them to
the kernel), and `sysXhci` from LeanOS/Kernel.lean decides it, with the USB driver's
capabilities as the manifest gives them (`initCaps 17`): the answer is a line `STATUS XHCIOP
USBA USBB USBC USBD`, the result it leaves the driver and what it asks the machine layer to do.
So nothing about the kernel's checks is copied into C: a request the kernel would refuse is
refused here. `boot` lists the nonzero words of `xhciBoot` (`I W`), then `end`, and `base`
gives `xhciBase`. -/
import LeanOS.Kernel
open LeanOS

def words (line : String) : List Nat :=
  ((line.splitOn " ").filter (fun w => !w.isEmpty)).map (fun w => (String.ofList (w.toList.filter Char.isDigit)).toNat!)

def main : IO Unit := do
  let s0 := init 0x3c100000
  let s := { s0 with cur := usbTask }
  let some t := nth? s.tasks usbTask | IO.println "no USB task"
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.startsWith "boot" then
      for i in [0:64 * 512] do
        let w := xhciBoot i
        if w != 0 then stdout.putStrLn s!"{i} {w}"
      stdout.putStrLn "end"
    else if line.startsWith "base" then
      stdout.putStrLn s!"{xhciBase}"
    else if line.startsWith "x" then
      match words (line.drop 1).toString with
      | [cap, op, x, y, z] =>
        let r := sysXhci s t cap op x y z
        let status := match nth? r.state.tasks usbTask with
          | some t' => (match t'.result with | v :: _ => v | [] => 99)
          | none => 98
        stdout.putStrLn s!"{status} {r.xhciOp} {r.usbA} {r.usbB} {r.usbC} {r.usbD}"
      | _ => stdout.putStrLn "?"
    else stdout.putStrLn "?"
    stdout.flush
