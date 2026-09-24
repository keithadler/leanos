#!/bin/bash
# Breaks the kernel on purpose, one way at a time, and checks the proofs reject each
# break. A mutant that still builds means a guarantee is weaker than it claims.
set -u
cd "$(dirname "$0")/.."
# The mutants: a name, text in LeanOS/Kernel.lean, and what it becomes. test/mutants.py
# runs them, several at once (JOBS, default half the cores), each in its own copy of the
# project, so the working tree is never touched.
mutant() { printf '%s\0%s\0%s\0%s\0' LeanOS/Kernel.lean "$1" "$2" "$3"; }
# the journal's model (its proof is LeanOS/Journal.lean)
mutant_journal() { printf '%s\0%s\0%s\0%s\0' LeanOS/JournalModel.lean "$1" "$2" "$3"; }

{
mutant "derive grants whatever is asked" \
  "⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩" "⟨o, Rights.ofBits bits, c.badge⟩"
mutant "derive lets a task pick its badge" \
  "⟨o, c.rights.meet (Rights.ofBits bits), c.badge⟩" "⟨o, c.rights.meet (Rights.ofBits bits), bits⟩"
mutant "level-2 table points past the 16 level-3 tables" \
  "def l2Word (l3 k : Nat) : Nat := if k < l3Tables then" "def l2Word (l3 k : Nat) : Nat := if k < l3Tables + 1 then"
mutant "map ignores the capability's frames" \
  "app (runMaps vpn base c.rights count)" "app (runMaps vpn (base + 1) c.rights count)"
mutant "derive cuts a piece past the end of the run" \
  "else if offset + count ≤ n then some (.frames (base + offset) count) else none" "else some (.frames (base + offset) count)"
mutant "map outside the user window" \
  "if vpn + count ≤ userPages && c.rights.r &&" "if c.rights.r &&"
mutant "write skips the page check" \
  "allReadable t.maps ((va - userBase) / pageSize)" "true || allReadable t.maps ((va - userBase) / pageSize)"
mutant "send without the send right" \
  "if c.rights.w then
        match grantOf" "if true then
        match grantOf"
mutant "receive without the receive right" \
  "if c.rights.r then
        match findSender" "if true then
        match findSender"
mutant "grant without the grant right" \
  "else if ep.rights.x then" "else if true then"
mutant "grant an endpoint capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | .frames _ _ => some (some g)
      | .endpoint _ => some (some g)
      | _ => none"
mutant "sender picks its own badge" \
  "let m : Msg := ⟨c.badge, w0, w1, w2, g, call⟩" "let m : Msg := ⟨w0, w0, w1, w2, g, call⟩"
mutant "reply wakes a task that is not waiting for it" \
  "    if awaitsFrom s.tasks j s.cur then" "    if true then"
mutant "reply hands over the replier's capabilities" \
  "ret (setTask s j { u with status := .ready, result := 0 :: w0 :: w1 :: w2 :: .nil }) t'" "ret (setTask s j { u with status := .ready, caps := t.caps, result := 0 :: w0 :: w1 :: w2 :: .nil }) t'"
mutant "manifest gives mallory the grant right" \
  "epCap 0 false true false 2" "epCap 0 false true true 2"
mutant "manifest gives mallory the receive right" \
  "epCap 0 false true false 2" "epCap 0 true true false 2"
mutant "map framebuffer frames without checking the firmware's address" \
  "(fbSane s.fbBase && base + count ≤ devBase)" "(base + count ≤ devBase)"
mutant "accept a framebuffer that overlaps the frame pool" \
  "b % pageSize == 0 && frameBase + poolFrames * pageSize ≤ b" "b % pageSize == 0 && frameBase ≤ b"
mutant "manifest gives mallory the framebuffer" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (runCap poolFrames fbPages Rights.rw)"
mutant "framebuffer frames count as alice's" \
  "if f < poolFrames then f / framesPerTask else if f < devBase then displayTask else inputTask" "if f < poolFrames then f / framesPerTask else if f < devBase then 0 else inputTask"
mutant "an interrupt wakes whoever waits on any line" \
  "    | .waitingIrq k => if k == n then some j else findIrqWaiter n ts (j + 1)" "    | .waitingIrq _ => some j"
mutant "manifest gives mallory the UART" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (runCap devBase devPages Rights.rw)"
mutant "manifest gives mallory the UART's interrupt" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (irqCap uartIrq)"
mutant "grant an interrupt capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | _ => some (some g)"
mutant "accept a framebuffer that overlaps the peripherals" \
  "b + fbPages * pageSize ≤ 0xFE000000" "b + fbPages * pageSize ≤ 2 ^ 36"
mutant "verify ignores the manifest" \
  "if openSlot i || eqList h (expectedHash i) then" "if true then"
mutant "tasks start ready, unchecked" \
  "def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .unverified, .nil, .nil, .nil⟩" "def mkTask (i : Nat) : Task := ⟨initCaps i, initMaps i, .ready, .nil, .nil, .nil⟩"
mutant "a stopped task may make system calls" \
  "    | .ready => runCall s t num a0 a1 a2 a3 a4" "    | .ready => runCall s t num a0 a1 a2 a3 a4
    | .dead => runCall s t num a0 a1 a2 a3 a4"
mutant "user pages always executable" \
  "privNoExec + (if m.rights.x then 0 else userNoExec)" "privNoExec + 0"
mutant "read-only pages writable" \
  "(if m.rights.w then apUserRW else apUserRO)" "apUserRW"
mutant "kernel RAM executable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + shInner + accessFlag"
mutant "kernel RAM readable from user mode" \
  "0 + dValid + attrNormal + shInner + accessFlag + userNoExec" "0 + dValid + attrNormal + apUserRO + shInner + accessFlag + userNoExec"
mutant "scheduler may pick a waiting task" \
  "if runnable busy ts j then some j else findReady busy ts (j + 1) fuel" "some j"
mutant "start leaves other tasks' mappings of the slot" \
  "maps := dropMaps k t.maps" "maps := t.maps"
mutant "start leaves other tasks' capabilities to the slot" \
  "caps := dropCaps k t.caps" "caps := t.caps"
mutant "start leaves grants of the slot's frames in waiting messages" \
  "| some c => if capInSlot k c then none else some c" "| some c => some c"
mutant "start leaves reply slots for the old run" \
  "(if x == k then noTask else x) :: forgetCaller k xs" "x :: forgetCaller k xs"
mutant "a task may restart itself" \
  "if startable u.status && !(k == s.cur) && imageOk" "if startable u.status && imageOk"
mutant "manifest lets mallory start programs" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (launchCap 0)"
mutant "manifest lets the display restart the input driver" \
  "(launchCap 0)) (launchCap 5)" "(launchCap 4)) (launchCap 5)"
mutant "manifest lets Terminal receive on the display's endpoint" \
  "(snoc (frameCaps 5) (epCap 0 false true true 5))" "(snoc (frameCaps 5) (epCap 0 true true true 5))"
mutant "drop keeps the pages it can no longer back" \
  "⟨setTask s s.cur { t with caps := cs, maps := keepBacked cs t.maps, result := 0 :: .nil }," "⟨setTask s s.cur { t with caps := cs, maps := t.maps, result := 0 :: .nil },"
mutant "drop lets a task keep the capability and gain another" \
  "    let cs := removeNth t.caps ci" "    let cs := snoc t.caps ⟨.frames 0 1, Rights.rw, 0⟩"
mutant "manifest lets mallory grant to the file server" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (epCap 1 false true true 2)"
mutant "manifest lets the file server grant to the display" \
  "| 8 => snoc (snoc (frameCaps 8) (epCap 1 true false false 0)) (blocksCap 0 diskBlocks)" "| 8 => snoc (snoc (snoc (frameCaps 8) (epCap 1 true false false 0)) (blocksCap 0 diskBlocks)) (epCap 0 false true true 8)"
mutant "manifest lets Settings receive the file server's mail" \
  "| 6 => snoc (snoc (frameCaps 6) (epCap 0 false true true 6)) boardCap" "| 6 => snoc (snoc (snoc (frameCaps 6) (epCap 0 false true true 6)) boardCap) (epCap 1 true false false 6)"
mutant "block I/O skips the memory check" \
  "if Nat.ble (idx + 1) n && capRightFor write c.rights && ioPageOk t.maps va write then" "if Nat.ble (idx + 1) n && capRightFor write c.rights then"
mutant "block I/O without the capability's right" \
  "if Nat.ble (idx + 1) n && capRightFor write c.rights && ioPageOk t.maps va write then" "if Nat.ble (idx + 1) n && ioPageOk t.maps va write then"
mutant "block I/O past the end of the capability" \
  "if Nat.ble (idx + 1) n && capRightFor write c.rights && ioPageOk t.maps va write then" "if capRightFor write c.rights && ioPageOk t.maps va write then"
mutant "a disk read may land in a read-only page" \
  "  | false => writableAt" "  | false => readableAt"
mutant "manifest gives mallory the disk" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) (blocksCap 0 diskBlocks)"
mutant "grant a block capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | .frames _ _ => some (some g)
      | .blocks _ _ => some (some g)
      | _ => none"
mutant "exec skips the page check" \
  "    Nat.ble 1 len && Nat.ble len maxImage && Nat.ble userBase src &&
      allReadable ms" "    Nat.ble 1 len && Nat.ble len maxImage && Nat.ble userBase src &&
      true || allReadable ms"
mutant "exec takes images larger than the code run" \
  "Nat.ble 1 len && Nat.ble len maxImage &&" "Nat.ble 1 len &&"
mutant "exec loads a program into a manifest slot" \
  "  else len == 0" "  else true"
mutant "Notes' slot counts as open" \
  "def openSlot (i : Nat) : Bool := Nat.ble 10 i && Nat.ble i 15" "def openSlot (i : Nat) : Bool := (Nat.ble 10 i && Nat.ble i 15) || i == 0"
mutant "manifest lets Notes start programs from the SD card" \
  "  | 0 => snoc (snoc (frameCaps 0) (epCap 0 false true true 1)) (epCap 1 false true true 1)" "  | 0 => snoc (snoc (snoc (frameCaps 0) (epCap 0 false true true 1)) (epCap 1 false true true 1)) (launchCap 10)"
mutant "an open slot may receive the file server's mail" \
  "  | 10 => snoc (snoc (frameCaps 10) (epCap 0 false true true 10)) (epCap 1 false true true 10)" "  | 10 => snoc (snoc (frameCaps 10) (epCap 0 false true true 10)) (epCap 1 true true true 10)"
mutant "an open slot sends to the file server as Terminal" \
  "  | 12 => snoc (snoc (frameCaps 12) (epCap 0 false true true 12)) (epCap 1 false true true 12)" "  | 12 => snoc (snoc (frameCaps 12) (epCap 0 false true true 12)) (epCap 1 false true true 5)"
mutant "a tick wakes sleepers early" \
  "  | .sleeping u => if Nat.ble u now then" "  | .sleeping u => if true then"
mutant "manifest gives Terminal the power capability" \
  "           (launchCap 14)) (launchCap 15)" "           (launchCap 14)) powerCap"
mutant "grant the power capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | .frames _ _ => some (some g)
      | .power => some (some g)
      | _ => none"

mutant "the CPU may be overclocked" \
  "def cpuSpeeds : List Nat := 600 :: 1000 :: 1500 :: .nil" "def cpuSpeeds : List Nat := 600 :: 1000 :: 1800 :: .nil"
mutant "board takes any CPU clock it is given" \
  "(match nth? cpuSpeeds value with | some mhz => mhz | none => 0)" "value"
mutant "board skips the rights check" \
  "(if boardChanges req then c.rights.w else c.rights.r)" "true"
mutant "Security also holds the board" \
  "| 7 => snoc (frameCaps 7) (epCap 0 false true true 7)" "| 7 => snoc (snoc (frameCaps 7) (epCap 0 false true true 7)) boardCap"
mutant "a tick moves the clock by two" \
  "schedule { s with now := s.now + 1," "schedule { s with now := s.now + 2,"
mutant "time reports a tick ahead" \
  "ret s t (0 :: s.now :: ms ::" "ret s t (0 :: (s.now + 1) :: ms ::"
mutant "the clock's minutes run past 59" \
  "(secs / 3600, secs / 60 % 60, secs % 60)" "(secs / 3600, secs / 60, secs % 60)"
mutant "sleep rounds down" \
  "let ticks := (ms + tickMs - 1) / tickMs" "let ticks := ms / tickMs"

mutant "USB start skips the DMA check" \
  "if dmaOk s.cur t.caps dma (size % 2 ^ 19 + usbSlack) (bit value 15) then" "if true then"
mutant "USB DMA check ignores the transfer's direction" \
  "Nat.ble (a + n) (frameBase + (b + k) * pageSize) && (if w then c.rights.w else c.rights.r)" "Nat.ble (a + n) (frameBase + (b + k) * pageSize) && true"
mutant "USB DMA check ignores the end of the run" \
  "Nat.ble (a + n) (frameBase + (b + k) * pageSize) && (if w" "true && (if w"
mutant "USB DMA into memory the driver was lent" \
  "     | .frames b k => Nat.ble (framesPerTask * j) b && Nat.ble (b + k) (framesPerTask * (j + 1)) &&" "     | .frames b k =>"
mutant "a receiver gives up before its deadline" \
  "    if !(u == 0) && Nat.ble u now then { t with status := .ready, result := eTimeout :: .nil } else t" "    if !(u == 0) then { t with status := .ready, result := eTimeout :: .nil } else t"
mutant "a receiver told to wait forever gives up" \
  "    if !(u == 0) && Nat.ble u now then { t with status := .ready, result := eTimeout :: .nil } else t" "    if Nat.ble u now then { t with status := .ready, result := eTimeout :: .nil } else t"
mutant "the network service may pass Terminal's memory on" \
  "(frameCaps 17) (epCap 0 false true false 17)" "(frameCaps 17) (epCap 0 false true true 17)"
mutant "USB DMA check forgets the packet of slack" \
  "(size % 2 ^ 19 + usbSlack)" "(size % 2 ^ 19)"
mutant "a channel's DMA address goes straight to the controller" \
  "if inChan reg && chanReg reg == 0x14 then" "if false then"
mutant "descriptor DMA allowed" \
  "(reg == 0x00C && bit value 30) || (reg == 0x400 && bit value 23) ||" "(reg == 0x00C && bit value 30) ||"
mutant "device mode allowed" \
  "(reg == 0x00C && bit value 30) || (reg == 0x400 && bit value 23) ||" "(reg == 0x400 && bit value 23) ||"
mutant "device mode's registers writable" \
  "(Nat.ble 0x800 reg && Nat.ble (reg + 1) 0xC00) ||" ""
mutant "manifest gives mallory the USB controller" \
  "| 2 => snoc (frameCaps 2) (epCap 0 false true false 2)" "| 2 => snoc (snoc (frameCaps 2) (epCap 0 false true false 2)) usbCap"
mutant "grant the USB capability" \
  "      | .frames _ _ => some (some g)
      | _ => none" "      | .frames _ _ => some (some g)
      | .usbHost => some (some g)
      | _ => none"

mutant "stop stops the slot after the one it names" \
  "          ret (setTask s k { u with status := .dead, result := .nil }) t (0 :: .nil)" "          ret (setTask s (k + 1) { u with status := .dead, result := .nil }) t (0 :: .nil)"

mutant "Security is given the time of day" \
  "  | 7 => snoc (frameCaps 7) (epCap 0 false true true 7)" "  | 7 => snoc (snoc (frameCaps 7) (epCap 0 false true true 7)) wallCap"
mutant "time sets the time of day" \
  "  ret s t (0 :: s.now :: ms ::" "  ret { s with wall := s.now } t (0 :: s.now :: ms ::"
mutant "the scheduler ignores what the other cores run" \
  "def runnable (busy : List Nat) (ts : List Task) (j : Nat) : Bool := isReady ts j && !memNat j busy" "def runnable (busy : List Nat) (ts : List Task) (j : Nat) : Bool := isReady ts j"
mutant "enter forgets one core" \
  "def enter (s : KState) (c b0 b1 b2 : Nat) : KState := { s with cur := c, busy := b0 :: b1 :: b2 :: .nil }" "def enter (s : KState) (c b0 b1 b2 : Nat) : KState := { s with cur := c, busy := b0 :: b1 :: .nil }"
mutant_journal "the journal writes home before the commit" \
  "  jw J 0 (t.map Prod.snd) ++
    (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (t ++ (J, clean) :: .nil)" "  jw J 0 (t.map Prod.snd) ++ t ++
    (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (J, clean) :: .nil"
mutant_journal "the journal commits before its copies are written" \
  "  jw J 0 (t.map Prod.snd) ++
    (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (t ++ (J, clean) :: .nil)" "  (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (jw J 0 (t.map Prod.snd) ++
    (t ++ (J, clean) :: .nil))"
mutant_journal "recovery never finishes a committed change" \
  "    then upd (applyW (ts.zip (readJ d J 0 n)) d) J clean" "    then upd d J clean"
mutant_journal "recovery replays only the first block" \
  "    then upd (applyW (ts.zip (readJ d J 0 n)) d) J clean" "    then upd (applyW ((ts.zip (readJ d J 0 n)).take 1) d) J clean"

} | python3 test/mutants.py ${JOBS:-}
