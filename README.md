# Intel 8086

A simple 8086 simulator.

Purely for entertainement and investigation purposes.

Reference [manual](https://edge.edx.org/c4x/BITSPilani/EEE231/asset/8086_family_Users_Manual_1_.pdf).

Data/binary contains the decoded assembly instructions, their equivalence
in assembly can be found in data/asm. Technically the simulator can take in the
decoded/raw binary instructions and turn them into asm and vice (re)versa.

8086 has 16 bits registers. Instructions width is 2 bytes and
follow the pattern:

| 1st byte: | op code  | d flag   | w flag   | 2nd byte: | mod flag | reg flag | rm flag |
|--         |-------------- | -------------- |--| -------------- | -- | --  |-- |
| --- | 6 bits    | 1 bit     | 1 bit  | --- | 2 bits | 3 bits | 3 bits |

* d = direction (to register or from register)
* w = word or byte operation (operating on full 16bits or only on 8bit)
* mod = Register mode
* reg = Register operand/extension of opcode
* rm = r/m register operand.


```6bits: MOV, 1bit: D, 1bit: W | 2bits: MOD, 3bits: REG, 3bits: RM```

asm format (specify `16 bits`): ```instruction dst, src``` ex ```mov ax, bx```

---
The emulator sucks in a stream of machine code instructions, interprets/parses
them into the defined instruction type and then operates on them.

For the sake of testing/completeness there's also a disassembler fn that
translate machine code back to asm.

#### Functionalities

- Interpret and parse valid 16 bits 8086 machine code instruction.

- Converts 8086 machine code to asm.

- Convert asm to machine code (allows reading in a file that contains a list of
  asm instructions separated by newlines). The asm instructions must be
  separated by newlines and in the following form: `opcode dst, src`
  ex: `mov ax, cx`.

- `machine code <-> type level representation <-> asm`
