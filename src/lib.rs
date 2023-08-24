//! Intel 8086 CPU simulator.
//!
//! Instructions follow the 16 bits pattern:
//!
//! First byte: [6bits: op_code][1bit: d_flag][1bit: w_flag]
//!
//! second byte: [2bits: mod_flag][3bit: reg_flag][3bit: rm_flag]

use std::fmt;
use std::fmt::Display;
use std::str;
use std::str::FromStr;

// Instruction size in bytes
const INSTRUCTION_SIZE: usize = 2;

/* ===============================================
*  =============== BIT MASKS =====================
*  ===============================================
*/

// MASKS FOR THE FIRST BYTE OF AN INSTRUCTION

// Instruction Mask. 6 highest bits represent the instruction.
const OPCODE_MASK: u8 = 0b1111_1100;
// D Flag Mask. 7th bit.
const D_FLAG_BITS_MASK: u8 = 0b0000_0010;
// D Flag Mask. LSB of the first byte.
const W_FLAG_BITS_MASK: u8 = 0b0000_0001;

// MASKS FOR THE SECOND BYTES OF AN INSTRUCTION

// Mod Flag Mask. 6 highest bits represent the instruction.
const MOD_FLAG_BITS_MASK: u8 = 0b1100_0000;
// REG Flag Mask. 7th bit.
const REG_FLAG_BITS_MASK: u8 = 0b0011_1000;
// RM Flag Mask. bits 6-7-8
const RM_FLAG_BITS_MASK: u8 = 0b0000_0111;

/* ===============================================
*  ===============================================
*  ===============================================
*/

/* ===============================================
*  ===============  OP CODE  =====================
*  ===============================================
*/

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum OpKind {
    ImmediateRegister,
    RegisterToRegister,
    UNKNOWN,
}

/// CPU Instructions
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum OpCode {
    /// MOV DST, SRC (copy)
    MOV,
    /// Represents an unrecognized instruction.
    UNKNOWN,
}

impl OpCode {
    /// Returns a mnemonic variant based on the byte's value.
    pub fn from_binary(val: u8) -> Option<(Self, OpKind)> {
        // register to register instructions have 6 bits op
        let register_to_register_op: u8 = val >> 2;

        let immediate_register_op: u8 = val >> 4;
        match register_to_register_op {
            // MOV is 100010 (34) with 6bits
            0b_0010_0010 => Some((Self::MOV, OpKind::RegisterToRegister)),
            _ => {
                // check if facing an immediate register OP
                match immediate_register_op {
                    0b_0000_1011 => Some((Self::MOV, OpKind::ImmediateRegister)),
                    _ => None,
                }
            }
        }
    }

    /// Returns a byte representing the 6bit for the opcode.
    pub fn to_byte(&self) -> Option<u8> {
        match self {
            Self::MOV => Some(0b_10_001000),
            _ => None,
        }
    }

    /// Returns a mnemonic variant based on asm op_code
    pub fn from_text(op_code: &str) -> Option<Self> {
        match op_code {
            "mov" | "MOV" => Some(Self::MOV),
            _ => None,
        }
    }
}

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/* ===============================================
*  ===============  REGISTER  ====================
*  ===============================================
*/

/// Registers. H -> High byte. L -> Low byte. X -> Full 16 bits
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Register {
    /// AX -> General purpose register A, using all 16 bits.
    Ax,
    /// Al -> General purpose register A, using the lower 8 bits.
    Al,
    /// Ah -> General purpose register A, using the upper 8 bits.
    Ah,
    /// Bx -> General purpose register B, using all 16 bits.
    Bx,
    /// Bl -> General purpose register B, using the lower 8 bits.
    Bl,
    /// Bh -> General purpose register B, using the upper 8 bits.
    Bh,
    /// Cx -> General purpose register C, using all 16 bits.
    Cx,
    /// Cl -> General purpose register C, using the lower 8 bits.
    Cl,
    /// Ch -> General purpose register C, using the upper 8 bits.
    Ch,
    /// Dx -> General purpose register D, using all 16 bits.
    Dx,
    /// Dl -> General purpose register D, using the lower 8 bits.
    Dl,
    /// Dh -> General purpose register D, using the upper 8 bits.
    Dh,
    Sp,
    Bp,
    Si,
    Di,
    /// An unrecognized register.
    UNKNOWN,
}

impl Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl FromStr for Register {
    type Err = ();

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "ax" => Ok(Self::Ax),
            "al" => Ok(Self::Al),
            "ah" => Ok(Self::Ah),
            "bx" => Ok(Self::Bx),
            "bl" => Ok(Self::Bl),
            "bh" => Ok(Self::Bh),
            "cx" => Ok(Self::Cx),
            "cl" => Ok(Self::Cl),
            "ch" => Ok(Self::Ch),
            "dx" => Ok(Self::Dx),
            "dl" => Ok(Self::Dl),
            "dh" => Ok(Self::Dh),
            "sp" => Ok(Self::Sp),
            "bp" => Ok(Self::Bp),
            "si" => Ok(Self::Si),
            "di" => Ok(Self::Di),
            _ => Err(()),
        }
    }
}

impl Register {
    /// Outputs which register the wide and register(REG/RM) flags represent.
    fn from_flags(wide_flag: u8, register_flag: u8) -> Self {
        // Wide is a bitflag of size 1. reg is 3bits wide.
        if wide_flag > 0b_0000_0111 || register_flag > 0b_0000_0111 {
            return Self::UNKNOWN;
        }

        // When wide == 1, instruction is on 16bits.
        match wide_flag {
            1 => match register_flag {
                0b_0000_0000 => Self::Ax,
                0b_0000_0001 => Self::Cx,
                0b_0000_0010 => Self::Dx,
                0b_0000_0011 => Self::Bx,
                0b_0000_0100 => Self::Sp,
                0b_0000_0101 => Self::Bp,
                0b_0000_0110 => Self::Si,
                0b_0000_0111 => Self::Di,
                _ => Self::UNKNOWN,
            },
            // wide == 0 -> instruction is on 8bits.
            0 => match register_flag {
                0b_0000_0000 => Self::Al,
                0b_0000_0001 => Self::Cl,
                0b_0000_0010 => Self::Dl,
                0b_0000_0011 => Self::Bl,
                0b_0000_0100 => Self::Ah,
                0b_0000_0101 => Self::Ch,
                0b_0000_0110 => Self::Dh,
                0b_0000_0111 => Self::Bh,
                _ => Self::UNKNOWN,
            },
            _ => Self::UNKNOWN,
        }
    }
}

/* ===============================================
*  ============== BITFLAG/FLAG ===================
*  ===============================================
*/
/// A variable width bit flag
#[derive(Debug, Copy, Clone)]
pub struct BitFlag {
    /// The number of bits for the flag.
    width: u8,
    /// The flag's value. Defaults to 0.
    value: u8,
}

/// CPU Flag
#[derive(Debug, Copy, Clone)]
pub enum Flag {
    /// 1 bit. Specifies if the REG flag represents SRC (when 0) or DST (when 1)
    D(BitFlag),
    /// 1 bit. Wide. 0 means the instruction is operating on 1byte. 1 means 16 bytes.
    W(BitFlag),
    /// 2 bits. Memory or register operation (register-register, register-mem..)
    MOD(BitFlag),
    /// 3 bit. Encodes a register.
    REG(BitFlag),
    /// 3 bit. Encodes a register or memory (depending on MOD).
    RM(BitFlag),
}

impl Flag {
    /// Returns the number of bits of a flag.
    pub fn get_width(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.width,
            Flag::W(flag) => flag.width,
            Flag::MOD(flag) => flag.width,
            Flag::REG(flag) => flag.width,
            Flag::RM(flag) => flag.width,
        }
    }

    /// Returns the flag's value.
    pub fn get_value(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.value,
            Flag::W(flag) => flag.value,
            Flag::MOD(flag) => flag.value,
            Flag::REG(flag) => flag.value,
            Flag::RM(flag) => flag.value,
        }
    }

    /// Sets the flag's value.
    pub fn set_value(&mut self, val: u8) {
        match self {
            Flag::D(flag) => flag.value = val,
            Flag::W(flag) => flag.value = val,
            Flag::MOD(flag) => flag.value = val,
            Flag::REG(flag) => flag.value = val,
            Flag::RM(flag) => flag.value = val,
        }
    }

    /// Creates a new D Instruction Flag.
    pub fn new_d(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::D(BitFlag {
                width: 1,
                value: val,
            }),
            None => Flag::D(BitFlag { width: 1, value: 0 }),
        }
    }

    /// Creates a new W Instruction Flag.
    pub fn new_w(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::W(BitFlag {
                width: 1,
                value: val,
            }),
            None => Flag::W(BitFlag { width: 1, value: 0 }),
        }
    }

    /// Creates a new MOD Instruction Flag.
    pub fn new_mod(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::MOD(BitFlag {
                width: 2,
                value: val,
            }),
            None => Flag::MOD(BitFlag { width: 2, value: 0 }),
        }
    }

    /// Creates a new REG Instruction Flag.
    pub fn new_reg(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::REG(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::REG(BitFlag { width: 3, value: 0 }),
        }
    }

    /// Creates a new RM Instruction Flag.
    pub fn new_rm(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::RM(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::RM(BitFlag { width: 3, value: 0 }),
        }
    }
}

impl Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.get_value();
        write!(
            f,
            "width: {}, value: {} -> {:#b}",
            self.get_width(),
            val,
            val
        )
    }
}

/* ===============================================
*  ============== INSTRUCTIONS ====================
*  ===============================================
*/

/// Functionalities of Instructions
pub trait Instructionable {
    /// Converts instruction to it's binary representation (machine code)
    fn assemble(&self) -> Result<Vec<u8>, String>;

    /// Converts instruction to it's ASM equivalent
    fn disassemble(&self) -> String;
}

/// Possible 8086 Instructions
#[derive(Debug, Copy, Clone)]
pub enum Instruction {
    /// Instruction that operates on two registers
    RegisterToRegister(RegisterToRegisterInst),
    // TODO
    ImmediateToRegister(()),
    // TODO
    MemoryToRegister(()),

    /// Unknown instruction
    UNKNOWN,
}

impl Instructionable for Instruction {
    /// Dispatches assemble() to the associated instruction type
    fn assemble(&self) -> Result<Vec<u8>, String> {
        match self {
            Self::RegisterToRegister(inst) => inst.assemble(),
            _ => Err("".to_owned()),
        }
    }

    /// Dispatches dissasemble() to the associated instruction type
    fn disassemble(&self) -> String {
        match self {
            Self::RegisterToRegister(inst) => inst.disassemble(),
            // todo: handle this
            _ => "Invalid instruction".to_owned(),
        }
    }
}

/// An intel_8086 Register to Register Instruction
/// i.e: ```MOV AX,BX```
#[derive(Debug, Copy, Clone)]
pub struct RegisterToRegisterInst {
    /// Instruction's common name in asm (mov)
    mnemonic: OpCode,
    /// Number of bytes (2) for this instruction.
    width: usize,
    /// D bit flag
    pub d_flag: Flag,
    /// W bit flag
    pub w_flag: Flag,
    /// MOD bit flag
    pub mod_flag: Flag,
    /// REG bit flag
    pub reg_flag: Flag,
    /// RM bit flag
    pub rm_flag: Flag,
}

impl RegisterToRegisterInst {
    pub fn new(
        mnemonic: OpCode,
        d_flag: Flag,
        w_flag: Flag,
        mod_flag: Flag,
        reg_flag: Flag,
        rm_flag: Flag,
    ) -> Self {
        Self {
            mnemonic,
            width: INSTRUCTION_SIZE,
            d_flag,
            w_flag,
            mod_flag,
            reg_flag,
            rm_flag,
        }
    }

    /// Constructs a RegisterToRegisterInst from two bytes
    pub fn from_bytes(high_byte: u8, low_byte: u8) -> Result<RegisterToRegisterInst, String> {
        let instruction_value = high_byte & OPCODE_MASK;
        let Some((instruction_mnemonic, _)) = OpCode::from_binary(instruction_value) else {
            return Err(format!(
                "Invalid instruction of value {} is not a known instruction.",
                instruction_value
            ));
        };

        const BYTE_LENGTH: u8 = 8;
        // Get value + shift so that the set bits are at LSB in the byte.

        // mod has size 2 and starts at MSB.
        let mod_val = (low_byte & MOD_FLAG_BITS_MASK) >> (BYTE_LENGTH - 2);
        // reg has size 3 and starts at pos 3 from MSB (0011_1_000)
        let reg_val = (low_byte & REG_FLAG_BITS_MASK) >> 3;
        // rm has size 3 and starts at pos 6 from MSB
        let rm_val = low_byte & RM_FLAG_BITS_MASK;

        Ok(RegisterToRegisterInst::new(
            instruction_mnemonic,
            Flag::new_d(Some(high_byte & D_FLAG_BITS_MASK)),
            Flag::new_w(Some(high_byte & W_FLAG_BITS_MASK)),
            Flag::new_mod(Some(mod_val)),
            Flag::new_reg(Some(reg_val)),
            Flag::new_rm(Some(rm_val)),
        ))
    }
}

impl Instructionable for RegisterToRegisterInst {
    /// Converts to the 16bit binary representation of the instruction.
    fn assemble(&self) -> Result<Vec<u8>, String> {
        // Opcode takes the first 6 bits of the first byte.
        let op_code = self.mnemonic.to_byte().unwrap();

        // First byte: [6bits: op code][1bit: d_flag][1bit: w_flag]
        let mut first_byte: u8 = op_code;

        let d_flag = self.d_flag.get_value();
        if d_flag > 1 {
            return Err(String::from("d_flag should be 0 or 1."));
        }
        // index of d_flag is 1
        first_byte |= d_flag << 1;
        let w_flag = self.w_flag.get_value();
        if w_flag > 1 {
            return Err(String::from("w_flag should be 0 or 1."));
        }
        // index of w_flag is 0
        first_byte |= w_flag;

        // mod_flag is 2 bits at MSB+ MSB-1 (11_000000)
        let mut second_byte: u8 = self.mod_flag.get_value();
        // reg_flag is 3 bits.
        second_byte = second_byte << self.reg_flag.get_width() | self.reg_flag.get_value();
        // rm flag is 3 bits.
        second_byte = second_byte << self.rm_flag.get_width() | self.rm_flag.get_value();

        Ok(vec![first_byte, second_byte])
    }

    /// Converts to a String which represents the ASM instruction.
    /// Ex: ```MOV AX,BX`
    fn disassemble(&self) -> String {
        let mut asm = self.mnemonic.to_string().to_ascii_lowercase() + " ";
        let dst = Register::from_flags(self.w_flag.get_value(), self.rm_flag.get_value());
        asm += dst.to_string().to_ascii_lowercase().as_str();
        asm += ", ";
        let src = Register::from_flags(self.w_flag.get_value(), self.reg_flag.get_value());
        asm += src.to_string().to_ascii_lowercase().as_str();
        asm
    }
}

impl Display for RegisterToRegisterInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "
{:?} instruction:
width: {},
d_flag: {},
w_flag: {},
mod_flag: {},
reg_flag: {},
rm_flag: {}
",
            self.mnemonic,
            self.width,
            self.d_flag,
            self.w_flag,
            self.mod_flag,
            self.reg_flag,
            self.rm_flag,
        )
    }
}
impl Default for RegisterToRegisterInst {
    fn default() -> Self {
        Self {
            mnemonic: OpCode::MOV,
            width: 2,
            d_flag: Flag::new_d(None),
            w_flag: Flag::new_d(None),
            mod_flag: Flag::new_mod(None),
            reg_flag: Flag::new_reg(None),
            rm_flag: Flag::new_rm(None),
        }
    }
}

/// Takes in an arbitrary number of 16 bits machine code instructions
/// Returns a Vec<Instruction>
pub fn read_instructions(instructions: &[u8]) -> Result<Vec<Instruction>, String> {
    // smallest potential nb of instruction since smallest inst is INSTRUCTION_SIZE
    let nb_instructions = instructions.len() / INSTRUCTION_SIZE;
    let mut instructions_vec: Vec<Instruction> = Vec::with_capacity(nb_instructions);

    let mut index = 0;
    while index < nb_instructions {
        match OpCode::from_binary(instructions[index]) {
            Some((_, op_kind)) => match op_kind {
                OpKind::RegisterToRegister => {
                    match RegisterToRegisterInst::from_bytes(
                        instructions[index],
                        instructions[index + 1],
                    ) {
                        Ok(i) => {
                            index += i.width;
                            instructions_vec.push(Instruction::RegisterToRegister(i));
                        }
                        Err(e) => return Err(e),
                    }
                }
                _ => return Err("Unknown instruction".to_owned()),
            },
            None => return Err("Could not parse instruction".to_owned()),
        };
    }

    Ok(instructions_vec)
}

// ***********************************************************************
// =======================================================================
// ================================ TESTS ================================
// =======================================================================
// ***********************************************************************
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assemble_test() {
        let bin = include_bytes!("../data/binary/single_register_mov.txt");
        let inst = RegisterToRegisterInst::from_bytes(bin[0], bin[1]).unwrap();
        let bin_from_inst = inst.assemble().unwrap();
        assert_eq!(bin_from_inst, bin.to_owned());
    }

    #[test]
    fn assemble_multiple_test() {
        let bin = include_bytes!("../data/binary/many_register_mov.txt");
        let instructions = read_instructions(bin).unwrap();
        // compare all individual instructions with binary equivalent
        let mut count = 0;
        for i in instructions.iter() {
            let bytes: [u8; 2] = [bin[count], bin[count + 1]];
            assert_eq!(i.assemble().unwrap(), bytes);
            count += 2;
        }
    }

    #[test]
    fn dissasemble_multiple_test() {
        let bin = include_bytes!("../data/binary/many_register_mov.txt");
        let asm = include_str!("../data/asm/many_register_mov.asm");

        let instructions = read_instructions(bin).unwrap();

        let mut splitted_asm = asm.lines();

        // compare all individual instructions with asm equivalent
        for inst in instructions.iter() {
            let dissas = inst.disassemble();
            assert_eq!(dissas, splitted_asm.next().unwrap());
        }
    }

    #[test]
    fn dissasemble_test() {
        let single_asm_inst = include_str!("../data/asm/single_register_mov.asm");
        let bin = include_bytes!("../data/binary/single_register_mov.txt");
        let inst = read_instructions(bin).unwrap()[0];
        assert_eq!(
            inst.disassemble(),
            single_asm_inst.to_owned().strip_suffix('\n').unwrap()
        );
    }
}
