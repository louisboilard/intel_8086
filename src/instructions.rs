use std::fmt::Display;
use std::fmt;

use crate::bitflag::Flag;
use crate::opcode::{OpCode, OpKind};
use crate::register::Register;

// Instruction size in bytes
pub const INSTRUCTION_SIZE: usize = 2;

/* ===============================================
*  =============== BIT MASKS =====================
*  ===============================================
*/

// MASKS FOR THE FIRST BYTE OF AN INSTRUCTION

// Instruction Mask. 6 highest bits represent the instruction.
const OPCODE_MASK: u8 = 0b1111_1100;
// D Flag Mask. 7th bit.
const D_FLAG_BITS_MASK: u8 = 0b0000_0010;
// S Flag Mask. 7th bit.
const S_FLAG_BITS_MASK: u8 = 0b0000_0010;
// D Flag Mask. LSB of the first byte.
const W_FLAG_BITS_MASK: u8 = 0b0000_0001;

// MASKS FOR THE SECOND BYTES OF AN INSTRUCTION

// Mod Flag Mask. 6 highest bits represent the instruction.
const MOD_FLAG_BITS_MASK: u8 = 0b1100_0000;
// REG Flag Mask. 7th bit.
const REG_FLAG_BITS_MASK: u8 = 0b0011_1000;
// RM Flag Mask. bits 6-7-8
const RM_FLAG_BITS_MASK: u8 = 0b0000_0111;

const BYTE_LENGTH: u8 = 8;


/* ===============================================
*  ============== INSTRUCTIONS ====================
*  ===============================================
*/

/// Functionalities of Instructions
pub trait Instructionable {
    /// Converts instruction to it's binary representation (machine code)
    fn assemble(&self) -> Result<Vec<u8>, String>;

    /// Converts instruction to it's ASM equivalent
    fn disassemble(&self) -> Option<String>;
}

// Used to do concrete type evaluation at runtime instead of dynamic dispatch
// API consumer is unaware of the underlying Instruction "kind"/real type and
// can freely use fn's from the Instructionable trait.

/// 8086 Instructions
#[derive(Debug, Copy, Clone)]
pub enum Instruction {
    /// Register <-> Register instruction
    RegisterToRegister(RegisterToRegisterInst),
    /// Directly operates on register
    ImmediateToRegister(ImmediateRegisterInst),
    /// Directly operates on register OR memory
    ImmediateToRegisterOrMemory(ImmediateToRegisterMemInst),
    /// Unknown instruction
    UNKNOWN,
}

impl Instructionable for Instruction {
    /// Assembles's the given instruction, resulting in it's machine code
    /// binary equivalence.
    fn assemble(&self) -> Result<Vec<u8>, String> {
        // Dispatches assemble() to the associated instruction type
        match self {
            Self::RegisterToRegister(inst) => inst.assemble(),
            Self::ImmediateToRegister(inst) => inst.assemble(),
            // Self::ImmediateToRegisterOrMemory(inst) => inst.assemble(),
            _ => Err("".to_owned()),
        }
    }

    /// Dissasemble's the given instruction, resulting in it's ASM equivalence
    /// in String form.
    fn disassemble(&self) -> Option<String> {
        // dispatches dissasemble() to the associated instruction type
        match self {
            Self::RegisterToRegister(inst) => inst.disassemble(),
            Self::ImmediateToRegister(inst) => inst.disassemble(),
            // Self::ImmediateToRegisterOrMemory(inst) => inst.dissasemble(),
            _ => None,
        }
    }
}


/// Immediate to register instruction.
/// Schema \[4bits :opcode, 1bit: w, 3bit: reg\]\[data\]\[data (if w = 1)\]
#[derive(Debug, Copy, Clone)]
#[allow(dead_code)]
pub struct ImmediateRegisterInst {
    /// Instruction's common name in asm (mov)
    mnemonic: OpCode,
    /// Number of bytes (3) for this instruction.
    width: usize,
    /// S bit flag (sign extension, for arithemtic ops)
    s_flag: Flag,
    /// W bit flag
    w_flag: Flag,
    /// Reg bit flag
    reg_flag: Flag,
    /// Immediate data byte
    data_lo: u8,
    /// Immediate data byte (only in 16bits mode, when w flag is set)
    data_hi: u8,
}

impl ImmediateRegisterInst {
    pub fn new(mnemonic: OpCode, w_flag: Flag, s_flag: Flag, reg_flag: Flag, data_lo: u8, data_hi: u8) -> Self {
        Self {
            mnemonic,
            width: 3,
            s_flag,
            w_flag,
            reg_flag,
            data_lo,
            data_hi,
        }
    }

    pub fn get_width(&self) -> usize {
        self.width
    }

    /// Generates an immediate register instruction based on valid machine code bytes
    pub fn from_bytes(
        first_byte: u8,
        data_byte: u8,
        data_byte_hi: u8,
    ) -> Result<ImmediateRegisterInst, String> {
        let instruction_value = first_byte & 0b1111_0000;
        let Some((instruction_mnemonic, _)) = OpCode::from_binary(instruction_value) else {
            return Err(format!(
                "Invalid instruction of value {} is not a known instruction.",
                instruction_value
            ));
        };

        let w_flag = (first_byte & 0b_0000_1000) >> 3;
        let reg_flag = first_byte & 0b_0000_0111;

        Ok(ImmediateRegisterInst::new(
            instruction_mnemonic,
            Flag::new_w(Some(w_flag)),
            Flag::new_s(None),
            Flag::new_reg(Some(reg_flag)),
            data_byte,
            data_byte_hi,
        ))
    }
}

impl Instructionable for ImmediateRegisterInst {

    fn assemble(&self) -> Result<Vec<u8>, String> {
        let data_byte = self.data_lo;
        // seems like nasm always produces data_hi regardless of mode
        let data_hi = self.data_hi;

        let mut first_byte = OpCode::to_byte(self.mnemonic, OpKind::ImmediateRegister).unwrap();

        let w_flag = self.w_flag.get_value();
        let reg_flag = self.reg_flag.get_value();

        first_byte |= w_flag << 3;
        first_byte |= reg_flag;

        Ok(vec![first_byte, data_byte, data_hi])

    }

    fn disassemble(&self) -> Option<String> {
        let mut asm = self.mnemonic.to_string().to_ascii_lowercase() + " ";
        let dst = Register::from_flags(self.w_flag.get_value(), self.reg_flag.get_value());
        asm += dst.to_string().to_ascii_lowercase().as_str();
        asm += ", ";

        let mut data_ : u16 = self.data_lo as u16;
        if self.data_hi != 0 {
            // Big endian.
            data_ = ((self.data_hi as u16) << 8) | self.data_lo as u16;
        }

        asm += data_.to_string().as_str();
        Some(asm)
    }
}

/// An intel_8086 Register to Register/memory Instruction
/// An immediate mode instruction that can be applied
/// directly to a register, but unlike it's ImmediateToRegisterInst
/// counterpart can also directly refer to a mem address.
/// i.e: ```MOV AX,BX```
#[derive(Debug, Copy, Clone)]
#[allow(dead_code)]
pub struct ImmediateToRegisterMemInst {
    /// Instruction's common name in asm (mov)
    mnemonic: OpCode,
    /// Number of bytes (up to 6) for this instruction.
    width: usize,
    /// S bit flag
    s_flag: Flag,
    /// W bit flag
    w_flag: Flag,
    /// MOD bit flag
    mod_flag: Flag,
    /// RM bit flag
    rm_flag: Flag,
}

impl ImmediateToRegisterMemInst {
    pub fn new(mnemonic: OpCode, width: usize, s_flag: Flag, w_flag: Flag, mod_flag: Flag, rm_flag: Flag) -> Self { Self { mnemonic, width, s_flag, w_flag, mod_flag, rm_flag } }

    pub fn from_bytes(high_byte: u8, low_byte: u8) -> Result<ImmediateToRegisterMemInst, String> {
        let instruction_value = high_byte & 0b_1111_1100;
        let Some((instruction_mnemonic, _)) = OpCode::from_binary(instruction_value) else {
            return Err(format!(
                "Invalid instruction of value {} is not a known instruction.",
                instruction_value
            ));
        };

        // Get value + shift so that the set bits are at LSB in the byte.

        // mod has size 2 and starts at MSB.
        let mod_val = (low_byte & MOD_FLAG_BITS_MASK) >> (BYTE_LENGTH - 2);
        // for this inst kind, r/m is 2 last bits of the second byte.
        let rm_val = low_byte & 0b_0000_0011;

        // TODO: find real size (not 2) + find s flag
        Ok(ImmediateToRegisterMemInst::new(
            instruction_mnemonic,
            2,
            Flag::new_s(Some(high_byte & S_FLAG_BITS_MASK)),
            Flag::new_w(Some(high_byte & W_FLAG_BITS_MASK)),
            Flag::new_mod(Some(mod_val)),
            Flag::new_rm(Some(rm_val)),
        ))
    }

    pub fn get_width(&self) -> usize {
        self.width
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
    d_flag: Flag,
    /// W bit flag
    w_flag: Flag,
    /// MOD bit flag
    mod_flag: Flag,
    /// REG bit flag
    reg_flag: Flag,
    /// RM bit flag
    rm_flag: Flag,
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

    pub fn get_width(&self) -> usize {
        self.width
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
        let op_code = self.mnemonic.to_byte(OpKind::MemoryOrRegToReg).unwrap();

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
    fn disassemble(&self) -> Option<String> {
        let mut asm = self.mnemonic.to_string().to_ascii_lowercase() + " ";
        let dst = Register::from_flags(self.w_flag.get_value(), self.rm_flag.get_value());
        asm += dst.to_string().to_ascii_lowercase().as_str();
        asm += ", ";
        let src = Register::from_flags(self.w_flag.get_value(), self.reg_flag.get_value());
        asm += src.to_string().to_ascii_lowercase().as_str();
        Some(asm)
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
            mnemonic: OpCode::Mov,
            width: 2,
            d_flag: Flag::new_d(None),
            w_flag: Flag::new_d(None),
            mod_flag: Flag::new_mod(None),
            reg_flag: Flag::new_reg(None),
            rm_flag: Flag::new_rm(None),
        }
    }
}

