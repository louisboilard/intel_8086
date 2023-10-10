use std::fmt;
use std::fmt::Display;

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
    /// 1 bit. Wide. 0 means the instruction is operating on 1byte. 1 means 2 bytes.
    W(BitFlag),
    /// 1 bit. Sign extension. (for arithmetic ops)
    S(BitFlag),
    /// 2 bits. Memory or register operation (register-register, register-mem..)
    Mod(BitFlag),
    /// 3 bit. Encodes a register.
    Reg(BitFlag),
    /// 3 bit. Encodes a register or memory (depending on MOD).
    Rm(BitFlag),
}

impl Flag {
    /// Returns the number of bits of a flag.
    pub fn get_width(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.width,
            Flag::W(flag) => flag.width,
            Flag::S(flag) => flag.width,
            Flag::Mod(flag) => flag.width,
            Flag::Reg(flag) => flag.width,
            Flag::Rm(flag) => flag.width,
        }
    }

    /// Returns the flag's value.
    pub fn get_value(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.value,
            Flag::W(flag) => flag.value,
            Flag::S(flag) => flag.value,
            Flag::Mod(flag) => flag.value,
            Flag::Reg(flag) => flag.value,
            Flag::Rm(flag) => flag.value,
        }
    }

    /// Sets the flag's value.
    pub fn set_value(&mut self, val: u8) {
        match self {
            Flag::D(flag) => flag.value = val,
            Flag::W(flag) => flag.value = val,
            Flag::S(flag) => flag.value = val,
            Flag::Mod(flag) => flag.value = val,
            Flag::Reg(flag) => flag.value = val,
            Flag::Rm(flag) => flag.value = val,
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

    /// Creates a new D Instruction Flag.
    pub fn new_s(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::S(BitFlag {
                width: 1,
                value: val,
            }),
            None => Flag::S(BitFlag { width: 1, value: 0 }),
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
            Some(val) => Flag::Mod(BitFlag {
                width: 2,
                value: val,
            }),
            None => Flag::Mod(BitFlag { width: 2, value: 0 }),
        }
    }

    /// Creates a new REG Instruction Flag.
    pub fn new_reg(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::Reg(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::Reg(BitFlag { width: 3, value: 0 }),
        }
    }

    /// Creates a new RM Instruction Flag.
    pub fn new_rm(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::Rm(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::Rm(BitFlag { width: 3, value: 0 }),
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
