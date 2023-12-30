use std::fmt;
use std::fmt::Display;
use std::str::FromStr;

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
    /// Ip -> Instruction Pointer.
    Ip,
    /// An unrecognized register.
    Unknown,
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
            "ip" => Ok(Self::Ip),
            _ => Err(()),
        }
    }
}

impl Register {
    /// Outputs which register the wide and register(REG/RM) flags represent.
    pub fn from_flags(wide_flag: u8, register_flag: u8) -> Self {
        // Wide is a bitflag of size 1. reg is 3bits wide.
        if wide_flag > 0b_0000_0111 || register_flag > 0b_0000_0111 {
            return Self::Unknown;
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
                _ => Self::Unknown,
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
                _ => Self::Unknown,
            },
            _ => Self::Unknown,
        }
    }
}

/// Registers: registers and their associated operations
#[derive(Debug)]
#[allow(dead_code)]
pub struct Registers {
    /// Ax general purpose register
    ax: u16,

    /// Bx general purpose register
    bx: u16,

    /// Cx general purpose register
    cx: u16,

    /// Dx general purpose register
    dx: u16,

    sp: u16,
    bp: u16,
    si: u16,
    di: u16,
    ip: u16,
}

impl Registers {
    pub fn new() -> Self {
        Self {
            ax: 0,
            bx: 0,
            cx: 0,
            dx: 0,
            sp: 0,
            bp: 0,
            si: 0,
            di: 0,
            ip: 0,
        }
    }

    /// Sets the lowest byte of the 16 bit Register to the desired value
    #[inline(always)]
    fn set_low_byte(byte: u8, current_val: u16) -> u16 {
        const MASK: u16 = 0b_1111_1111_0000_0000;
        (current_val & MASK) | byte as u16
    }

    /// Gets the lowest byte of the 16 bit Register
    #[inline(always)]
    fn get_low_byte(value: u16) -> u8 {
        const MASK: u16 = 0b_0000_0000_1111_1111;
        (value & MASK) as u8
    }

    /// Sets the high byte of the 16 bit Register to the desired value
    #[inline(always)]
    fn set_high_byte(byte: u8, current_val: u16) -> u16 {
        const MASK: u16 = 0b_0000_0000_1111_1111;
        (current_val & MASK) | (byte as u16) << 8
    }

    /// Gets the high byte of the 16 bit Register
    #[inline(always)]
    fn get_high_byte(value: u16) -> u8 {
        const MASK: u16 = 0b_1111_1111_0000_0000;
        ((value & MASK) >> 8) as u8
    }

    /// Given a Register variant, update the corresponding register
    pub fn update_register(&mut self, register: Register, value: u16) {
        match register {
            Register::Ax => self.ax = value,
            Register::Al => {
                self.ax = Self::set_low_byte(value as u8, self.ax);
            }
            Register::Ah => {
                self.ax = Self::set_high_byte(value as u8, self.ax);
            }
            Register::Bx => self.bx = value,
            Register::Bl => {
                self.bx = Self::set_low_byte(value as u8, self.bx);
            }
            Register::Bh => {
                self.bx = Self::set_high_byte(value as u8, self.bx);
            }
            Register::Cx => self.cx = value,
            Register::Cl => {
                self.cx = Self::set_low_byte(value as u8, self.cx);
            }
            Register::Ch => {
                self.cx = Self::set_high_byte(value as u8, self.cx);
            }
            Register::Dx => self.dx = value,
            Register::Dl => {
                self.dx = Self::set_low_byte(value as u8, self.dx);
            }
            Register::Dh => {
                self.dx = Self::set_high_byte(value as u8, self.dx);
            }
            Register::Sp => self.sp = value,
            Register::Bp => self.bp = value,
            Register::Si => self.si = value,
            Register::Di => self.di = value,
            Register::Ip => self.ip = value,
            Register::Unknown => (),
        }
    }

    pub fn get_value(&self, register: Register) -> Option<u16> {
        match register {
            Register::Ax => Some(self.ax),
            Register::Al => Some(Self::get_low_byte(self.ax) as u16),
            Register::Ah => Some(Self::get_high_byte(self.ax) as u16),
            Register::Bx => Some(self.bx),
            Register::Bl => Some(Self::get_low_byte(self.bx) as u16),
            Register::Bh => Some(Self::get_high_byte(self.bx) as u16),
            Register::Cx => Some(self.cx),
            Register::Cl => Some(Self::get_low_byte(self.cx) as u16),
            Register::Ch => Some(Self::get_high_byte(self.cx) as u16),
            Register::Dx => Some(self.dx),
            Register::Dl => Some(Self::get_low_byte(self.dx) as u16),
            Register::Dh => Some(Self::get_high_byte(self.dx) as u16),
            Register::Sp => Some(self.sp),
            Register::Bp => Some(self.bp),
            Register::Si => Some(self.si),
            Register::Di => Some(self.di),
            Register::Ip => Some(self.ip),
            Register::Unknown => None,
        }
    }

    /// Updates the instruction pointer register.
    pub fn update_instr_ptr(&mut self, value: usize) {
        self.ip += value as u16;
    }
}
