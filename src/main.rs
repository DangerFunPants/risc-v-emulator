use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

use crate::helpers::{get_bits, splice_bits, twos_complement};

mod assembler;
mod helpers;

#[cfg(tests)]
mod nom_tests;

#[cfg(tests)]
mod helper_tests;

#[derive(Debug)]
pub enum Rv64VmError {
    InvalidRegisterNumber(u16),
    InvalidOpCode(u32),
    InvalidMux2Control(u32),
    InvalidAluControl(u32),
}

type Error = Rv64VmError;
pub type Result<T> = ::std::result::Result<T, Rv64VmError>;

#[derive(Debug, Copy, Clone, PartialEq)]
enum OpCode {
    BEQ,
    SW,
    LW,
    ADDI,
    RTYPE,
    HALT,
}

impl TryFrom<u32> for OpCode {
    type Error = Rv64VmError;
    fn try_from(code: u32) -> Result<OpCode> {
        Ok(match code {
            0b110_0011 => OpCode::BEQ,
            0b010_0011 => OpCode::SW,
            0b000_0011 => OpCode::LW,
            0b001_0011 => OpCode::ADDI,
            0b011_0011 => OpCode::RTYPE,
            0b000_0000 => OpCode::HALT,
            _ => return Err(Rv64VmError::InvalidOpCode(code)),
        })
    }
}

#[derive(Debug)]
struct InstructionMemory {
    base_address    : u32,
    memory          : HashMap<u32, u32>,
    a               : u32,
    rd              : u32,
}

impl fmt::Display for InstructionMemory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (addr, instruction) in self.memory.iter() {
            writeln!(f, "0x{:x}: 0x{:x}", addr, instruction);
        }
        Ok(())
    }
}

impl InstructionMemory {
    fn from_vec(instructions: Vec<u32>, base_address: u32) -> InstructionMemory {
        let mut instruction_memory = HashMap::new();
        for (offset, instruction) in instructions.iter().enumerate() {
            instruction_memory.insert((offset as u32)*4 + base_address, *instruction);
        }

        InstructionMemory { base_address
                          , memory      : instruction_memory      
                          , a           : 0
                          , rd          : 0
                          }
    }
    
    fn set_a(self: &mut Self, addr: u32) {
        self.a = addr;
    }

    fn clock_low(self: &mut Self) {
        println!("Instruction memory read location: {:x}", self.a);
        self.rd = *self.memory.get(&self.a).unwrap();
    }
}

struct DataMemory {
    a           : u32,
    wd          : u32,
    we          : bool,
    rd          : u32,
    memory      : HashMap<u32, u32>,
}

impl DataMemory {
    fn new() -> DataMemory {
        DataMemory {a: 0, wd: 0, we: false, rd: 0, memory: HashMap::new()}
    }

    fn set_a(self: &mut Self, val: u32) {
        self.a = val;
    }

    fn set_wd(self: &mut Self, val: u32) {
        self.wd = val;
    }

    fn set_we(self: &mut Self, val: bool) {
        self.we = val;
    }

    fn clock_low(self: &mut Self) {
        println!("Data memory read location: {}", self.a);
        self.rd = *self.memory.entry(self.a).or_insert(0);
    }
    
    fn clock_high(self: &mut Self) {
        if self.we {
            println!("Writing {} to address {}", self.wd, self.a);
            self.memory.insert(self.a, self.wd);
        }
    }

    fn initialize_memory(self: &mut Self, addr: u32, val: u32) {
        self.memory.insert(addr, val);
    }
}

struct RegisterFile {
    registers   : HashMap<u16, u32>,
    a1          : u16,
    a2          : u16,
    a3          : u16,
    wd3         : u32,
    we3         : bool,

    rd_1        : u32,
    rd_2        : u32,
}

impl fmt::Display for RegisterFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        println!("Register File:");
        for reg_num in 0..31_u16 {
            if self.registers.contains_key(&reg_num) {
                let reg_result = self.registers.get(&reg_num).unwrap();
                writeln!(f, "x{:2}: 0x{:x}", reg_num, reg_result);
            }
        }
        Ok(())
    }
}

impl RegisterFile {
    fn new() -> RegisterFile {
        RegisterFile { registers: HashMap::new()
                     , a1       : 0
                     , a2       : 0
                     , a3       : 0
                     , wd3      : 0
                     , we3      : false
                     , rd_1     : 0
                     , rd_2     : 0
                     }
    }

    fn set_a1(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a1 = val;
        Ok(())
    }

    fn set_a2(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a2 = val;
        Ok(())
    }

    fn set_a3(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a3 = val;
        Ok(())
    }

    fn set_wd3(self: &mut Self, val: u32) {
        self.wd3 = val;
    }

    fn set_we3(self: &mut Self, val: bool) {
        self.we3 = val;
    }

    fn clock_high(self: &mut Self) {
        self.rd_1 = *self.registers.entry(self.a1).or_insert(0);
        self.rd_2 = *self.registers.entry(self.a2).or_insert(0);
    }

    // Register file updates take place on the falling edge of clock cycles.
    fn clock_low(self: &mut Self) {
        if self.we3 {
            println!("writing {} to register number {}", self.wd3, self.a3);
            self.registers.insert(self.a3, self.wd3);
        }
    }

    fn initialize_register(self: &mut Self, reg_num: u16, val: u32) {
        self.registers.insert(reg_num, val);
    }
}

struct Rv64Vm {
    fd_register             : FDRegister,
    de_register             : DERegister,
    em_register             : EMRegister,
    mw_register             : MWRegister,
    wf_register             : WFRegister,
    instruction_memory      : InstructionMemory,
    data_memory             : DataMemory,
    register_file           : RegisterFile,
    last_cycle_was_stall    : bool,
}

enum Rv64VmState {
    Idle,
    Halted,
}

impl Rv64Vm {
    fn from_instructions(instructions: Vec<u32>, base_address: u32) -> Rv64Vm {
        let imem = InstructionMemory::from_vec(instructions, base_address);
        let dmem = DataMemory::new();
        let register_file = RegisterFile::new();
        let fd_register = FDRegister::new(base_address);
        let de_register = DERegister::new();
        let em_register = EMRegister::new();
        let mw_register = MWRegister::new();
        let wf_register = WFRegister::new(base_address);

        Rv64Vm { fd_register
               , de_register
               , em_register
               , mw_register
               , wf_register
               , instruction_memory: imem
               , data_memory: dmem
               , register_file
               , last_cycle_was_stall: false
               }
    }

    fn execute_program(self: &mut Self) -> Result<Rv64VmState> {
        let mut executed_cycles = 0;
        loop {
            executed_cycles += 1;
            println!("************************ Start of Cycle {} ************************", executed_cycles);
            match self.execute_a_cycle()? {
                Rv64VmState::Idle => {},
                Rv64VmState::Halted => break,
            };
            println!("************************ End of Cycle {} ************************", executed_cycles);
        }
        println!("Executed {} cycles.", executed_cycles);
        Ok(Rv64VmState::Halted)
    }

    fn execute_a_cycle(self: &mut Self) -> Result<Rv64VmState> {
        let is_branch = self.writeback_stage()?;
        self.fetch_stage();
        let op_code = self.decode_stage()?;
        self.execute_stage();
        self.mem_stage();
        
        // In the case that we branch, invalidate the last 3 instructions in 
        // the pipeline. 
        if is_branch {
            self.fd_register.instruction_in = 0x13; // NOP

            self.de_register.reg_write_in = false;
            self.de_register.mem_write_in = false;
            self.de_register.branch_in = false;

            self.em_register.mem_write_in = false;
            self.em_register.reg_write_in = false;
            self.em_register.branch_in = false;
        }

        let src_reg_1 = get_bits(19, 15, self.fd_register.instruction_out);
        let src_reg_2 = get_bits(24, 20, self.fd_register.instruction_out);
        let exec_write_reg = self.de_register.wd_out;
        let mem_write_reg = self.em_register.wd_out;

        let mut src_reg_1_forwarded = false;
        let mut src_reg_2_forwarded = false;
        let mut should_stall_for_lw = false;

        // I don't like that this is up here and not with the rest of the clock high calls. Putting
        // it here so that we can forward data memory read results from 2 removed ancestors.
        self.data_memory.clock_high();
        
        // Check if we need to forward the ALU result to either of the source registers.
        if self.de_register.reg_write_out {
            // Forward from the ALU
            if !self.de_register.mem_to_reg_out {
                if exec_write_reg == src_reg_1 {
                    self.de_register.rd_1_in = self.em_register.alu_out_in as u32;
                    src_reg_1_forwarded = true;
                }
                if exec_write_reg == src_reg_2 {
                    self.de_register.rd_2_in = self.em_register.alu_out_in as u32;
                    src_reg_2_forwarded = true;
                }
            } else {
                // Can't actually "forward" here, need to stall. 
                // This means that there is a lw in the execute stage that is loading into a
                // register that is a source for the current instruction.
                //
                // This is actually incorrect though since we could end up stalling and wasting a
                // cycle for instructions that don't actually have two source registers.
                // All instructions have src_reg_1, only R-type, SW and BEQ have src_reg_2.
                if exec_write_reg == src_reg_1 || exec_write_reg == src_reg_2 {
                    should_stall_for_lw = true;
                }
            }
        }

        // This is actually somewhat tedious. We could have one source register coming from 
        // the first ancestor and another source register coming from the second ancestor, need
        // to handle that case. 
        if self.em_register.reg_write_out {
            if !self.em_register.mem_to_reg_out {
                if mem_write_reg == src_reg_1 && !src_reg_1_forwarded {
                    self.de_register.rd_1_in = self.em_register.alu_out_out as u32;     
                }
                if mem_write_reg == src_reg_2 && !src_reg_2_forwarded {
                    self.de_register.rd_2_in = self.em_register.alu_out_out as u32;
                }
            } else {
                // Forward from DMEM.
                if mem_write_reg == src_reg_1 && !src_reg_1_forwarded {
                    self.de_register.rd_1_in = self.mw_register.read_data_in;
                }
                if mem_write_reg == src_reg_2 && !src_reg_2_forwarded {
                    self.de_register.rd_2_in = self.mw_register.read_data_in;
                }
            }
        }

        // I'm not certain that this makes sense. We set clock high for these registers
        // in the case that we're not stalling or in the case that we stalled last cycle. We don't
        // stall in the case that we stalled in the last cycle since we need to move the LW from 
        // decode into execute stage, and since the lw in the execute can't cause another data
        // hazard with the instruction that moves into decode, we don't need to worry about
        // stalling again.
        if !should_stall_for_lw || self.last_cycle_was_stall {
            self.fd_register.clock_high();
            self.de_register.clock_high();
            self.wf_register.clock_high();
            self.last_cycle_was_stall = false;
        } else {
            self.last_cycle_was_stall = true;
        }

        self.em_register.clock_high();
        self.mw_register.clock_high();

        Ok(match op_code {
            OpCode::HALT => Rv64VmState::Halted,
            _ => Rv64VmState::Idle,
        })
    }

    fn writeback_stage(self: &mut Self) -> Result<bool> {
        // BEGIN WB
        println!("Alu out in writeback: {:x}", self.mw_register.alu_out_out);
        let result = mux2(self.mw_register.mem_to_reg_out as u32, self.mw_register.alu_out_out, 
                          self.mw_register.read_data_out)?;
        self.register_file.set_a3(self.mw_register.rd_out as u16);
        self.register_file.set_wd3(result);
        self.register_file.set_we3(self.mw_register.reg_write_out);
        self.register_file.clock_low();
        let and_result = if self.em_register.branch_out && self.em_register.eq_comp_out {1} else {0};
        // and_result tells us if we should branch or not. 
        // so if and_result is true we need to invalidate the instructions that are currently in
        // fetch, decode and execute.
        println!("branch {} eq_comp {}", self.em_register.branch_out, self.em_register.eq_comp_out);
        let pc = mux2(and_result, self.wf_register.pc_out + 4, self.em_register.alu_out_out as u32)?;
        self.wf_register.pc_in = pc;
        Ok(self.em_register.branch_out && self.em_register.eq_comp_out)
    }

    fn fetch_stage(self: &mut Self) -> Result<()> {
        let pc = self.wf_register.pc_out;
        self.instruction_memory.set_a(pc);
        self.instruction_memory.clock_low();
    
        self.fd_register.pc_in = pc;
        self.fd_register.instruction_in = self.instruction_memory.rd;
        Ok(())
    }

    fn decode_stage(self: &mut Self) -> Result<OpCode> {
        let instr = self.fd_register.instruction_out;
        let a1 = get_bits(19, 15, instr);
        let a2 = get_bits(24, 20, instr);

        // Don't really know what the better solutions for these casts is?
        self.register_file.set_a1(a1 as u16);
        self.register_file.set_a2(a2 as u16);
        self.register_file.clock_high();

        let rd_1 = self.register_file.rd_1;
        let rd_2 = self.register_file.rd_2;

        let inB = get_bits(14, 12, instr);
        let inC = get_bits(6, 0, instr);
        let op_code = match OpCode::try_from(inC) {
            Ok(op_code) => op_code,
            Err(op_err) => return Err(op_err),
        };
        let wd = get_bits(11, 7, instr);
        println!("op code is {:?}, dst_reg: {}", op_code, wd);

        let (reg_write, mem_to_reg, mem_write, branch, alu_control, alu_src_b, alu_src_a) = 
            match op_code {
                OpCode::BEQ => (false, false, false, true, 0, 1, 0),
                OpCode::SW => (false, false, true, false, 0, 1, 1),
                OpCode::LW => (true, true, false, false, 0, 1, 1),
                OpCode::ADDI => (true, false, false, false, 0, 1, 1),
                OpCode::RTYPE => (true, false, false, false, inB, 0, 1),
                OpCode::HALT => (true, false, false, false, 0, 1, 1),
            };

        let immed = immed_gen(op_code, get_bits(31, 20, instr), get_bits(11, 0, instr));
        println!("Immediate value is: {}", immed);
        
        self.de_register.reg_write_in = reg_write;
        self.de_register.mem_to_reg_in = mem_to_reg;
        self.de_register.mem_write_in = mem_write;
        self.de_register.branch_in = branch;
        self.de_register.alu_control_in = alu_control;
        self.de_register.alu_src_a_in = alu_src_a;
        self.de_register.alu_src_b_in = alu_src_b;
        self.de_register.pc_in = self.fd_register.pc_out;
        self.de_register.rd_1_in = rd_1;
        self.de_register.rd_2_in = rd_2;
        self.de_register.wd_in = wd;
        self.de_register.immed_in = immed as u32;

        Ok(op_code)
    }

    fn execute_stage(self: &mut Self) -> Result<()> {
        let reg_write = self.de_register.reg_write_out;
        let mem_to_reg = self.de_register.mem_to_reg_out;
        let mem_write = self.de_register.mem_write_out;
        let branch = self.de_register.branch_out;
        let eq_comp = self.de_register.rd_1_out == self.de_register.rd_2_out;

        let alu_in_a = mux2(self.de_register.alu_src_a_out, self.de_register.pc_out, self.de_register.rd_1_out)?;
        println!("pc_out: {}, rd_1_out: {}", self.de_register.pc_out, self.de_register.rd_1_out);
        let alu_in_b = mux2(self.de_register.alu_src_b_out, 
                            self.de_register.rd_2_out, self.de_register.immed_out)?;
        let alu_out = alu_comp(self.de_register.alu_control_out, alu_in_a as i32, alu_in_b as i32)?;
        println!("alu_in_a: {}, alu_in_b: {}", alu_in_a, alu_in_b);
        println!("ALU out in exec stage {}", alu_out);
        let rd_2 = self.de_register.rd_2_out;
        let rd_1 = self.de_register.rd_1_out;
        
        self.em_register.reg_write_in = reg_write;
        self.em_register.mem_to_reg_in = mem_to_reg;
        self.em_register.mem_write_in = mem_write;
        self.em_register.branch_in = branch;
        self.em_register.eq_comp_in = eq_comp;
        self.em_register.alu_out_in = alu_out;
        self.em_register.rd_2_in = rd_2;
        self.em_register.rd_in = rd_1;
        self.em_register.wd_in = self.de_register.wd_out;
        Ok(())
    }

    fn mem_stage(self: &mut Self) -> Result<()> {
        let reg_write = self.em_register.reg_write_out;
        let mem_to_reg = self.em_register.mem_to_reg_out;

        self.data_memory.set_we(self.em_register.mem_write_out);
        self.data_memory.set_a(self.em_register.alu_out_out as u32);
        self.data_memory.set_wd(self.em_register.rd_2_out);
        self.data_memory.clock_low();
        let read_data = self.data_memory.rd;

        self.mw_register.reg_write_in = reg_write;
        self.mw_register.mem_to_reg_in = mem_to_reg;
        self.mw_register.alu_out_in = self.em_register.alu_out_out as u32;
        self.mw_register.read_data_in = read_data;
        self.mw_register.rd_in = self.em_register.wd_out;
        Ok(())
    }
}

struct FDRegister {
    pc_in           : u32,
    instruction_in  : u32,

    pc_out          : u32,
    instruction_out : u32,
}

impl FDRegister {
    fn new(base_address: u32) -> FDRegister {
        FDRegister {pc_in: base_address+4, instruction_in: 0x13, pc_out: 0, instruction_out: 0x13}
    }

    fn clock_high(self: &mut Self) {
        self.pc_out = self.pc_in;
        self.instruction_out = self.instruction_in;
    }
}

struct DERegister {
    reg_write_in    : bool,
    mem_to_reg_in   : bool,
    mem_write_in    : bool,
    branch_in       : bool,
    alu_control_in  : u32,
    alu_src_a_in    : u32,
    alu_src_b_in    : u32,
    pc_in           : u32,
    rd_1_in         : u32,
    rd_2_in         : u32,
    immed_in        : u32,
    wd_in           : u32,

    reg_write_out   : bool,
    mem_to_reg_out  : bool,
    mem_write_out   : bool,
    branch_out      : bool,
    alu_control_out : u32,
    alu_src_a_out   : u32,
    alu_src_b_out   : u32,
    pc_out          : u32,
    rd_1_out        : u32,
    rd_2_out        : u32,
    immed_out       : u32,
    wd_out          : u32,
}

impl DERegister {
    fn new() -> DERegister {
        DERegister { reg_write_in: false
                   , mem_to_reg_in: false
                   , mem_write_in: false
                   , branch_in: false
                   , alu_control_in: 0
                   , alu_src_a_in: 0
                   , alu_src_b_in: 0
                   , pc_in: 0
                   , rd_1_in: 0
                   , rd_2_in: 0
                   , immed_in: 0
                   , wd_in: 0
                   , reg_write_out: false
                   , mem_to_reg_out: false
                   , mem_write_out: false
                   , branch_out: false
                   , alu_control_out: 0
                   , alu_src_a_out: 0
                   , alu_src_b_out: 0
                   , pc_out: 0
                   , rd_1_out: 0
                   , rd_2_out: 0
                   , immed_out: 0
                   , wd_out: 0
                   }
    }

    fn clock_high(self: &mut Self) {
        self.reg_write_out = self.reg_write_in;
        self.mem_to_reg_out = self.mem_to_reg_in;
        self.mem_write_out = self.mem_write_in;
        self.branch_out = self.branch_in;
        self.alu_control_out = self.alu_control_in;
        self.alu_src_a_out = self.alu_src_a_in;
        self.alu_src_b_out = self.alu_src_b_in;
        self.pc_out = self.pc_in;
        self.rd_1_out = self.rd_1_in;
        self.rd_2_out = self.rd_2_in;
        self.immed_out = self.immed_in;
        self.wd_out = self.wd_in;
    }
}

struct EMRegister {
    reg_write_in    : bool,
    mem_to_reg_in   : bool,
    mem_write_in    : bool,
    branch_in       : bool,
    eq_comp_in      : bool,
    alu_out_in      : i32,
    rd_2_in         : u32,
    rd_in           : u32,
    wd_in           : u32,

    reg_write_out   : bool,
    mem_to_reg_out  : bool,
    mem_write_out   : bool,
    branch_out      : bool,
    eq_comp_out     : bool,
    alu_out_out     : i32,
    rd_2_out        : u32,
    rd_out          : u32,
    wd_out          : u32
}

impl EMRegister {
    fn new() -> EMRegister {
        EMRegister { reg_write_in: false
                   , mem_to_reg_in: false
                   , mem_write_in: false
                   , branch_in: false
                   , eq_comp_in: false
                   , alu_out_in: 0
                   , rd_2_in: 0
                   , rd_in: 0
                   , wd_in: 0
                   , reg_write_out: false
                   , mem_to_reg_out: false
                   , mem_write_out: false
                   , branch_out: false
                   , eq_comp_out: false
                   , alu_out_out: 0
                   , rd_2_out: 0
                   , rd_out: 0
                   , wd_out: 0
                   }
    }

    fn clock_high(self: &mut Self) {
        self.reg_write_out = self.reg_write_in;
        self.mem_to_reg_out = self.mem_to_reg_in;
        self.mem_write_out = self.mem_write_in;
        self.branch_out = self.branch_in;
        self.eq_comp_out = self.eq_comp_in;
        self.alu_out_out = self.alu_out_in;
        self.rd_2_out = self.rd_2_in;
        self.rd_out = self.rd_in;
        self.wd_out = self.wd_in;
    }
}

struct MWRegister {
    reg_write_in    : bool,
    mem_to_reg_in   : bool,
    alu_out_in      : u32,
    read_data_in    : u32,
    rd_in           : u32, 

    reg_write_out   : bool,
    mem_to_reg_out  : bool,
    alu_out_out     : u32,
    read_data_out   : u32,
    rd_out          : u32, 
}

impl MWRegister {
    fn new() -> MWRegister {
        MWRegister { reg_write_in: false
                   , mem_to_reg_in: false
                   , alu_out_in: 0
                   , read_data_in: 0
                   , rd_in: 0
                   , reg_write_out: false
                   , mem_to_reg_out: false
                   , alu_out_out: 0
                   , read_data_out: 0
                   , rd_out: 0
                   }
    }

    fn clock_high(self: &mut Self) {
        self.reg_write_out = self.reg_write_in;
        self.mem_to_reg_out = self.mem_to_reg_in;
        self.alu_out_out = self.alu_out_in;
        self.read_data_out = self.read_data_in;
        self.rd_out = self.rd_in;
    }
}

struct WFRegister {
    pc_in   : u32,

    pc_out  : u32,
}

impl WFRegister {
    fn new(base_address: u32) -> WFRegister {
        WFRegister {pc_in: base_address, pc_out: base_address}
    }

    fn clock_high(self: &mut Self) {
        self.pc_out = self.pc_in;
    }
}

// BEGIN HELPERS
fn alu_comp(alu_control: u32, alu_in_a: i32, alu_in_b: i32) -> Result<i32> {
    Ok(match alu_control {
        0b000 => alu_in_a + alu_in_b,
        0b001 => alu_in_a * alu_in_b,
        0b010 => if alu_in_a < alu_in_b {1} else {0},
        _ => return Err(Error::InvalidAluControl(alu_control)),
    })
}


fn mux2(control: u32, a_in: u32, b_in: u32) -> Result<u32> {
    Ok(match control {
        0 => a_in,
        1 => b_in,
        _ => return Err(Error::InvalidMux2Control(control)),
    })
}

fn immed_gen(op_code: OpCode, inA: u32, inB: u32) -> i32 {
    match op_code {
        OpCode::BEQ => {
            let reconstructed  = (inA << 20) | inB;
            let bit_12 = get_bits(31, 31, reconstructed);
            let bits_10_to_5 = get_bits(30, 25, reconstructed);
            let bits_4_to_1 = get_bits(11, 8, reconstructed);
            let bit_11 = get_bits(7, 7, reconstructed);
            
            let mut dest_word: u32 = 0;
            dest_word = splice_bits(12, 12, dest_word, bit_12);
            dest_word = splice_bits(10, 5, dest_word, bits_10_to_5);
            dest_word = splice_bits(4, 1, dest_word, bits_4_to_1);
            dest_word = splice_bits(11, 11, dest_word, bit_11);
            twos_complement(dest_word, 13)
        },
        OpCode::SW => {
            let reconstructed = (inA << 20) | inB;
            ((get_bits(31, 25, reconstructed) << 5) | get_bits(11, 7, reconstructed)) as i32
        },
        _ => {
            inA as i32
        },
    }
}
// END HELPERS

fn main() {
    println!("Hello, world!");
    let base_address: u32 = 0;
    let instruction_list = assembler::from_file("/home/alexj/rust/risc-v-emulator/test-files/program-8.rsv");
    let mut vm = Rv64Vm::from_instructions(instruction_list, base_address);
    vm.execute_program();
    println!("{}", vm.register_file);
}

