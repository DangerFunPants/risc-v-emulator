use std::fs;
extern crate nom;

use crate::helpers::{get_bits, splice_bits};

use std::fmt;
use std::collections::HashMap;
use std::convert::Into;

use nom::IResult;
use nom::bytes::complete::{take_while1, take, tag, tag_no_case, take_while};
use nom::character::complete::{space1, space0};
use nom::sequence::tuple;
use nom::branch::alt;
use nom::combinator::{map_res, opt};
use nom::error::{ErrorKind};
use std::str::FromStr;

#[derive(Debug)]
enum Instruction {
    AddI(Register, Register, i32),
    RType(Register, Register, Register, Operation),
    Lw(Register, Register, i32),
    Beq(Register, Register, Label),
    LabelLine(Label), 
    Halt,
}

impl fmt::Display for Instruction {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Instruction::AddI(r1, r2, i) => write!(f, "addi {} {} {}", r1, r2, i),
            Instruction::Lw(r1, r2, offset) => write!(f, "lw {} {} {}", r1, r2, offset),
            Instruction::Beq(r1, r2, label) => write!(f, "beq {} {} {}", r1, r2, label),
            Instruction::RType(r1, r2, r3, Operation::Add) => write!(f, "add {} {} {}", r1, r2, r3),
            Instruction::RType(r1, r2, r3, Operation::Slt) => write!(f, "slt {} {} {}", r1, r2, r3),
            Instruction::Halt => write!(f, "halt"),
            Instruction::LabelLine(label) => write!(f, "{}", label),
        };
        Ok(())
    }
}

impl Instruction {
    fn to_machine_code(self: &Self, offset: u32, label_dict: &HashMap<Label, u32>) -> u32 {
        match self {
            Instruction::AddI(Register(r1), Register(r2), immediate) => {
                let dest = splice_bits(31, 20, 0, *immediate as u32);
                let dest = splice_bits(19, 15, dest, *r2);
                let dest = splice_bits(14, 12, dest, 0);
                let dest = splice_bits(11, 7, dest, *r1);
                let dest = splice_bits(6, 0, dest, 0b0010011);
                dest
            },

            Instruction::Lw(Register(r1), Register(r2), offset) => {
                let dest = splice_bits(31, 20, 0, *offset as u32);
                let dest = splice_bits(19, 15, dest, *r2);
                let dest = splice_bits(14, 12, dest, 0b010);
                let dest = splice_bits(11, 7, dest, *r1);
                let dest = splice_bits(6, 0, dest, 0b0000011);
                dest
            },

            Instruction::Beq(Register(r1), Register(r2), label) => {
                let label_loc = match label_dict.get(label) {
                    Some(label_loc) => label_loc,
                    None => panic!("Tried to branch to unknown label"),
                };
                let branch_offset: u32 = (((*label_loc as i32) - (offset as i32)) * 4) as u32;
                let bit_31 = get_bits(12, 12, branch_offset as u32);
                let bits_30_to_25 = get_bits(10, 5, branch_offset);
                let bits_11_to_8 = get_bits(4, 1, branch_offset);
                let bit_7 = get_bits(11, 11, branch_offset);

                let dest = splice_bits(31, 31, 0, bit_31);
                let dest = splice_bits(30, 25, dest, bits_30_to_25);
                let dest = splice_bits(24, 20, dest, *r2);
                let dest = splice_bits(19, 15, dest, *r1);
                let dest = splice_bits(14, 12, dest, 0b000);
                let dest = splice_bits(11, 8, dest, bits_11_to_8);
                let dest = splice_bits(7, 7, dest, bit_7);
                let dest = splice_bits(6, 0, dest, 0b1100011);
                dest
            },

            Instruction::RType(Register(r1), Register(r2), Register(r3), operation) => {
                let op_indicator = match operation {
                    Operation::Add => 0b000,
                    Operation::Slt => 0b010,
                };
                let dest = splice_bits(31, 25, 0, 0);
                let dest = splice_bits(24, 20, dest, *r3);
                let dest = splice_bits(19, 15, dest, *r2);
                let dest = splice_bits(14, 12, dest, op_indicator);
                let dest = splice_bits(11, 7, dest, *r1);
                let dest = splice_bits(6, 0, dest, 0b0110011);
                dest
            },

            Instruction::Halt => 0,

            Instruction::LabelLine(_) => panic!("Don't try to genrate machine code for label"),
        }
    }
}

#[derive(Debug)]
enum Operation {
    Slt,
    Add,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Label(String);

impl fmt::Display for Label {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, ".{}", self.0);
        Ok(())
    }
}

#[derive(Debug)]
struct Register(u32); 

impl fmt::Display for Register {
    fn fmt(self: &Self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "x{}", self.0);
        Ok(())
    }
}

fn int32(input: &str) -> IResult<&str, i32> {
    let(input, minus) = opt(tag("-"))(input)?;
    let (input, mut digits) = map_res(take_while1(|c: char| c.is_digit(10)), i32::from_str)(input)?;
    if let Some(m) = minus {
        digits *= -1;
    } Ok((input, digits))
}

fn register(input: &str) -> IResult<&str, Register> {
    let (input, _) = tag_no_case("x")(input)?;
    let (input, reg_num) = take_while1(|c| (c as char).is_digit(10))(input)?;
    let (input, _) = take_while(|c| (c as char) == ',' || (c as char).is_whitespace())(input)?;
    Ok((input, Register(reg_num.parse().unwrap())))
}

fn whitespace(input: &str) -> IResult<&str, ()> {
    let (input, _) = take_while(|c| (c as char) == ',' || (c as char).is_whitespace())(input)?;
    Ok((input, ()))
}

fn register_with_offset(input: &str) -> IResult<&str, (Register, i32)> {
    let (input, offset) = int32(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, reg) = register(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = whitespace(input)?;
    Ok((input, (reg, offset)))
}

fn immediate_value(input: &str) -> IResult<&str, i32> {
    int32(input)
}

fn label(input: &str) -> IResult<&str, Label> {
    let (input, _) = tag(".")(input)?;
    let (input, label_str) = take_while1(|c: char| c.is_alphanumeric())(input)?;
    // let (input, _) = tag(":")(input)?;
    Ok((input, Label(String::from(label_str))))
}

fn instruction(input: &str) -> IResult<&str, Instruction> {
    let (input, instr_name) = take_while1(|c: char| c.is_alphabetic())(input)?;
    let (input, _) = space0(input)?;
    Ok(match instr_name {
        "addi" => {
            let (input, (r1, r2, immed)) = tuple((register, register, immediate_value))(input)?; 
            (input, Instruction::AddI(r1, r2, immed))
        },

        "slt" => {
            let (input, (r1, r2, r3)) = tuple((register, register, register))(input)?;
            (input, Instruction::RType(r1, r2, r3, Operation::Slt))
        },

        "lw" => {
            let (input, (r1, (r2, offset))) = tuple((register, register_with_offset))(input)?;
            (input, Instruction::Lw(r1, r2, offset))
        },

        "beq" => {
            let (input, (r1, r2, label)) = tuple((register, register, label))(input)?;
            (input, Instruction::Beq(r1, r2, label))
        },

        "add" => {
            let (input, (r1, r2, r3)) = tuple((register, register, register))(input)?;
            (input, Instruction::RType(r1, r2, r3, Operation::Add))
        },

        "nop" => {
            (input, Instruction::AddI(Register(0), Register(0), 0))
        },

        "halt" => {
            (input, Instruction::Halt)
        },

        _ => return Err(nom::Err::Error((input, ErrorKind::Tag))),
    })
}

fn label_line(input: &str) -> IResult<&str, Instruction> {
    let (input, label) = label(input)?;
    Ok((input, Instruction::LabelLine(label)))
}

fn program(input: &str) -> IResult<&str, Vec<Instruction>> {
    let instruction_or_label = alt((instruction, label_line));
    let mut input_out = "";
    let mut instructions = Vec::new();
    for line in input.lines() {
        let (input, instruction) = instruction_or_label(line)?;
        instructions.push(instruction);
        input_out = input;
    }

    Ok((input_out, instructions))
}

fn gen_machine_code(instructions: &Vec<Instruction>) -> Vec<u32> {
    fn mk_label_dict(instructions: &Vec<Instruction>) -> HashMap<Label, u32> {
        let mut label_dict: HashMap<Label, u32> = HashMap::new();
        let mut offset: u32 = 0;
        for instruction in instructions.iter() {
            if let Instruction::LabelLine(label) = instruction {
                label_dict.insert(label.clone(), offset);
            } else {
                offset += 1;
            }
        }
        label_dict
    }

    let label_dict = mk_label_dict(instructions);
    
    let mut machine_code: Vec<u32> = Vec::new();
    let mut offset: u32 = 0;
    for instruction in instructions.iter() {
        if let Instruction::LabelLine(_) = instruction {
        } else {
            machine_code.push(instruction.to_machine_code(offset, &label_dict));
            offset += 1;
        }
    }
    machine_code
}

pub fn from_file(file_path: &str) -> Vec<u32> {
    let file_text = fs::read_to_string(file_path).expect("Failed to read assembly file.");
    let instructions = program(&file_text).unwrap();
    gen_machine_code(&instructions.1)
}

mod nom_tests {
    use nom::combinator::opt;
    use nom::bytes::complete::{tag, take_while1};
    use nom::combinator::{map_res};
    use nom::IResult;
    use std::str::FromStr;

    use super::*;


    #[test]
    fn test_nom() {
        let instrs = ["add x1, x2, x3", "beq x14, x0, .L3", "slt x14, x11, x10", "lw x12, 5(x10)"];
        for instr in instrs.iter() {
            let res = instruction(instr).unwrap();
            println!("{}", res.1);
        }
    }
    
    #[test]
    fn test_instruction_parsing() {
        let instrs = from_file("/home/alexj/rust/risc-v-emulator/test-files/program-1.rsv");
        let halt = 0;
        let nop = 0x13;
        let instruction_list: Vec<u32>  = vec![ 0x0005_2603  // lw
                                              , 0x0045_0513  // addi x10, x10, 4
                                              , 0x0000_0013  // nop
                                              , 0x00c6_86b3  // add x13, x13, x12
                                              , 0x00a5_a733  // slt x14, x11, x10
                                              , 0x0000_0013  // nop
                                              , 0x0000_0013  // nop
                                              , 0xfe07_02e3  // beq x14, x0, .L3
                                              , 0x01c0_0e13  // addi x28, x0, 28
                                              , 0x01d0_0e93  // addi x29, x0, 29
                                              , 0x01e0_0f13  // addi x30, x0, 30
                                              , 0x01f0_0f93  // addi x31, x0 31
                                              , nop
                                              , nop
                                              , nop
                                              , nop
                                              , halt
                                              , nop
                                              , nop
                                              , nop
                                              , nop
                                              ];
        assert_eq!(instrs, instruction_list);
    }
}
