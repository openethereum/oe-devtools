// Copyright 2020 Gnosis Ltd.
// SPDX-License-Identifier: Apache-2.0

use clap::{App, AppSettings, Arg, SubCommand};

mod evm_asm;

use anyhow::Result;
use evm_asm::EvmAssembler;
use rustc_hex::ToHex;

fn main() -> Result<()> {
    let matches = App::new("evmasmtool")
        .version("1.0")
        .subcommand(
            SubCommand::with_name("asm")
                .about("assemble code")
                .setting(AppSettings::ArgRequiredElseHelp)
                .arg(Arg::with_name("code")),
        )
        .get_matches();

    // You can see which subcommand was used
    match matches.subcommand() {
        ("asm", Some(args)) => {
            if let Some(code) = args.value_of("code") {
                let code = if code.starts_with("@") {
                    std::fs::read_to_string(&code[1..])?
                } else {
                    code.replace(';', "\n")
                };
                let code: String = EvmAssembler::asm(&code)?.to_hex();
                println!("{}", code);
            }
        }
        ("", None) => println!("No subcommand specified"),
        _ => unreachable!(),
    }

    Ok(())
}
