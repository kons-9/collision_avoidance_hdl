use multiple_object_generater::Args;
use multiple_object_generater::NocConfig;
use serde_json::from_str;
use clap::Parser;

fn read_json_file(args: &Args) -> NocConfig {
    let json_file = std::fs::read_to_string(&args.json_file).unwrap();
    from_str(&json_file).unwrap()
}

fn main() {
    let args = Args::parse();
    let mut noc_config = read_json_file(&args);
    let system_verilog = noc_config.generate_system_verilog();
    std::fs::write(&args.output_file, system_verilog).unwrap();
}
