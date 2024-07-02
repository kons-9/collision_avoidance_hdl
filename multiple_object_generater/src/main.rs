use clap::Parser;
use multiple_object_generater::Args;
use multiple_object_generater::NocConfig;
use serde_json::from_str;

fn read_json_file(args: &Args) -> NocConfig {
    let json_file = std::fs::read_to_string(&args.json_file).unwrap();
    from_str(&json_file).unwrap()
}

fn main() {
    let args = Args::parse();
    let mut noc_config = read_json_file(&args);
    let verilog = if args.module_name.is_none() {
        let module_name = args.output_file.split('.').next().unwrap();
        let module_name = module_name.split('/').last().unwrap();
        noc_config.generate_system_verilog(module_name)
    } else {
        noc_config.generate_system_verilog(&args.module_name.unwrap())
    };
    std::fs::write(&args.output_file, verilog).unwrap();
}
