use clap::Parser;
use serde::{Deserialize, Serialize};

#[derive(Parser)]
pub struct Args {
    /// json file
    #[clap(short, long)]
    pub json_file: String,

    /// output file
    #[clap(short, long)]
    pub output_file: String,
}

#[derive(Serialize, Deserialize)]
pub struct NocConfig {
    number_of_instances: u32,
    number_of_events: u32,
    events: Vec<Event>,
}

#[derive(Serialize, Deserialize)]
pub struct Event {
    timer: u32,
    instances: Vec<Instance>,
}

#[derive(Serialize, Deserialize)]
pub struct Instance {
    instance_name: u32,
    neighbor: Vec<u32>,
}

impl NocConfig {
    fn sort_by_timer(&mut self) {
        self.events.sort_by(|a, b| a.timer.cmp(&b.timer));
    }
    pub fn generate_system_verilog(&mut self) -> String {
        self.sort_by_timer();

        let max_timer = self.events.last().unwrap().timer;

        let mut system_verilog = format!(
            "
module sample(
    input logic clk,
    input logic rst_n
);

    logic [7:0] timer;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            timer <= 0;
        end else if (timer < {max_timer}) begin
            timer <= timer + 1;
        end
    end"
        );
        for i in 0..self.number_of_instances {
            system_verilog.push_str(&format!(
                "

    logic nic{i}_rx, nic{i}_tx;
    nic nic{i}(
        .rx(nic{i}_rx),
        .tx(nic{i}_tx)
    );"
            ));
        }

        system_verilog.push_str(
            "
    always_comb begin",
        );
        for i in 0..self.number_of_instances {
            system_verilog.push_str(&format!(
                "
        nic{i}_tx = 0;"
            ));
        }
        system_verilog.push_str(
            "
        if (0) begin
            // dummy",
        );

        for event in &self.events {
            let timer = event.timer;
            system_verilog.push_str(&format!(
                "
        end else if (timer < {timer}) begin"
            ));
            for instance in &event.instances {
                let name = instance.instance_name;
                let mut tmp = format!("nic{name}_rx = nic{name}_tx");
                for neighbor in &instance.neighbor {
                    tmp += format!(" | nic{neighbor}_tx", neighbor = neighbor).as_str();
                }
                tmp += ";";
                system_verilog.push_str(&format!(
                    "
            {tmp}"
                ));
            }
        }

        system_verilog.push_str(
            "
        end else begin
        end
    end
endmodule",
        );
        system_verilog
    }
}
