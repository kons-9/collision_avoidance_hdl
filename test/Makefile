BUILD_TOOL:=iverilog
SIM_TOOL:=vvp
VIEW:=gtkwave

PROJECT_PATH:=$(abspath ../)

SRC_DIR:=$(PROJECT_PATH)/src
TB_DIR:=$(PROJECT_PATH)/test
INCLUDE_DIR:=$(PROJECT_PATH)/include
BUILD_DIR=$(PROJECT_PATH)/build

BUILD_OPTION=-g2012 -I$(INCLUDE_DIR) -t$(SIM_TOOL)

all: prepare run_top_test run_checksum_test

prepare: $(BUILD_DIR)
	mkdir -p $(BUILD_DIR)

run_top_test: top_test
	$(SIM_TOOL) $(BUILD_DIR)/$^

top_test: $(TB_DIR)/tb_top.sv
	$(BUILD_TOOL) $(BUILD_OPTION) -o $(BUILD_DIR)/$@ $^ -s tb_top 

run_checksum_test: checksum_test
	$(SIM_TOOL) $(BUILD_DIR)/$^

checksum_test: $(SRC_DIR)/utils/calculate_checksum_comb.sv $(TB_DIR)/utils/tb_calculate_checksum_comb.sv
	$(BUILD_TOOL) $(BUILD_OPTION) -o $(BUILD_DIR)/$@ $^ -s tb_calculate_checksum_comb

run_buffer_test: buffer_test
	$(SIM_TOOL) $(BUILD_DIR)/$^

buffer_test: $(SRC_DIR)/utils/flit_queue.sv $(TB_DIR)/utils/tb_flit_queue.sv
	$(BUILD_TOOL) $(BUILD_OPTION) -o $(BUILD_DIR)/$@ $^ -s tb_flit_queue

clean:
	rm -rf $(BUILD_DIR)/*

.PHONY: all prepare run_top_test run_checksum_test clean
