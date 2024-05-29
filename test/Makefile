TOOL:=iverilog -g2009
VIEW:=gtkwave

SYSTEM_SRC:=Makefile
SRC_DIR:=$(abspath ../src)
TB_DIR:=$(abspath .)

INCLUDE:=$(SRC_DIR)/types.svh

all: run_checksum_test

run_checksum_test: checksum_test
	./checksum_test

checksum_test: $(INCLUDE) $(SRC_DIR)/utils/calculate_checksum_comb.sv $(TB_DIR)/utils/tb_calculate_checksum_comb.sv 
	$(TOOL) -o $@ $^ -s tb_calculate_checksum_comb
