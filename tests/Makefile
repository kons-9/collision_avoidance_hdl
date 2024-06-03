
PROJECT_PATH:=$(abspath ../)

SRC_DIR:=$(PROJECT_PATH)/src
TB_DIR:=$(PROJECT_PATH)/tests
INCLUDE_DIR:=$(PROJECT_PATH)/include
BUILD_DIR=$(PROJECT_PATH)/build
TEST_DIR=$(BUILD_DIR)/tests
TB_INCLUDE_DIR=$(TB_DIR)/include

# BUILD_TOOL:=iverilog
# SIM_TOOL:=vvp
# BUILD_OPTION=-g2012 -I$(INCLUDE_DIR) -t$(SIM_TOOL)

UNIT_TEST_TB_FILENAMES:=utils/tb_calculate_checksum_comb.sv utils/tb_flit_queue.sv
UNIT_TEST_TB_FILES:=$(addprefix $(TB_DIR)/,$(UNIT_TEST_TB_FILENAMES))
UNIT_TEST_SRC_FILES:=$(addprefix $(SRC_DIR)/,$(subst tb_,,$(UNIT_TEST_TB_FILENAMES)))
UNIT_TEST_TARGETS:=$(subst .sv,,$(subst $(SRC_DIR)/,,$(UNIT_TEST_SRC_FILES)))

.PHONY: all prepare clean tb_calculate_checksum_comb tb_flit_queue
.SILENT: tb_calculate_checksum_comb tb_flit_queue all prepare start

all: prepare start tb_calculate_checksum_comb tb_flit_queue
	echo -n "\033[0;32m"
	echo "-------------All tests passed-------------"
	echo -n "\033[0m"

start: prepare
	echo -n "\033[0;32m"
	echo "-------------Start Tests-------------"
	echo -n "\033[0m"

prepare: $(TEST_DIR) xsim_test.sh
	chmod u+x xsim_test.sh

tb_calculate_checksum_comb: $(TEST_DIR)/tb_calculate_checksum_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Calculate Checksum Comb test passed\033[0m"

$(TEST_DIR)/tb_calculate_checksum_comb.log: $(SRC_DIR)/utils/calculate_checksum_comb.sv $(TB_DIR)/utils/tb_calculate_checksum_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_flit_queue: $(TEST_DIR)/tb_flit_queue.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Flit Queue test passed\033[0m"

$(TEST_DIR)/tb_flit_queue.log: $(TB_DIR)/utils/tb_flit_queue.sv $(SRC_DIR)/utils/flit_queue.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

$(TEST_DIR):
	mkdir -p $@

clean:
	rm -rf $(BUILD_DIR)/tests/*
