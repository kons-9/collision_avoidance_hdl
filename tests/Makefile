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

.PHONY: all prepare clean

all: prepare tb_calculate_checksum_comb tb_flit_queue

prepare: $(BUILD_DIR) $(TEST_DIR)
	mkdir -p $(TEST_DIR)

tb_calculate_checksum_comb: $(SRC_DIR)/utils/calculate_checksum_comb.sv $(TB_DIR)/utils/tb_calculate_checksum_comb.sv
	./xsim_test.sh $@ $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^
	cat $(TEST_DIR)/$@.log | grep -q "Test Passed" || exit 1

tb_flit_queue: $(TB_DIR)/utils/tb_flit_queue.sv $(SRC_DIR)/utils/flit_queue.sv
	./xsim_test.sh $@ $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^
	cat $(TEST_DIR)/$@.log | grep -q "Test Passed" || exit 1

clean:
	rm -rf $(BUILD_DIR)/tests/*

