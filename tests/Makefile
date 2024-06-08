
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

UNIT_TEST_TB_FILENAMES:=utils/tb_calculate_checksum_comb.sv utils/tb_flit_queue.sv tb_receive_controller_comb.sv packet_controller/tb_next_free_index_comb.sv packet_controller/tb_packet_buffer.sv packet_controller/tb_packet_transfer_buffer.sv packet_controller/tb_router.sv packet_controller/tb_packet_controller.sv
UNIT_TEST_TB_FILES:=$(addprefix $(TB_DIR)/,$(UNIT_TEST_TB_FILENAMES))
UNIT_TEST_SRC_FILES:=$(addprefix $(SRC_DIR)/,$(subst tb_,,$(UNIT_TEST_TB_FILENAMES)))
UNIT_TEST_TARGETS:=$(subst .sv,,$(subst $(SRC_DIR)/,,$(UNIT_TEST_SRC_FILES)))

.PHONY: all prepare clean gen_test tb_calculate_checksum_comb tb_flit_queue tb_receive_controller_comb tb_next_free_index_comb tb_packet_buffer tb_packet_transfer_buffer tb_router tb_packet_controller
.SILENT: tb_calculate_checksum_comb tb_flit_queue all prepare start tb_receive_controller_comb tb_next_free_index_comb tb_packet_buffer tb_packet_transfer_buffer tb_router tb_packet_controller

all: prepare start tb_calculate_checksum_comb tb_flit_queue tb_receive_controller_comb tb_next_free_index_comb tb_packet_buffer tb_packet_transfer_buffer tb_router tb_packet_controller
	echo -n "\033[0;32m"
	echo "-------------All tests passed-------------"
	echo -n "\033[0m"

start: prepare
	echo -n "\033[0;32m"
	echo "-------------Start Tests-------------"
	echo -n "\033[0m"

prepare: $(TEST_DIR) xsim_test.sh
	chmod u+x xsim_test.sh

gen_test:
	echo "Generate test"
	./gen_test.sh

# utils/tb_calculate_checksum_comb.sv
# utils/tb_flit_queue.sv

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

$(TEST_DIR)/tb_flit_queue.log: $(TB_DIR)/utils/tb_flit_queue.sv $(SRC_DIR)/utils/flit_queue.sv $(SRC_DIR)/utils/queue.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

# tb_receive_controller_comb.sv

tb_receive_controller_comb: $(TEST_DIR)/tb_receive_controller_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Receive Controller Comb test passed\033[0m"

$(TEST_DIR)/tb_receive_controller_comb.log: $(TB_DIR)/tb_receive_controller_comb.sv $(SRC_DIR)/receive_controller_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

# packet_controller/tb_next_free_index_comb.sv
# packet_controller/tb_packet_buffer.sv
# packet_controller/tb_packet_transfer_buffer.sv
# packet_controller/tb_router.sv
# packet_controller/tb_packet_controller.sv

tb_next_free_index_comb: $(TEST_DIR)/tb_next_free_index_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Next Free Index Comb test passed\033[0m"

$(TEST_DIR)/tb_next_free_index_comb.log: $(TB_DIR)/packet_controller/tb_next_free_index_comb.sv $(SRC_DIR)/packet_controller/next_free_index_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_packet_buffer: $(TEST_DIR)/tb_packet_buffer.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Packet Buffer test passed\033[0m"

$(TEST_DIR)/tb_packet_buffer.log: $(TB_DIR)/packet_controller/tb_packet_buffer.sv $(SRC_DIR)/packet_controller/packet_buffer.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^


tb_packet_transfer_buffer: $(TEST_DIR)/tb_packet_transfer_buffer.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Packet Transfer Buffer test passed\033[0m"

$(TEST_DIR)/tb_packet_transfer_buffer.log: $(TB_DIR)/packet_controller/tb_packet_transfer_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_router: $(TEST_DIR)/tb_router.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Router test passed\033[0m"

$(TEST_DIR)/tb_router.log: $(TB_DIR)/packet_controller/tb_router.sv $(SRC_DIR)/packet_controller/router.sv $(SRC_DIR)/packet_controller/packet_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv $(SRC_DIR)/packet_controller/next_free_index_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_packet_controller: $(TEST_DIR)/tb_packet_controller.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Packet Controller test passed\033[0m"

$(TEST_DIR)/tb_packet_controller.log: $(TB_DIR)/packet_controller/tb_packet_controller.sv $(SRC_DIR)/packet_controller/packet_controller.sv $(SRC_DIR)/packet_controller/next_free_index_comb.sv $(SRC_DIR)/packet_controller/packet_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv $(SRC_DIR)/packet_controller/router.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

$(TEST_DIR):
	mkdir -p $@

clean:
	rm -rf $(BUILD_DIR)/tests/*
