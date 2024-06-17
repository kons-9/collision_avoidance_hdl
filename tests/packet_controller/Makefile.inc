# packet_controller/tb_packet_buffer.sv
# packet_controller/tb_packet_transfer_buffer.sv
# packet_controller/tb_router.sv
# packet_controller/tb_packet_controller.sv : depends on all

PACKET_CONTROLLER_TARGETS:=tb_packet_buffer tb_packet_transfer_buffer tb_system_flit_comb

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

$(TEST_DIR)/tb_router.log: $(TB_DIR)/packet_controller/tb_router.sv $(SRC_DIR)/packet_controller/router.sv $(SRC_DIR)/packet_controller/packet_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv $(SRC_DIR)/utils/next_free_index_comb.sv $(SRC_DIR)/packet_controller/system_flit_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_packet_controller: $(TEST_DIR)/tb_packet_controller.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Packet Controller test passed\033[0m"

$(TEST_DIR)/tb_packet_controller.log: $(TB_DIR)/packet_controller/tb_packet_controller.sv $(SRC_DIR)/packet_controller/packet_controller.sv $(SRC_DIR)/utils/next_free_index_comb.sv $(SRC_DIR)/packet_controller/packet_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv $(SRC_DIR)/packet_controller/router.sv $(SRC_DIR)/packet_controller/system_flit_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_system_flit_comb: $(TEST_DIR)/tb_system_flit_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* System Flit Comb test passed\033[0m"

$(TEST_DIR)/tb_system_flit_comb.log: $(TB_DIR)/packet_controller/tb_system_flit_comb.sv $(SRC_DIR)/packet_controller/system_flit_comb.sv 
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^
