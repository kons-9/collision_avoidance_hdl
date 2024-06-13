# tb_noc.sv
# tb_receive_controller_comb.sv
# tb_tx_buffer_selecter_comb.sv

NOC_TARGETS:=tb_receive_controller_comb

# tb_noc.sv
tb_noc: $(TEST_DIR)/tb_noc.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* NoC test passed\033[0m"

$(TEST_DIR)/tb_noc.log: $(TB_DIR)/tb_noc.sv $(SRC_DIR)/noc.sv $(SRC_DIR)/packet_controller/packet_controller.sv $(SRC_DIR)/packet_controller/next_free_index_comb.sv $(SRC_DIR)/packet_controller/packet_buffer.sv $(SRC_DIR)/packet_controller/packet_transfer_buffer.sv $(SRC_DIR)/packet_controller/router.sv $(SRC_DIR)/utils/flit_queue.sv $(SRC_DIR)/utils/queue.sv $(SRC_DIR)/utils/calculate_checksum
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

# tb_receive_controller_comb.sv

tb_receive_controller_comb: $(TEST_DIR)/tb_receive_controller_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Receive Controller Comb test passed\033[0m"

$(TEST_DIR)/tb_receive_controller_comb.log: $(TB_DIR)/tb_receive_controller_comb.sv $(SRC_DIR)/receive_controller_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

# tb_tx_buffer_selecter_comb.sv

tb_tx_buffer_selecter_comb: $(TEST_DIR)/tb_tx_buffer_selecter_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Tx Buffer Selecter Comb test passed\033[0m"

$(TEST_DIR)/tb_tx_buffer_selecter_comb.log: $(TB_DIR)/tb_tx_buffer_selecter_comb.sv $(SRC_DIR)/tx_buffer_selecter_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^
