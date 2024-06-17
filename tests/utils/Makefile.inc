# utils/tb_calculate_checksum_comb.sv
# utils/tb_flit_queue.sv : queue.sv
# utils/tb_make_ack_comb.sv
# utils/tb_next_free_index_comb.sv

UTILS_TARGETS:=tb_calculate_checksum_comb tb_flit_queue tb_make_ack_comb tb_next_free_index_comb

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

tb_make_ack_comb: $(TEST_DIR)/tb_make_ack_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Make Ack Comb test passed\033[0m"

$(TEST_DIR)/tb_make_ack_comb.log: $(TB_DIR)/utils/tb_make_ack_comb.sv $(SRC_DIR)/utils/make_ack_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_next_free_index_comb: $(TEST_DIR)/tb_next_free_index_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Next Free Index Comb test passed\033[0m"

$(TEST_DIR)/tb_next_free_index_comb.log: $(TB_DIR)/utils/tb_next_free_index_comb.sv $(SRC_DIR)/utils/next_free_index_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

