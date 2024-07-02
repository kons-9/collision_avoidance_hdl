# packet_controller/router/tb_system_flit_decoder_comb.sv
# packet_controller/router/tb_router.sv
ROUTER_TARGETS:=tb_router tb_system_flit_decoder_comb

depend_router:= $(wildcard $(SRC_DIR)/packet_controller/router/*.sv) $(wildcard $(SRC_DIR)/utils/*.sv)

tb_router: $(TEST_DIR)/tb_router.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* Router test passed\033[0m"

$(TEST_DIR)/tb_router.log: $(TB_DIR)/packet_controller/router/tb_router.sv $(depend_router)
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^

tb_system_flit_decoder_comb: $(TEST_DIR)/tb_system_flit_decoder_comb.log
	echo -n "\033[0;31m"
	cat $< | tail -n 1 | grep -q "Test Passed" || (cat $< && echo -n "\033[0m" && exit 1)
	echo "\033[0;32m* System Flit Decoder Comb test passed\033[0m"

$(TEST_DIR)/tb_system_flit_decoder_comb.log: $(TB_DIR)/packet_controller/router/tb_system_flit_decoder_comb.sv $(SRC_DIR)/packet_controller/router/system_flit_decoder_comb.sv
	./xsim_test.sh $(basename $(notdir $@)) $(SRC_DIR) $(TB_DIR) $(TEST_DIR) $(INCLUDE_DIR) $(TB_INCLUDE_DIR) $^
