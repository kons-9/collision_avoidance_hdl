
PROJECT_PATH:=$(abspath ../)

SRC_DIR:=$(PROJECT_PATH)/src
TB_DIR:=$(PROJECT_PATH)/tests
INCLUDE_DIR:=$(PROJECT_PATH)/include
BUILD_DIR=$(PROJECT_PATH)/build
TEST_DIR=$(BUILD_DIR)/tests
TB_INCLUDE_DIR=$(TB_DIR)/include

TARGETS:=top all start prepare clean gen_test clean

top: all

include $(TB_DIR)/Makefile.inc
include $(TB_DIR)/utils/Makefile.inc
include $(TB_DIR)/packet_controller/Makefile.inc

all: prepare start $(UTILS_TARGETS) $(PACKET_CONTROLLER_TARGETS) $(NOC_TARGETS)
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

$(TEST_DIR):
	mkdir -p $@

clean:
	rm -rf $(BUILD_DIR)/tests/*

.PHONY: $(TARGETS) $(UTILS_TARGETS) $(PACKET_CONTROLLER_TARGETS) $(NOC_TARGETS)

.SILENT: $(TARGETS) $(UTILS_TARGETS) $(PACKET_CONTROLLER_TARGETS) $(NOC_TARGETS)
