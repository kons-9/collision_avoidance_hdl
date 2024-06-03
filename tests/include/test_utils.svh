`ifndef TEST_UTILS_SVH
`define TEST_UTILS_SVH

`define RED_COLOR $write("\033[31m");
`define GREEN_COLOR $write("\033[32m");
`define YELLOW_COLOR $write("\033[33m");
`define RESET_COLOR $write("\033[0m");

int __failed_count = 0;
int __number_of_test = 0;
string __test_log_path = "";
int __fd;

`define TEST_START(test_log_path) \
  __failed_count = 0; \
  __number_of_test = 0; \
  __test_log_path = test_log_path; \
  __fd = $fopen(__test_log_path, "w"); \
  `GREEN_COLOR \
  $display("Test Start: %0s", __test_log_path); \
  `RESET_COLOR \

`define TEST_EXPECTED(expected, actual, message, file = `__FILE__, line = `__LINE__) \
  __number_of_test++; \
  assert (expected == actual) else begin \
    __failed_count++; \
    `RED_COLOR \
    $display("Error: %s, actual = %0d, expected = %0d(file:%0s line:%0d)", message, actual, expected, file, line); \
    $fwrite(__fd, "Error: %s, actual = %0d, expected = %0d(file:%0s line:%0d)\n", message, actual, expected, file, line); \
    `RESET_COLOR \
  end

`define TEST_UNEXPECTED(unexpected, actual, message, file = __FILE__, line = __LINE__) \
  __number_of_test++; \
  assert (expected != actual) else begin \
    __failed_count++; \
    `RED_COLOR \
    $display("Error: %s, actual = %0d, unexpected = %0d(file:%0s line:%0d)", message, actual, unexpected, file, line); \
    $fwrite(__fd, "Error: %s, actual = %0d, unexpected = %0d(file:%0s line:%0d)\n", message, actual, unexpected, file, line); \
    `RESET_COLOR \
  end

`define TEST_RESULT \
  if (__failed_count > 0) begin \
    `RED_COLOR \
    $display("Test Failed: passed = %0d, failed = %0d", __number_of_test - __failed_count, __failed_count); \
    $fwrite(__fd, "Test Failed: passed = %0d, failed = %0d\n", __number_of_test - __failed_count, __failed_count); \
    `RESET_COLOR \
  end else begin \
    `GREEN_COLOR \
    $display("Test Passed"); \
    $fwrite(__fd, "Test Passed\n"); \
    `RESET_COLOR \
  end

`endif
