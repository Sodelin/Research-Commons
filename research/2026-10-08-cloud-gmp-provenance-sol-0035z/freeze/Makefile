CXX ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -Werror -pedantic
BUILD_DIR ?= build

.PHONY: all clean
all: $(BUILD_DIR)/interval_probe

$(BUILD_DIR)/interval_probe: src/certified_forward_gmp.cpp src/interval_probe.cpp include/certified_forward_gmp.hpp
	mkdir -p $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -Iinclude src/certified_forward_gmp.cpp src/interval_probe.cpp -lgmpxx -lgmp -o $@

clean:
	rm -f $(BUILD_DIR)/interval_probe
