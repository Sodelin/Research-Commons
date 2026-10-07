CC = gcc
CXX = g++
CPPFLAGS = -Iinclude
CFLAGS = -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra -Wpedantic -Werror
OUT ?= build

.PHONY: all
all: $(OUT)/count_cpp $(OUT)/check_c_abi

$(OUT):
	mkdir -p $(OUT)

$(OUT)/count_gmp.o: src/count_gmp.c include/rc_count.h | $(OUT)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(OUT)/count_cpp: src/count_cli.cpp $(OUT)/count_gmp.o include/rc_count.h
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) src/count_cli.cpp $(OUT)/count_gmp.o -lgmp -o $@

$(OUT)/check_c_abi: check_c_abi.c $(OUT)/count_gmp.o include/rc_count.h
	$(CC) $(CPPFLAGS) $(CFLAGS) check_c_abi.c $(OUT)/count_gmp.o -Wl,--wrap=realloc -lgmp -o $@

