// Sux Elias-Fano benchmark.
// Reads test data from stdin (values, then queries).
// Outputs results and timing.

#include <sux/bits/EliasFano.hpp>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

int main() {
    // Read values
    std::vector<uint64_t> values;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line == "---") break;
        values.push_back(std::stoull(line));
    }

    uint64_t n = values.size();
    if (n == 0) {
        std::cerr << "empty input" << std::endl;
        return 1;
    }
    uint64_t universe = values.back() + 1;

    // Encode
    auto t0 = std::chrono::high_resolution_clock::now();
    sux::bits::EliasFano<> ef(values, universe);
    auto t1 = std::chrono::high_resolution_clock::now();

    double encode_us = std::chrono::duration<double, std::micro>(t1 - t0).count();
    std::cout << "sux encode: " << encode_us << " us (" << n << " elements)" << std::endl;

    // Decode (access all elements)
    auto t2 = std::chrono::high_resolution_clock::now();
    for (uint64_t i = 0; i < n; i++) {
        volatile uint64_t v = ef.select(i);
        (void)v;
    }
    auto t3 = std::chrono::high_resolution_clock::now();

    double decode_us = std::chrono::duration<double, std::micro>(t3 - t2).count();
    std::cout << "sux decode_all: " << decode_us << " us" << std::endl;

    // Process queries
    while (std::getline(std::cin, line)) {
        if (line.substr(0, 7) == "access ") {
            uint64_t i = std::stoull(line.substr(7));
            auto ta = std::chrono::high_resolution_clock::now();
            uint64_t result = ef.select(i);
            auto tb = std::chrono::high_resolution_clock::now();
            double us = std::chrono::duration<double, std::micro>(tb - ta).count();
            std::cout << "sux access(" << i << ") = " << result
                      << " [" << us << " us]" << std::endl;
        } else if (line.substr(0, 8) == "nextGEQ ") {
            uint64_t v = std::stoull(line.substr(8));
            auto ta = std::chrono::high_resolution_clock::now();
            // nextGEQ(v) = select(rank(v))
            uint64_t idx = ef.rank(v);
            uint64_t result;
            if (idx < n) {
                result = ef.select(idx);
            } else {
                result = UINT64_MAX; // sentinel for "none"
            }
            auto tb = std::chrono::high_resolution_clock::now();
            double us = std::chrono::duration<double, std::micro>(tb - ta).count();
            if (result == UINT64_MAX) {
                std::cout << "sux nextGEQ(" << v << ") = None"
                          << " [" << us << " us]" << std::endl;
            } else {
                std::cout << "sux nextGEQ(" << v << ") = " << result
                          << " [" << us << " us]" << std::endl;
            }
        }
    }

    std::cout << "sux bitCount: " << ef.bitCount() << " bits" << std::endl;
    return 0;
}
