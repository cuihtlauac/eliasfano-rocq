// SDSL sd_vector (Elias-Fano) benchmark.
// Reads: values (one per line), "---", access indices, "---", nextGEQ values.
// Outputs TSV to stdout, oracle checks to stderr.

#include <sdsl/sd_vector.hpp>
#include <chrono>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

static const int WARMUP = 3;
static const int REPS = 15;
static const char* IMPL = "sdsl";

struct Stats {
    double median, min, p25, p75;
};

Stats compute_stats(std::vector<double>& samples) {
    std::sort(samples.begin(), samples.end());
    int n = samples.size();
    auto percentile = [&](double p) -> double {
        int k = static_cast<int>((n - 1) * p);
        return samples[k];
    };
    return { percentile(0.5), samples[0], percentile(0.25), percentile(0.75) };
}

void print_tsv(const char* impl, uint64_t n, const char* op, Stats s,
               double bits_per_elem = -1) {
    std::cout << impl << "\t" << n << "\t" << op << "\t"
              << static_cast<int64_t>(s.median) << "\t"
              << static_cast<int64_t>(s.min) << "\t"
              << static_cast<int64_t>(s.p25) << "\t"
              << static_cast<int64_t>(s.p75) << "\t";
    if (bits_per_elem >= 0)
        std::cout << bits_per_elem;
    std::cout << "\n";
}

using Clock = std::chrono::steady_clock;

template<typename F>
Stats bench(F f) {
    for (int i = 0; i < WARMUP; i++) f();
    std::vector<double> samples(REPS);
    for (int i = 0; i < REPS; i++) {
        auto t0 = Clock::now();
        f();
        auto t1 = Clock::now();
        samples[i] = std::chrono::duration<double, std::nano>(t1 - t0).count();
    }
    return compute_stats(samples);
}

std::vector<uint64_t> read_section() {
    std::vector<uint64_t> result;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line == "---") break;
        result.push_back(std::stoull(line));
    }
    return result;
}

int main() {
    std::ios_base::sync_with_stdio(false);
    std::cin.tie(nullptr);

    auto values = read_section();
    auto access_indices = read_section();
    auto nextgeq_values = read_section();

    uint64_t n = values.size();
    if (n == 0) {
        std::cerr << "empty input" << std::endl;
        return 1;
    }
    uint64_t universe = values.back() + 1;
    uint64_t nq = access_indices.size();

    // Encode: build bit_vector, set bits at value positions, then sd_vector
    sdsl::sd_vector<>* sdv = nullptr;
    sdsl::sd_vector<>::rank_1_type* rank_support = nullptr;
    sdsl::sd_vector<>::select_1_type* select_support = nullptr;

    auto encode_stats = bench([&]() {
        delete select_support; select_support = nullptr;
        delete rank_support; rank_support = nullptr;
        delete sdv; sdv = nullptr;
        sdsl::bit_vector bv(universe, 0);
        for (uint64_t i = 0; i < n; i++) {
            bv[values[i]] = 1;
        }
        sdv = new sdsl::sd_vector<>(bv);
        rank_support = new sdsl::sd_vector<>::rank_1_type(sdv);
        select_support = new sdsl::sd_vector<>::select_1_type(sdv);
    });
    double bits_per_elem = static_cast<double>(sdsl::size_in_bytes(*sdv) * 8) / n;
    print_tsv(IMPL, n, "encode", encode_stats, bits_per_elem);

    // Helper: access(i) = select_1(i+1) — SDSL select is 1-indexed
    auto access = [&](uint64_t i) -> uint64_t {
        return (*select_support)(i + 1);
    };

    // Helper: nextGEQ(v) = rank then select
    auto nextGEQ = [&](uint64_t v) -> uint64_t {
        uint64_t r = (*rank_support)(v);
        // rank_1(v) counts 1-bits in [0, v). We need >= v.
        // If bv[v] is set, rank_1(v) doesn't count it, so check:
        // We need the (r+1)-th 1-bit if it exists, but first check if
        // the r-th 1-bit (0-indexed) is >= v.
        // Actually: rank_1(v) = number of 1-bits in [0, v).
        // If bv[v]=1, the next 1-bit >= v is v itself, at rank r (0-indexed).
        // select_1(r+1) gives position of (r+1)-th 1-bit (1-indexed).
        // But we need to handle the case where bv[v]=1:
        //   rank_1(v) = count of 1s in [0,v), so select_1(rank_1(v)+1) = v.
        // If bv[v]=0:
        //   rank_1(v) = count of 1s in [0,v), select_1(rank_1(v)+1) = next 1-bit > v.
        // In both cases, select_1(rank_1(v)+1) gives the answer if rank_1(v) < n.
        // But rank_1(v) might equal rank_1(v+1) if bv[v]=0, and we need rank_1(v+1):
        // No — rank_1(v) counts [0,v). We want first 1-bit at position >= v.
        // That is select_1(rank_1(v) + 1) since rank_1(v) 1-bits are at positions < v.
        if (r >= n) return UINT64_MAX;
        return (*select_support)(r + 1);
    };

    // Oracle: decode
    bool decode_ok = true;
    for (uint64_t i = 0; i < n; i++) {
        if (access(i) != values[i]) { decode_ok = false; break; }
    }
    std::cerr << IMPL << " n=" << n << " ORACLE decode "
              << (decode_ok ? "OK" : "FAIL") << std::endl;

    // Oracle: access spot-check
    uint64_t num_checks = std::min(nq, (uint64_t)100);
    bool access_ok = true;
    for (uint64_t i = 0; i < num_checks; i++) {
        if (access(access_indices[i]) != values[access_indices[i]]) {
            access_ok = false; break;
        }
    }
    std::cerr << IMPL << " n=" << n << " ORACLE access "
              << (access_ok ? "OK" : "FAIL") << std::endl;

    // Oracle: nextGEQ spot-check
    bool geq_ok = true;
    for (uint64_t i = 0; i < num_checks; i++) {
        uint64_t v = nextgeq_values[i];
        uint64_t got = nextGEQ(v);
        uint64_t expected = UINT64_MAX;
        for (uint64_t j = 0; j < n; j++) {
            if (values[j] >= v) { expected = values[j]; break; }
        }
        if (got != expected) { geq_ok = false; break; }
    }
    std::cerr << IMPL << " n=" << n << " ORACLE nextGEQ "
              << (geq_ok ? "OK" : "FAIL") << std::endl;

    // Decode benchmark
    auto decode_stats = bench([&]() {
        uint64_t acc = 0;
        for (uint64_t i = 0; i < n; i++) {
            acc ^= access(i);
        }
        volatile uint64_t sink = acc;
        (void)sink;
    });
    print_tsv(IMPL, n, "decode", decode_stats);

    // Batched access
    auto access_bench_stats = bench([&]() {
        uint64_t acc = 0;
        for (uint64_t i = 0; i < nq; i++) {
            acc ^= access(access_indices[i]);
        }
        volatile uint64_t sink = acc;
        (void)sink;
    });
    Stats aq = { access_bench_stats.median / nq, access_bench_stats.min / nq,
                 access_bench_stats.p25 / nq, access_bench_stats.p75 / nq };
    print_tsv(IMPL, n, "access", aq);

    // Batched nextGEQ
    auto geq_bench_stats = bench([&]() {
        uint64_t acc = 0;
        for (uint64_t i = 0; i < nq; i++) {
            acc ^= nextGEQ(nextgeq_values[i]);
        }
        volatile uint64_t sink = acc;
        (void)sink;
    });
    Stats gq = { geq_bench_stats.median / nq, geq_bench_stats.min / nq,
                 geq_bench_stats.p25 / nq, geq_bench_stats.p75 / nq };
    print_tsv(IMPL, n, "nextGEQ", gq);

    delete select_support;
    delete rank_support;
    delete sdv;
    return 0;
}
