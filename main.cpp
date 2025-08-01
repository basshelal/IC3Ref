#include <iostream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger.h"
}

#include "IC3.h"
#include "Model.h"
#include "Core.hpp"

constexpr
const char *STD_IN_PATH = "/dev/stdin";

void
printUsage() {
    PRINT("Usage: ic3 [options] FILE\n"
        "Options:\n"
        "-v, --verbose          Verbose\n"
        "--stdin                Use stdin instead of FILE\n"
    );
}

void
printAigerFile(const aiger *aig) {
    REQUIRE(aig != nullptr, "aig was null");
    LOG("Aiger File:");
    LOG("Inputs:");
    std::stringstream ss;
    ss << "[";
    for (uint i = 0; i < aig->num_inputs; i++) {
        const aiger_symbol &input = aig->inputs[i];
        if (input.name != nullptr) {
            ss << input.name;
        } else {
            ss << input.lit;
        }
        if (i != aig->num_inputs - 1) {
            ss << ", ";
        }
    }
    ss << "]";
    LOG("%s", ss.str().c_str());

    LOG("Latches:");
    ss = std::stringstream();
    ss << "[";
    for (uint i = 0; i < aig->num_latches; i++) {
        const aiger_symbol &latch = aig->latches[i];
        if (latch.name != nullptr) {
            ss << latch.name;
        } else {
            ss << latch.lit;
        }
        if (i != aig->num_latches - 1) {
            ss << ", ";
        }
    }
    ss << "]";
    LOG("%s", ss.str().c_str());

    LOG("Outputs:");
    ss = std::stringstream();
    ss << "[";
    for (uint i = 0; i < aig->num_outputs; i++) {
        const aiger_symbol &output = aig->outputs[i];
        if (output.name != nullptr) {
            ss << output.name;
        } else {
            ss << output.lit;
        }
        if (i != aig->num_outputs - 1) {
            ss << ", ";
        }
    }
    ss << "]";
    LOG("%s", ss.str().c_str());

    LOG("AND Gates:");
    ss = std::stringstream();
    ss << "[";
    for (uint i = 0; i < aig->num_ands; i++) {
        const aiger_and &gate = aig->ands[i];
        ss << gate.lhs << " = " << gate.rhs0 << " & " << gate.rhs1;
        if (i != aig->num_ands - 1) {
            ss << ", ";
        }
    }
    ss << "]";
    LOG("%s", ss.str().c_str());
    LOG("");
}

int
main(int argc, char **argv) {
    // TODO add time information
    LOG("Starting ic3");
    unsigned int propertyIndex = 0;
    bool verbose = false;
    const char *filePath = nullptr;

    for (int i = 1; i < argc; ++i) {
        const auto arg = std::string(argv[i]);
        if (arg == "-h" || arg == "--help") {
            printUsage();
            exit(0);
        }

        if (arg == "-v" || arg == "--verbose") {
            verbose = true;
        } else if (arg == "--stdin") {
            filePath = STD_IN_PATH;
        } else {
            // TODO, make this an argument instead of this and document
            //  when we will verify for the B bad or O output in MILOAB
            // optional argument: set property index
            // propertyIndex = (unsigned) atoi(argv[i]);
            filePath = argv[i];
        }
    }
    if (filePath == nullptr) {
        PRINT_ERR("No file path was provided and flag --stdin was not used\n\n");
        printUsage();
        exit(1);
    }

    FILE *file;
    if (filePath == STD_IN_PATH) {
        file = stdin;
    } else {
        file = fopen(filePath, "r+");
    }
    REQUIRE(file != nullptr, "Failed to open file: %s, error: %s", filePath, ::strerror(errno));

    // read AIGER model
    ::aiger *aig = ::aiger_init();
    const char *msg = ::aiger_read_from_file(aig, file);
    REQUIRE(msg == nullptr, "Failed to read aiger file: %s", msg);

    printAigerFile(aig);

    // create the Model from the obtained aig
    Model *model = ::modelFromAiger(aig, propertyIndex);
    ::aiger_reset(aig);
    REQUIRE(model != nullptr, "Model was null");

    // model check it
    bool rv = IC3::check(*model, verbose);

    delete model;

    const int numberToPrint = !rv;
    // print 0/1 according to AIGER standard
    PRINT("%d", numberToPrint);
    return numberToPrint;
}
