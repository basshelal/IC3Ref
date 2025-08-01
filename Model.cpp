#include <iostream>

#include "Model.h"

#include "Core.hpp"
#include "SimpSolver.h"
#include "Vec.h"

// Creates a named variable
static
Var
var(const aiger_symbol &symbol, const char *prefix, std::size_t index) {
    std::stringstream ss;
    ss << symbol.lit;
    if (symbol.name != nullptr) {
        ss << "-" << symbol.name;
    } else {
        ss << "-" << prefix << index;
    }
    return Var(ss.str());
}

static
Minisat::Lit
lit(const std::vector<Var> &vars, unsigned int l) {
    return vars[l >> 1].lit(aiger_sign(l));
}

Model *
modelFromAiger(aiger *aig, unsigned int propertyIndex) {
    std::vector<Var> vars(1, Var("false"));
    std::vector<Minisat::Lit> init;
    std::vector<Minisat::Lit> constraints;
    std::vector<Minisat::Lit> nextStateFns;

    // declare primary inputs and latches
    for (std::size_t i = 0; i < aig->num_inputs; ++i) {
        const aiger_symbol &symbol = aig->inputs[i];
        vars.push_back(var(symbol, "input", i));
    }
    for (std::size_t i = 0; i < aig->num_latches; ++i) {
        const aiger_symbol &symbol = aig->latches[i];
        vars.push_back(var(symbol, "latch", i));
    }

    // the AND section
    std::vector<AigRow> andGates;
    for (std::size_t i = 0; i < aig->num_ands; ++i) {
        const aiger_and &andGate = aig->ands[i];
        // 1. create a representative
        std::stringstream ss;
        ss << andGate.lhs << "-gate" << i;

        vars.push_back(Var(ss.str()));
        const Var &rep = vars.back();
        // 2. obtain arguments of AND as lits
        Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
        Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
        // 3. add AIG row
        andGates.push_back(AigRow(rep.lit(false), l0, l1));
    }

    // acquire latches' initial states and next-state functions
    for (std::size_t i = 0; i < aig->num_latches; ++i) {
        const Var &latch = vars[1 + aig->num_inputs + i];
        // initial condition
        unsigned int r = aig->latches[i].reset;
        if (r < 2) {
            init.push_back(latch.lit(r == 0));
        }
        // next-state function
        nextStateFns.push_back(lit(vars, aig->latches[i].next));
    }

    // invariant constraints
    for (std::size_t i = 0; i < aig->num_constraints; ++i)
        constraints.push_back(lit(vars, aig->constraints[i].lit));

    // acquire error from given propertyIndex
    if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
        || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex)) {
        std::cout << "Bad property index specified." << std::endl;
        return nullptr;
    }
    Minisat::Lit err = aig->num_bad > 0
                           ? lit(vars, aig->bad[propertyIndex].lit)
                           : lit(vars, aig->outputs[propertyIndex].lit);

    std::size_t inputsOffset = 1;
    std::size_t latchesOffset = inputsOffset + aig->num_inputs;
    std::size_t andsOffset = latchesOffset + aig->num_latches;

    return new Model(vars,
                     inputsOffset, latchesOffset,
                     andsOffset,
                     init, constraints, nextStateFns, err, andGates);
}
