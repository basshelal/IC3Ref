#include <iostream>

#include "Model.h"

#include "Core.hpp"
#include "SimpSolver.h"
#include "Vec.h"

Minisat::Var Var::gvi = 0;

const Var &
Model::primeVar(const Var &v, Minisat::SimpSolver *slv) {
    // var for false
    if (v.index() == 0) {
        return v;
    }
    // latch or PI
    if (v.index() < this->reps) {
        return this->vars[this->primes + v.index() - this->inputs];
    }
    // AND lit
    ASSERT(v.index() >= this->reps,
           "v.index(): %zu this->reps: %zu",
           v.index(), this->reps);
    ASSERT(v.index() < this->primes,
           "v.index(): %zu this->primes: %zu",
           v.index(), this->primes);
    // created previously?
    IndexMap::const_iterator i = this->primedAnds.find(v.index());
    std::size_t index;
    if (i == this->primedAnds.end()) {
        // no, so make sure the model hasn't been locked
        ASSERT(this->primesUnlocked, "");
        // create a primed version
        std::stringstream ss;
        ss << v.name() << "'";
        index = this->vars.size();
        this->vars.push_back(Var(ss.str()));
        if (slv != nullptr) {
            Minisat::Var newVar = slv->newVar();
            const Minisat::Var &backVar = this->vars.back().var();
            ASSERT(newVar == backVar, "newVar: %d backVar: %d",
                   newVar, backVar);
        }
        ASSERT(this->vars.back().index() == index,
               "this->vars.back().index(): %zu index: %zu", this->vars.back().index(), index);
        this->primedAnds.insert(IndexMap::value_type(v.index(), index));
    } else {
        index = i->second;
    }
    return this->vars[index];
}

void Model::loadTransitionRelation(Minisat::Solver &solver, bool primeConstraints) {
    LOG("Load transition relation into solver");
    if (!this->sslv) {
        // create a simplified CNF version of (this slice of) the TR
        this->sslv = new Minisat::SimpSolver();
        Minisat::SimpSolver &simpleSolver = *this->sslv;

        // introduce all variables to maintain alignment
        for (std::size_t i = 0; i < this->vars.size(); ++i) {
            Minisat::Var newVar = simpleSolver.newVar();
            ASSERT(newVar == this->vars[i].var(), "");
        }

        // freeze inputs, latches, and special nodes (and primed forms)
        // This is why we use a SimpleSolver, to "freeze" variables

        // Freeze inputs and primed inputs
        for (auto iter = this->beginInputs(); iter != this->endInputs(); ++iter) {
            const Var &input = *iter;
            simpleSolver.setFrozen(input.var(), true);
            simpleSolver.setFrozen(this->primeVar(input).var(), true);
        }

        // Freeze latches and primed latches
        for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
            const Var &latch = *iter;
            simpleSolver.setFrozen(latch.var(), true);
            simpleSolver.setFrozen(this->primeVar(latch).var(), true);
        }

        // Freeze safety property (output or bad) and its primed
        simpleSolver.setFrozen(this->varOfLit(this->error()).var(), true);
        simpleSolver.setFrozen(this->varOfLit(this->primedError()).var(), true);

        // Freeze constraints and primed constraints
        for (auto iter = this->constraints.begin(); iter != this->constraints.end(); ++iter) {
            const Var &constraint = this->varOfLit(*iter);
            simpleSolver.setFrozen(constraint.var(), true);
            simpleSolver.setFrozen(this->primeVar(constraint).var(), true);
        }

        // initialize with roots of required formulas
        LitSet require; // unprimed formulas
        for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
            require.insert(this->nextStateFn(*iter));
        }
        require.insert(this->_error);
        require.insert(this->constraints.begin(), this->constraints.end());

        LitSet prequire; // for primed formulas; always subset of require
        prequire.insert(this->_error);
        prequire.insert(this->constraints.begin(), this->constraints.end());

        // traverse AIG backward
        for (auto iter = this->aig.rbegin(); iter != this->aig.rend(); ++iter) {
            const AigRow &gate = *iter;
            // skip if this row is not required
            if (!require.contains(gate.lhs) && !require.contains(~gate.lhs)) {
                continue;
            }
            // encode into CNF
            LOG("Loading gate into solver: %s = %s & %s",
                this->stringOfLit(gate.lhs).c_str(),
                this->stringOfLit(gate.rhs0).c_str(),
                this->stringOfLit(gate.rhs1).c_str()
            );
            this->addClause2(simpleSolver, ~gate.lhs, gate.rhs0);
            this->addClause2(simpleSolver, ~gate.lhs, gate.rhs1);
            this->addClause3(simpleSolver, ~gate.rhs0, ~gate.rhs1, gate.lhs);

            // require arguments
            require.insert(gate.rhs0);
            require.insert(gate.rhs1);

            // primed: skip if not required
            if (!prequire.contains(gate.lhs) && !prequire.contains(~gate.lhs)) {
                continue;
            }

            // encode PRIMED form into CNF
            Minisat::Lit lhsPrime = this->primeLit(gate.lhs, this->sslv);
            Minisat::Lit rhs0Prime = this->primeLit(gate.rhs0, this->sslv);
            Minisat::Lit rhs1Prime = this->primeLit(gate.rhs1, this->sslv);
            LOG("Loading gate into solver: %s = %s & %s",
                this->stringOfLit(lhsPrime).c_str(),
                this->stringOfLit(rhs0Prime).c_str(),
                this->stringOfLit(rhs1Prime).c_str()
            );
            this->addClause2(simpleSolver, ~lhsPrime, rhs0Prime);
            this->addClause2(simpleSolver, ~lhsPrime, rhs1Prime);
            this->addClause3(simpleSolver, ~rhs0Prime, ~rhs1Prime, lhsPrime);

            // require arguments
            prequire.insert(gate.rhs0);
            prequire.insert(gate.rhs1);
        }

        // assert literal for true
        this->addClause1(simpleSolver, this->btrue());
        // assert ~error, constraints, and primed constraints
        this->addClause1(simpleSolver, ~this->_error);
        LOG("Adding constraints to solver");
        for (auto iter = this->constraints.begin(); iter != this->constraints.end(); ++iter) {
            simpleSolver.addClause(*iter);
            // TODO 22-Jul-2025 18:01 @basshelal : Primed constraints aren't here,
            //  is this a bug by Bradley?
        }
        LOG("Adding primed latches and latch next states to solver");
        // assert l' = f for each latch l
        for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
            const Var &latch = *iter;
            Minisat::Lit primedLatch = this->primeLit(latch.lit(false));
            Minisat::Lit latchNext = this->nextStateFn(latch);
            this->addClause2(simpleSolver, ~primedLatch, latchNext);
            this->addClause2(simpleSolver, ~latchNext, primedLatch);
        }
        // turn off elimination (I don't know why)
        simpleSolver.eliminate(true);
    }

    Minisat::SimpSolver &simpleSolver = *this->sslv;
    // load the clauses from the simplified context
    while (solver.nVars() < simpleSolver.nVars()) {
        solver.newVar();
    }
    for (auto iter = simpleSolver.clausesBegin(); iter != simpleSolver.clausesEnd(); ++iter) {
        const Minisat::Clause &clause = *iter;
        Minisat::vec<Minisat::Lit> literals;
        for (int i = 0; i < clause.size(); ++i) {
            const Minisat::Lit &lit = clause[i];
            literals.push(lit);
        }
        this->addClauseVec(solver, literals);
    }
    for (auto iter = simpleSolver.trailBegin(); iter != simpleSolver.trailEnd(); ++iter) {
        const Minisat::Lit &lit = *iter;
        this->addClause1(solver, lit);
    }

    if (primeConstraints) {
        for (const Minisat::Lit &lit: this->constraints) {
            this->addClause1(solver, this->primeLit(lit));
        }
    }
}

void
Model::loadInitialCondition(Minisat::Solver &solver) const {
    LOG("Load initial condition into solver");
    this->addClause1(solver, this->btrue());
    for (const Minisat::Lit &lit: this->init) {
        this->addClause1(solver, lit);
    }
    if (this->constraints.empty()) {
        return;
    }

    // impose invariant constraints on initial states (AIGER 1.9)
    LitSet require;
    require.insert(this->constraints.begin(), this->constraints.end());
    for (auto iter = this->aig.rbegin(); iter != this->aig.rend(); ++iter) {
        const AigRow &gate = *iter;
        // skip if this (*i) is not required
        if (!require.contains(gate.lhs) && !require.contains(~gate.lhs)) {
            continue;
        }
        // encode into CNF
        LOG("Loading gate into solver: %s = %s & %s",
            this->stringOfLit(gate.lhs).c_str(),
            this->stringOfLit(gate.rhs0).c_str(),
            this->stringOfLit(gate.rhs1).c_str()
        );
        this->addClause2(solver, ~gate.lhs, gate.rhs0);
        this->addClause2(solver, ~gate.lhs, gate.rhs1);
        this->addClause3(solver, ~gate.rhs0, ~gate.rhs1, gate.lhs);
        // require arguments
        require.insert(gate.rhs0);
        require.insert(gate.rhs1);
    }
    for (auto iter = this->constraints.begin(); iter != this->constraints.end(); ++iter) {
        const Minisat::Lit &lit = *iter;
        this->addClause1(solver, lit);
    }
}

// Creates a named variable.
Var
var(const aiger_symbol *syms, size_t i, const char prefix, bool prime = false) {
    const aiger_symbol &sym = syms[i];
    std::stringstream ss;
    if (sym.name) {
        ss << sym.name;
    } else {
        ss << prefix << i;
    }
    if (prime) {
        ss << "'";
    }
    return Var(ss.str());
}

Minisat::Lit
lit(const VarVec &vars, unsigned int l) {
    return vars[l >> 1].lit(aiger_sign(l));
}

Model *
modelFromAiger(aiger *aig, unsigned int propertyIndex) {
    VarVec vars(1, Var("false"));
    LitVec init, constraints, nextStateFns;

    // declare primary inputs and latches
    for (size_t i = 0; i < aig->num_inputs; ++i)
        vars.push_back(var(aig->inputs, i, 'i'));
    for (size_t i = 0; i < aig->num_latches; ++i)
        vars.push_back(var(aig->latches, i, 'l'));

    // the AND section
    AigVec aigv;
    for (size_t i = 0; i < aig->num_ands; ++i) {
        // 1. create a representative
        std::stringstream ss;
        ss << 'r' << i;
        vars.push_back(Var(ss.str()));
        const Var &rep = vars.back();
        // 2. obtain arguments of AND as lits
        Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
        Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
        // 3. add AIG row
        aigv.push_back(AigRow(rep.lit(false), l0, l1));
    }

    // acquire latches' initial states and next-state functions
    for (size_t i = 0; i < aig->num_latches; ++i) {
        const Var &latch = vars[1 + aig->num_inputs + i];
        // initial condition
        unsigned int r = aig->latches[i].reset;
        if (r < 2)
            init.push_back(latch.lit(r == 0));
        // next-state function
        nextStateFns.push_back(lit(vars, aig->latches[i].next));
    }

    // invariant constraints
    for (size_t i = 0; i < aig->num_constraints; ++i)
        constraints.push_back(lit(vars, aig->constraints[i].lit));

    // acquire error from given propertyIndex
    if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
        || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex)) {
        std::cout << "Bad property index specified." << std::endl;
        return 0;
    }
    Minisat::Lit err =
            aig->num_bad > 0
                ? lit(vars, aig->bad[propertyIndex].lit)
                : lit(vars, aig->outputs[propertyIndex].lit);

    size_t inputsOffset = 1;
    size_t latchesOffset = inputsOffset + aig->num_inputs;
    size_t andsOffset = latchesOffset + aig->num_latches;
    return new Model(vars,
                     inputsOffset, latchesOffset,
                     andsOffset,
                     init, constraints, nextStateFns, err, aigv);
}
