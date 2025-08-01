#ifndef HELPERS_HPP
#define HELPERS_HPP

#include "Solver.h"

// A row of the AIGER spec: lhs = rhs0 & rhs1
struct AigRow {
    Minisat::Lit lhs;
    Minisat::Lit rhs0;
    Minisat::Lit rhs1;

    AigRow(Minisat::Lit _lhs, Minisat::Lit _rhs0, Minisat::Lit _rhs1)
        : lhs(_lhs), rhs0(_rhs0), rhs1(_rhs1) {
    }
};

// A lightweight wrapper around Minisat::Var that includes a name
class Var {
private: // fields
    Minisat::Var _var; // corresponding Minisat::Var in *any* solver
    std::string _name;

private: // static fields
    inline static
    Minisat::Var globalVariableIndex_sf = 0; // aligned with solvers
public:
    explicit
    Var(std::string name)
        : _var(Var::globalVariableIndex_sf++),
          _name(std::move(name)) {
        LOG("Var: %d", this->_var);
    }

    [[nodiscard]]
    std::size_t
    index() const {
        return (std::size_t) this->_var;
    }

    [[nodiscard]]
    Minisat::Var
    var() const {
        return this->_var;
    }

    [[nodiscard]]
    Minisat::Lit
    lit(bool neg) const {
        return Minisat::mkLit(this->_var, neg);
    }

    [[nodiscard]]
    std::string
    name() const {
        return this->_name;
    }
};

class VarComp {
public:
    bool operator()(const Var &v1, const Var &v2) const {
        return v1.index() < v2.index();
    }
};

// A proof obligation
struct Obligation {
    std::size_t state; // Generalize this state...
    std::size_t level; // ... relative to this level
    std::size_t depth; // Length of CTI suffix to error

    Obligation(std::size_t state, std::size_t level, std::size_t depth)
        : state(state), level(level), depth(depth) {
    }
};

class ObligationComp {
public:
    bool
    operator()(const Obligation &o1, const Obligation &o2) const {
        if (o1.level < o2.level) {
            return true; // prefer lower levels (required)
        }
        if (o1.level > o2.level) {
            return false;
        }
        if (o1.depth < o2.depth) {
            return true; // prefer shallower (heuristic)
        }
        if (o1.depth > o2.depth) {
            return false;
        }
        if (o1.state < o2.state) {
            return true; // canonical final decider
        }
        return false;
    }
};

typedef std::set<Obligation, ObligationComp> PriorityQueue;

// The State structures are for tracking trees of (lifted) CTIs.
// Because States are created frequently, I want to avoid dynamic
// memory management; instead their (de)allocation is handled via
// a vector-based pool
struct State {
    std::size_t successor; // successor State
    std::vector<Minisat::Lit> latches;
    std::vector<Minisat::Lit> inputs;
    std::size_t index; // for pool
    bool used; // for pool
};

// A CubeSet is a set of ordered (by integer value) vectors of
// Minisat::Lits
class LitVecComp {
public:
    bool
    operator()(const std::vector<Minisat::Lit> &v1, const std::vector<Minisat::Lit> &v2) const {
        if (v1.size() < v2.size()) {
            return true;
        }
        if (v1.size() > v2.size()) {
            return false;
        }
        for (std::size_t i = 0; i < v1.size(); ++i) {
            if (v1[i] < v2[i]) {
                return true;
            }
            if (v2[i] < v1[i]) {
                return false;
            }
        }
        return false;
    }
};

typedef std::set<std::vector<Minisat::Lit>, LitVecComp> CubeSet;

// Structure and methods for imposing priorities on literals
// through ordering the dropping of literals in mic (drop leftmost
// literal first) and assumptions to Minisat.  The implemented
// ordering prefers to keep literals that appear frequently in
// addCube() calls
struct HeuristicLitOrder {
    std::vector<float> counts;
    std::size_t _mini;

    HeuristicLitOrder()
        : _mini(1 << 20) {
    }

    void
    count(const std::vector<Minisat::Lit> &cube) {
        assert(!cube.empty());
        // assumes cube is ordered
        auto size = (std::size_t) Minisat::toInt(Minisat::var(cube.back()));
        if (size >= this->counts.size()) {
            this->counts.resize(size + 1);
        }
        this->_mini = (std::size_t) Minisat::toInt(Minisat::var(cube[0]));
        for (const Minisat::Lit &lit: cube) {
            auto index = (std::size_t) Minisat::toInt(Minisat::var(lit));
            this->counts[index] += 1;
        }
    }

    void
    decay() {
        for (std::size_t i = this->_mini; i < this->counts.size(); ++i) {
            this->counts[i] *= 0.99;
        }
    }
};

struct SlimLitOrder {
    HeuristicLitOrder *heuristicLitOrder;

    bool
    operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const {
        // l1, l2 must be unprimed
        auto i2 = (std::size_t) Minisat::toInt(Minisat::var(l2));
        if (i2 >= this->heuristicLitOrder->counts.size()) {
            return false;
        }
        auto i1 = (std::size_t) Minisat::toInt(Minisat::var(l1));
        if (i1 >= this->heuristicLitOrder->counts.size()) {
            return true;
        }
        return (this->heuristicLitOrder->counts[i1] < this->heuristicLitOrder->counts[i2]);
    }
};

#endif //HELPERS_HPP
