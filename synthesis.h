#ifndef __SYNTHESIS__
#define __SYNTHESIS__

#include <unordered_set>
#include <list>
#include <map>
#include <unordered_map>
#include <sys/time.h>

#include "formula_in_bdd.h"
#include "deps/CUDD-install/include/cudd.h"
#include "carchecker.h"

using namespace std;

typedef enum
{
    To_winning_state,
    To_failure_state,
    Accepting_edge,
    NoWay,
    // for Y, there is some X such that \delta(s,X\cup Y) has no successor
    Incomplete_Y
} Signal;

// main entry
bool is_realizable(aalta_formula *src_formula, unordered_set<string> &env_var, const struct timeval &prog_start, bool verbose = false);

class Syn_Frame
{
public:
    static int print_state_cnt;
    static unordered_map<int, string> print_states;
    static string get_print_id(int state_id);

    // number of variables
    static int num_varX_;
    static int num_varY_;

    // set of X- Y- variables
    static set<int> var_X;
    static set<int> var_Y;

    static void fill_in_edgeset(std::unordered_set<int> &partial_edgeset);

    // the bdd pointer of winning/failure state
    static unordered_set<ull> swin_state;
    static unordered_set<ull> ewin_state;
    static unordered_set<ull> undecided_state;

    static vector<DdNode *> swin_state_vec;
    static vector<DdNode *> ewin_state_vec;
    static vector<DdNode *> undecided_state_vec;

    static bool inSwinSet(DdNode *bddP);
    static bool inEwinSet(DdNode *bddP);

    static void insert_winning_state(DdNode *bddP, aalta_formula *afP);
    static void insert_winning_state(FormulaInBdd *state_in_bdd_);

    static void insert_failure_state(DdNode *bddP, aalta_formula *afP);
    static void insert_failure_state(Syn_Frame *syn_frame_);
    static void insert_failure_state(FormulaInBdd *state_in_bdd_);

    static void insert_undecided_state(DdNode *bddP, aalta_formula *afP);
    static void insert_undecided_state(Syn_Frame *syn_frame_);
    static void insert_undecided_state(FormulaInBdd *state_in_bdd_);

    Status checkStatus();
    Status curY_status = Status::Unknown;
    static bool inUndeterminedState(DdNode *bddP);
    static void setEwinState(Syn_Frame *syn_frame);
    static void setSwinState(Syn_Frame *syn_frame);

    bool KnownFailure(bool verbose = false);
    bool KnownWinning(bool verbose = false);

    // from bdd pointer to aalta_formula pointer
    // for blocking failure state
    static map<ull, ull> bddP_to_afP;

    static int sat_call_cnt;
    static long double average_sat_time;

    Syn_Frame(aalta_formula *);
    ~Syn_Frame() {
        delete edgeCons_;
        delete state_in_bdd_;
        // delete current_X_;
        // delete current_Y_;
        // delete X_constraint_;
        // delete Y_constraint_;
    }
    Status CheckRealizability(bool verbose = false);
    inline DdNode *GetBddPointer()
    {
        return state_in_bdd_->GetBddPointer();
    }
    inline aalta_formula *GetFormulaPointer()
    {
        return state_in_bdd_->GetFormulaPointer();
    }

    // whther the current frame is
    // the beginning of a sat trace
    inline bool IsTraceBeginning()
    {
        return is_trace_beginning_;
    }

    inline bool IsNotTryingY()
    {
        return current_Y_ == NULL;
    }

    // return the constraint on edge
    aalta_formula *GetEdgeConstraint();

    void SetTravelDirection(aalta_formula *Y, aalta_formula *X);
    inline void ResetTravelDirection()
    {
        current_Y_ = NULL;
        current_X_ = NULL;
    }

    inline void SetTraceBeginning() { is_trace_beginning_ = true; }

    void PrintInfo();

    static void setTimeLimit(int time_limit) { TIME_LIMIT_ = time_limit; }
    static int getTimeLimit() { return TIME_LIMIT_; }

    EdgeCons *edgeCons_;

    aalta_formula *current_Y_;
    aalta_formula *current_X_;
    ull current_next_stateid_;

    int swin_checked_idx_;
    int ewin_checked_idx_;
    int undecided_checked_idx_;

private:
    FormulaInBdd *state_in_bdd_;

    // constraint for Y variables
    // initialize by TRUE
    aalta_formula *Y_constraint_;

    // constraint for X variables
    // initialize by TRUE
    aalta_formula *X_constraint_;

    // whther the current frame is
    // the beginning of a sat trace
    bool is_trace_beginning_;

    static int TIME_LIMIT_;
};

aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge);

bool BaseWinningAtY(aalta_formula *end_state, unordered_set<int> &Y);

bool repeat_with_prefix(list<Syn_Frame *> &prefix, aalta_formula *dfa_state, bool verbose = false);

// partition atoms and save index values respectively
void PartitionAtoms(aalta_formula *af, unordered_set<string> &env_val);

// check the constraint for edge is unsat
// there is no temporal operator in the input formula
inline bool EdgeConstraintIsUnsat(aalta_formula *edge)
{
    edge = edge->add_tail();
    CARChecker checker(edge, false, false);
    return !(checker.check());
}

inline aalta_formula *global_not(aalta_formula *phi)
{
    aalta_formula *not_phi = aalta_formula(aalta_formula::Not, NULL, phi).nnf();
    return aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), not_phi).unique();
}

bool RepeatState(list<Syn_Frame *> &prefix, DdNode *state);

#endif