#include <list>
#include <cassert>
#include <map>
#include <unordered_map>
#include <sys/time.h>

#include "synthesis.h"
#include "dfs_search.h"
#include "carchecker.h"

using namespace std;
using namespace aalta;

int Syn_Frame::print_state_cnt = 0;
int Syn_Frame::TIME_LIMIT_ = 5;
unordered_map<int, string> Syn_Frame::print_states;
string Syn_Frame::get_print_id(int state_id)
{
    print_states.insert({state_id, "state"+to_string(print_states.size()+1)});
    return print_states.at(state_id);
}
// static public variable of Syn_Frame
int Syn_Frame::num_varX_;
int Syn_Frame::num_varY_;
set<int> Syn_Frame::var_X;
set<int> Syn_Frame::var_Y;
unordered_set<ull> Syn_Frame::swin_state;
unordered_set<ull> Syn_Frame::ewin_state;
unordered_set<ull> Syn_Frame::undecided_state;
vector<DdNode *> Syn_Frame::swin_state_vec;
vector<DdNode *> Syn_Frame::ewin_state_vec;
vector<DdNode *> Syn_Frame::undecided_state_vec;
map<ull, ull> Syn_Frame::bddP_to_afP;
int Syn_Frame::sat_call_cnt;
long double Syn_Frame::average_sat_time;

void Syn_Frame::insert_winning_state(DdNode *bddP)
{
    if (Syn_Frame::swin_state.find(ull(bddP)) != Syn_Frame::swin_state.end())
        return;
    Syn_Frame::swin_state.insert(ull(bddP));
    Syn_Frame::swin_state_vec.push_back(bddP);
}

void Syn_Frame::insert_winning_state(FormulaInBdd *state_in_bdd_)
{
    Syn_Frame::insert_winning_state(state_in_bdd_->GetBddPointer());
}

void Syn_Frame::insert_failure_state(DdNode *bddP, aalta_formula *afP)
{
    if (Syn_Frame::ewin_state.find(ull(bddP)) != Syn_Frame::ewin_state.end())
        return;
    Syn_Frame::ewin_state.insert(ull(bddP));
    Syn_Frame::bddP_to_afP[ull(bddP)] = ull(afP);
    Syn_Frame::ewin_state_vec.push_back(bddP);
}

void Syn_Frame::insert_failure_state(Syn_Frame *syn_frame_)
{
    Syn_Frame::insert_failure_state(syn_frame_->GetBddPointer(), syn_frame_->GetFormulaPointer());
}

void Syn_Frame::insert_failure_state(FormulaInBdd *state_in_bdd_)
{
    Syn_Frame::insert_failure_state(state_in_bdd_->GetBddPointer(), state_in_bdd_->GetFormulaPointer());
}

void Syn_Frame::insert_undecided_state(DdNode *bddP, aalta_formula *afP)
{
    if (Syn_Frame::undecided_state.find(ull(bddP)) != Syn_Frame::undecided_state.end())
        return;
    Syn_Frame::undecided_state.insert(ull(bddP));
    Syn_Frame::bddP_to_afP[ull(bddP)] = ull(afP);
    Syn_Frame::undecided_state_vec.push_back(bddP);
}

void Syn_Frame::insert_undecided_state(Syn_Frame *syn_frame_)
{
    Syn_Frame::insert_undecided_state(syn_frame_->GetBddPointer(), syn_frame_->GetFormulaPointer());
}

void Syn_Frame::insert_undecided_state(FormulaInBdd *state_in_bdd_)
{
    Syn_Frame::insert_undecided_state(state_in_bdd_->GetBddPointer(), state_in_bdd_->GetFormulaPointer());
}

bool Syn_Frame::inSwinSet(DdNode *bddP)
{
    return swin_state.find((ull) bddP) != swin_state.end();
}

bool Syn_Frame::inEwinSet(DdNode *bddP)
{
    return ewin_state.find((ull) bddP) != ewin_state.end();
}

bool Syn_Frame::inUndeterminedState(DdNode *bddP)
{
    return !inEwinSet(bddP) && !inSwinSet(bddP);
}

void Syn_Frame::setEwinState(Syn_Frame *syn_frame)
{
    insert_failure_state(syn_frame->state_in_bdd_);
}

void Syn_Frame::setSwinState(Syn_Frame *syn_frame)
{
    insert_winning_state(syn_frame->state_in_bdd_);
}

bool is_realizable(aalta_formula *src_formula, unordered_set<string> &env_var, const struct timeval &prog_start, bool verbose)
{
    //   partition atoms and save index values respectively
    PartitionAtoms(src_formula, env_var);
    if (verbose)
    {
        cout << "initial state: " << src_formula->to_string() << endl;
        cout << "Y variables:";
        for (auto item : Syn_Frame::var_Y)
            cout << ' ' << aalta_formula(item, NULL, NULL).to_string();
        cout << "\nX variables:";
        for (auto item : Syn_Frame::var_X)
            cout << ' ' << aalta_formula(item, NULL, NULL).to_string();
        cout << endl;
    }

    Syn_Frame::sat_call_cnt = 0;
    Syn_Frame::average_sat_time = 0;

    // number of variables
    Syn_Frame::num_varX_ = Syn_Frame::var_X.size();
    Syn_Frame::num_varY_ = Syn_Frame::var_Y.size();

    // initializa utils of bdd
    FormulaInBdd::InitBdd4LTLf(src_formula, false);
    FormulaInBdd::fixXYOrder(Syn_Frame::var_X, Syn_Frame::var_Y);
    Syn_Frame::insert_winning_state(FormulaInBdd::TRUE_bddP_);
    Syn_Frame::insert_failure_state(FormulaInBdd::FALSE_bddP_, aalta_formula::FALSE());

    Syn_Frame *init = new Syn_Frame(src_formula); // xnf(src_formula)
    
    TarjanSearch::tarjan_search_init();
    return forwardSearch(init);
}

Syn_Frame::Syn_Frame(aalta_formula *af)
{
    state_in_bdd_ = new FormulaInBdd(af);
    edgeCons_ = FormulaInBdd::get_EdgeCons(state_in_bdd_->GetBddPointer());
    swin_checked_idx_ = 0;
    ewin_checked_idx_ = 0;
    undecided_checked_idx_ = 0;
    Y_constraint_ = aalta_formula::TRUE();
    X_constraint_ = aalta_formula::TRUE();
    current_Y_ = NULL;
    current_X_ = NULL;
    is_trace_beginning_ = false;
}

Status Syn_Frame::checkStatus()
{
    // TODO-DONE: deal with TRUE/FALSE
    if (state_in_bdd_->GetBddPointer() == FormulaInBdd::TRUE_bddP_)
        return Status::Realizable;
    if (state_in_bdd_->GetBddPointer() == FormulaInBdd::FALSE_bddP_)
        return Status::Unrealizable;

    if (edgeCons_->state_status == Status::Realizable || edgeCons_->state_status == Status::Unrealizable)
        return edgeCons_->state_status;
    if (swin_state.find(ull(state_in_bdd_->GetBddPointer())) != swin_state.end())
    {
        return edgeCons_->state_status = Status::Realizable;
    }
    else if (ewin_state.find(ull(state_in_bdd_->GetBddPointer())) != ewin_state.end())
    {
        return edgeCons_->state_status = Status::Unrealizable;
    }
    else if (undecided_state.find(ull(state_in_bdd_->GetBddPointer())) != undecided_state.end())
    {
        // cannot return because Undetermined may not finish search!!!
        // edgeCons_->state_status = Status::Undetermined;

        // but I have adjust logic in forwardSearch func to make sure it have been searched done!!!
        return edgeCons_->state_status = Status::Undetermined;
    }

    // NOTE: don't need to check whether cur_state in ewin/swin, that's impossible!

    // === collect swin and ewin states, then execute update_fixed_edge_cons
    unordered_set<ull> swin, ewin, undecided;
    for (; swin_checked_idx_ < Syn_Frame::swin_state_vec.size(); swin_checked_idx_++)
        swin.insert(ull(Syn_Frame::swin_state_vec[swin_checked_idx_]));
    for (; ewin_checked_idx_ < Syn_Frame::ewin_state_vec.size(); ewin_checked_idx_++)
        ewin.insert(ull(Syn_Frame::ewin_state_vec[ewin_checked_idx_]));
    for (; undecided_checked_idx_ < Syn_Frame::undecided_state_vec.size(); undecided_checked_idx_++)
        if (inUndeterminedState(Syn_Frame::undecided_state_vec[undecided_checked_idx_]))
            undecided.insert(ull(Syn_Frame::undecided_state_vec[undecided_checked_idx_]));
    edgeCons_->update_fixed_edge_cons(ewin, swin, undecided);

    // TODO-DONE: insert cur_state to swin/ewin/undecided states, if not Unknown
    switch(edgeCons_->state_status)
    {
        case Status::Realizable:
            Syn_Frame::insert_winning_state(state_in_bdd_);
            break;
        case Status::Unrealizable:
            Syn_Frame::insert_failure_state(state_in_bdd_);
            break;
        case Status::Undetermined:
            Syn_Frame::insert_undecided_state(state_in_bdd_);
            break;
        default:
            break;
    }

    return edgeCons_->state_status;
}

aalta_formula *Syn_Frame::GetEdgeConstraint()
{
    if (current_Y_ == NULL)
        return Y_constraint_;
    else
        return aalta_formula(aalta_formula::And, current_Y_, X_constraint_).unique();
}

void Syn_Frame::PrintInfo()
{
    cout << "state formula: " << (state_in_bdd_->GetFormulaPointer())->to_string() << endl;
    cout << "Y constraint: " << Y_constraint_->to_string() << endl;
    cout << "X constraint: " << X_constraint_->to_string() << endl;
    if (current_Y_ != NULL)
        cout << "current Y: " << current_Y_->to_literal_set_string() << endl;
    if (current_X_ != NULL)
        cout << "current X: " << current_X_->to_literal_set_string() << endl;
    cout << (is_trace_beginning_ ? "is " : "is not ") << "a starting point" << endl;
}

void Syn_Frame::SetTravelDirection(aalta_formula *Y, aalta_formula *X)
{
    if (current_Y_ == NULL)
        current_Y_ = Y;
    current_X_ = X;
}

aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge)
{
    if (predecessor == NULL)
        return NULL;
    int op = predecessor->oper();
    if (op == aalta_formula::True || op == aalta_formula::False)
        return predecessor;
    else if (op == aalta_formula::And)
    {
        aalta_formula *lf = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *rf = FormulaProgression(predecessor->r_af(), edge);
        if ((lf->oper()) == aalta_formula::False || (rf->oper()) == aalta_formula::False)
            return aalta_formula::FALSE();
        else if ((lf->oper()) == aalta_formula::True)
            return rf;
        else if ((rf->oper()) == aalta_formula::True)
            return lf;
        else
            return aalta_formula(aalta_formula::And, lf, rf).unique();
    }
    else if (op == aalta_formula::Or)
    {
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *r_fp = FormulaProgression(predecessor->r_af(), edge);
        if ((l_fp->oper()) == aalta_formula::True || (r_fp->oper()) == aalta_formula::True)
            return aalta_formula::TRUE();
        else if ((l_fp->oper()) == aalta_formula::False)
            return r_fp;
        else if ((r_fp->oper()) == aalta_formula::False)
            return l_fp;
        else
            return aalta_formula(aalta_formula::Or, l_fp, r_fp).unique();
    }
    else if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((predecessor->r_af())->oper()));
        if (edge.find(lit) != edge.end())
            return aalta_formula::TRUE();
        else
            return aalta_formula::FALSE();
    }
    else if (op == aalta_formula::Next || op == aalta_formula::WNext)
    {
        return predecessor->r_af();
    }
    // if predecessor is in XNF,
    // the following two cases cannot appear
    else if (op == aalta_formula::Until)
    { // l U r = r | (l & X(l U r))
        aalta_formula *first_part = FormulaProgression(predecessor->r_af(), edge);
        if ((first_part->oper()) == aalta_formula::True)
            return aalta_formula::TRUE();
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *second_part = NULL;
        if ((l_fp->oper()) == aalta_formula::True)
        {
            if (first_part == predecessor->r_af())
                return predecessor;
            second_part = predecessor;
        }
        else if ((l_fp->oper()) == aalta_formula::False)
            return first_part;
        else
            second_part = aalta_formula(aalta_formula::And, l_fp, predecessor).unique();
        if ((first_part->oper()) == aalta_formula::False)
            return second_part;
        else
            return aalta_formula(aalta_formula::Or, first_part, second_part).unique();
    }
    else if (op == aalta_formula::Release)
    { // l R r = r & (l | N(l R r))
        aalta_formula *first_part = FormulaProgression(predecessor->r_af(), edge);
        if ((first_part->oper()) == aalta_formula::False)
            return aalta_formula::FALSE();
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *second_part = NULL;
        if ((l_fp->oper()) == aalta_formula::True)
            return first_part;
        else if ((l_fp->oper()) == aalta_formula::False)
            second_part = predecessor;
        else
            second_part = aalta_formula(aalta_formula::Or, l_fp, predecessor).unique();
        if ((first_part->oper()) == aalta_formula::True)
            return second_part;
        else
            return aalta_formula(aalta_formula::And, first_part, second_part).unique();
    }
}

bool BaseWinningAtY(aalta_formula *end_state, unordered_set<int> &Y)
{
    if (end_state == NULL)
        return false;
    int op = end_state->oper();
    if (op == aalta_formula::True || op == aalta_formula::WNext)
        return true;
    else if (op == aalta_formula::False || op == aalta_formula::Next)
        return false;
    else if (op == aalta_formula::And)
        return BaseWinningAtY(end_state->l_af(), Y) && BaseWinningAtY(end_state->r_af(), Y);
    else if (op == aalta_formula::Or)
        return BaseWinningAtY(end_state->l_af(), Y) || BaseWinningAtY(end_state->r_af(), Y);
    else if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((end_state->r_af())->oper()));
        return Y.find(lit) != Y.end();
    }
    else if (op == aalta_formula::Until || op == aalta_formula::Release)
        return BaseWinningAtY(end_state->r_af(), Y);
}

bool repeat_with_prefix(list<Syn_Frame *> &prefix, aalta_formula *dfa_state, bool verbose)
{
    FormulaInBdd *state_in_bdd_ = new FormulaInBdd(dfa_state);
    // block prefix
    for (auto it = prefix.begin(); it != prefix.end(); it++)
    {
        // A|B -> A|B|C, A&B&C -> A&B
        if (ull(state_in_bdd_->GetBddPointer()) == ull((*it)->GetBddPointer()))
        {
            if (verbose)
            {
                aalta_formula *af = (*it)->GetFormulaPointer();
                cout 
                    << "repeat with prefix -- find in prefix by equal -- " 
                    << "\t found state id: " << Syn_Frame::get_print_id(af->id()) << endl
                    << "\t current state: " << state_in_bdd_->GetFormulaPointer()->to_string() << endl;
            }
            return true;
        }
    }
    return false;
}

// partition atoms and save index values respectively
void PartitionAtoms(aalta_formula *af, unordered_set<string> &env_val)
{
    if (af == NULL)
        return;
    int op = af->oper();
    if (op >= 11)
        if (env_val.find(af->to_string()) != env_val.end())
            Syn_Frame::var_X.insert(op);
        else
            Syn_Frame::var_Y.insert(op);
    else
    {
        PartitionAtoms(af->l_af(), env_val);
        PartitionAtoms(af->r_af(), env_val);
    }
}

bool IsAcc(aalta_formula *predecessor, unordered_set<int> &tmp_edge)
{
    if (predecessor == NULL)
        return false;
    int op = predecessor->oper();
    if (op == aalta_formula::True || op == aalta_formula::WNext)
        return true;
    else if (op == aalta_formula::False || op == aalta_formula::Next)
        return false;
    else if (op == aalta_formula::And)
        return BaseWinningAtY(predecessor->l_af(), tmp_edge) && BaseWinningAtY(predecessor->r_af(), tmp_edge);
    else if (op == aalta_formula::Or)
        return BaseWinningAtY(predecessor->l_af(), tmp_edge) || BaseWinningAtY(predecessor->r_af(), tmp_edge);
    else if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((predecessor->r_af())->oper()));
        return tmp_edge.find(lit) != tmp_edge.end();
    }
    else if (op == aalta_formula::Until || op == aalta_formula::Release)
        return BaseWinningAtY(predecessor->r_af(), tmp_edge);
}

bool RepeatState(list<Syn_Frame *> &prefix, DdNode *state)
{
    for (auto it = prefix.begin(); it != prefix.end(); ++it)
        if (state == ((*it)->GetBddPointer()))
            return true;
    return false;
}