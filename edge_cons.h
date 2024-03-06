#ifndef __EDGE_CONS__
#define __EDGE_CONS__

#include <unordered_map>
#include <memory>

#include "formula/aalta_formula.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

typedef enum
{
    Unknown,
    Undetermined, // TODO: whether need to add?
    Realizable,
    Unrealizable
} Status;

using afX_state_pair = pair<aalta_formula *, ull>;
class XCons
{
public:
    Status curY_status = Status::Unknown;
    unordered_map<ull, aalta_formula*> state2afX_map_;
    unordered_map<ull, aalta_formula*> undecided_afX_state_pairs_;
    aalta_formula *fixed_swin_X_cons = aalta_formula::TRUE();
    aalta_formula *fixed_undecided_X_cons = aalta_formula::TRUE();

    bool exist_ewin(unordered_set<ull> &ewin);
    bool exist_ewin(ull ewin_state_id);
    void update_fixed_swin_X_cons(unordered_set<ull> &swin);
    void update_fixed_swin_X_cons(ull swin_state_id);
    void update_fixed_undecided_X_cons(unordered_set<ull> &undecided);
    void update_fixed_swin_X_cons_repeat_prefix(ull prefix_state_id);

    bool undecided_afX_search_done() { return state2afX_map_.empty(); }

    afX_state_pair *choose_afX();

    void print_map(unordered_map<ull, aalta_formula*> &state2afX_map);
    void print_all_map();

    ~XCons();

private:
};

using afY_Xcons_pair = pair<aalta_formula *, shared_ptr<XCons>>;
class EdgeCons
{
public:
    vector<afY_Xcons_pair> afY_Xcons_pairs_;
    vector<afY_Xcons_pair> afY_Xcons_pairs_undecided_;
    int undecided_visited_idx = 0;
    aalta_formula *fixed_Y_cons = aalta_formula::TRUE();
    aalta_formula *fixed_Y_imply_X_cons = aalta_formula::TRUE();
    Status state_status = Status::Unknown;

    void update_fixed_edge_cons(unordered_set<ull> &ewin, unordered_set<ull> &swin, unordered_set<ull> &undecided);
    // void update_fixed_edge_cons(aalta_formula* af_Y);
    void update_fixed_edge_cons_repeat_prefix(aalta_formula* af_Y, ull prefix_state_id);
    void update_fixed_edge_cons(aalta_formula* af_Y, ull next_state_id, Status next_status);
    // void update_fixed_edge_cons(aalta_formula* af_Y);
    // void update_fixed_edge_cons(ull ewin_state_id);
    aalta_formula *get_fixed_edge_cons();

    bool undecided_afY_search_done() { return undecided_visited_idx == afY_Xcons_pairs_undecided_.size(); }

    aalta_formula *choose_afY();
    afX_state_pair *choose_afX(aalta_formula *af_Y);

    void print_vector(vector<afY_Xcons_pair> &afY_Xcons_pairs_vec);
    void print_all_vec();

    ~EdgeCons();

private:
};

#endif