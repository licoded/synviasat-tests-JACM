#ifndef __EDGE_CONS_
#define __EDGE_CONS_

#include <unordered_map>

#include "formula/aalta_formula.h"
#include "synthesis.h"  // only for State enum

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

class XCons
{
public:
    unordered_map<ull, aalta_formula*> state2afX_map_;
    aalta_formula *fixed_swin_X_cons = aalta_formula::TRUE();
    aalta_formula *fixed_undetermined_X_cons = aalta_formula::TRUE();
    Status curY_status = Status::Unknown;

    bool exist_ewin(unordered_set<ull> &ewin);
    bool exist_ewin(ull swin_state_id);
    void update_fixed_swin_X_cons(unordered_set<ull> &swin);
    void update_fixed_swin_X_cons(ull swin_state_id);

    aalta_formula *choose_afX();

private:
};

using afY_Xcons_pair = pair<aalta_formula *, XCons*>;
class EdgeCons
{
public:
    vector<afY_Xcons_pair> afY_Xcons_pairs_;
    aalta_formula *fixed_Y_cons;
    aalta_formula *fixed_Y_imply_X_cons;
    Status state_status = Status::Unknown;

    void reinit_fixed_edge_cons(unordered_set<ull> &ewin, unordered_set<ull> &swin);
    void update_fixed_edge_cons(aalta_formula* af_Y, ull swin_state_id);
    void update_fixed_edge_cons(aalta_formula* af_Y);
    void update_fixed_edge_cons(ull ewin_state_id);
    aalta_formula *get_fixed_edge_cons();

    aalta_formula *choose_afY();
    aalta_formula *choose_afX(aalta_formula *af_Y);

private:
};

#endif