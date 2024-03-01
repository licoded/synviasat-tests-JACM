#ifndef __EDGE_CONS_
#define __EDGE_CONS_

#include <unordered_map>

#include "formula/aalta_formula.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

class XCons
{
public:
    unordered_map<ull, aalta_formula*> state2afX_map_;
    aalta_formula *fixed_X_cons;

    bool exist_ewin(unordered_set<ull> &ewin);
    bool exist_ewin(ull swin_state_id);
    void update_fixed_X_cons(unordered_set<ull> &swin);
    void update_fixed_X_cons(ull swin_state_id);

private:
};

using afY_Xcons_pair = pair<aalta_formula *, XCons*>;
class EdgeCons
{
public:
    vector<afY_Xcons_pair> afY_Xcons_pairs_;
    aalta_formula *fixed_Y_cons;
    aalta_formula *fixed_Y_imply_X_cons;

    void update_fixed_edge_cons(unordered_set<ull> &ewin, unordered_set<ull> &swin);
    void update_fixed_edge_cons(aalta_formula* af_Y, ull swin_state_id);
    void update_fixed_edge_cons(aalta_formula* af_Y);
    void update_fixed_edge_cons(ull ewin_state_id);
    aalta_formula *get_fixed_edge_cons();

private:
};

#endif