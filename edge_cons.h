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
    void update_fixed_X_cons(unordered_set<ull> &swin);

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
    aalta_formula *get_fixed_edge_cons();

private:
};

#endif