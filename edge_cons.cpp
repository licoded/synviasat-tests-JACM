#include <iostream>
#include <cassert>

#include "edge_cons.h"
#include "formula_in_bdd.h"
#include "formula/aalta_formula.h"

bool XCons::exist_ewin(unordered_set<int> &ewin)
{
    for (auto afX_state_pair_ : afX_state_pairs_)
    {
        int state_id = afX_state_pair_.second;

        if (ewin.find(state_id) != ewin.end())
            return true;
    }

    return false;
}

void XCons::update_fixed_X_cons(unordered_set<int> &swin)
{
    for (auto afX_state_pair_ : afX_state_pairs_)
    {
        aalta_formula *afX = afX_state_pair_.first;
        int state_id = afX_state_pair_.second;

        if (swin.find(state_id) != swin.end())
        {
            aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
            fixed_X_cons = aalta_formula(aalta_formula::And, fixed_X_cons, not_afX).unique();
            // TODO: delete curItem (afX_state_pair_) from afX_state_pairs_
        }
    }
}

void EdgeCons::update_fixed_edge_cons(unordered_set<int> &ewin, unordered_set<int> &swin)
{
    fixed_Y_imply_X_cons = aalta_formula::TRUE();

    for (auto afY_Xcons_pair_ : afY_Xcons_pairs_)
    {
        aalta_formula *afY = afY_Xcons_pair_.first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        XCons *xCons = afY_Xcons_pair_.second;

        if (xCons->exist_ewin(ewin))
        {
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // TODO: delete curItem (afY_Xcons_pair_) from afY_Xcons_pairs_
            continue;
        }

        xCons->update_fixed_X_cons(swin);
        aalta_formula *cur_Y_imply_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_X_cons).unique();
        fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_X_cons).unique();
    }
}

aalta_formula *EdgeCons::get_fixed_edge_cons()
{
    aalta_formula *fixed_edge_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, fixed_Y_imply_X_cons).unique();
    return fixed_edge_cons;
}