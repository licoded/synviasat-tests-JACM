#include <iostream>
#include <cassert>

#include "edge_cons.h"
#include "formula_in_bdd.h"
#include "formula/aalta_formula.h"

bool XCons::exist_ewin(unordered_set<ull> &ewin)
{
    for (auto stateid2af_item : state2afX_map_)
    {
        ull state_id = stateid2af_item.first;

        if (ewin.find(state_id) != ewin.end())
            return true;
    }

    return false;
}

bool XCons::exist_ewin(ull swin_state_id)
{
    return state2afX_map_.find(swin_state_id) != state2afX_map_.end();
}

void XCons::update_fixed_swin_X_cons(unordered_set<ull> &swin)
{
    for (auto swin_state_id : swin)
    {
        auto state2afX_map_Iter = state2afX_map_.find(swin_state_id);
        if (state2afX_map_Iter != state2afX_map_.end())
        {
            aalta_formula *afX = state2afX_map_Iter->second;
            // block afX
            aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
            fixed_swin_X_cons = aalta_formula(aalta_formula::And, fixed_swin_X_cons, not_afX).unique();
            // delete curItem from state2afX_map_
            state2afX_map_.erase(state2afX_map_Iter);
        }
    }
}

void XCons::update_fixed_swin_X_cons(ull swin_state_id)
{
    auto state2afX_map_Iter = state2afX_map_.find(swin_state_id);
    if (state2afX_map_Iter != state2afX_map_.end())
    {
        aalta_formula *afX = state2afX_map_Iter->second;
        // block afX
        aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
        fixed_swin_X_cons = aalta_formula(aalta_formula::And, fixed_swin_X_cons, not_afX).unique();
        // delete curItem from state2afX_map_
        state2afX_map_.erase(state2afX_map_Iter);
    }
}

aalta_formula *XCons::choose_afX()
{
    if (state2afX_map_.empty())
        return NULL;
    // TODO: consider randomly choose?
    return state2afX_map_.begin()->second;
}

void EdgeCons::reinit_fixed_edge_cons(unordered_set<ull> &ewin, unordered_set<ull> &swin)
{
    fixed_Y_imply_X_cons = aalta_formula::TRUE();
    state_status = Status::Unknown;

    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        XCons *xCons = it->second;

        if (xCons->exist_ewin(ewin))
        {
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // delete curItem from afY_Xcons_pairs_
            afY_Xcons_pairs_.erase(it);
        }
        else
            ++it;
    }

    if (afY_Xcons_pairs_.empty())
    {
        state_status = Status::Unrealizable;
        return;
    }

    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        XCons *xCons = it->second;

        xCons->update_fixed_swin_X_cons(swin);
        aalta_formula *cur_Y_imply_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_swin_X_cons).unique();
        fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_X_cons).unique();

        if (xCons->curY_status == Status::Realizable)
        {
            state_status = Status::Realizable;
            return;
        }

        if (xCons->curY_status == Status::Undetermined)
        {
            afY_Xcons_pairs_undecided_.push_back(*it);
            afY_Xcons_pairs_.erase(it);
        }
        else
            ++it;
    }

    if (afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Unrealizable : Status::Undetermined;
        return;
    }
}

void EdgeCons::update_fixed_edge_cons(aalta_formula *af_Y, ull swin_state_id)
{
    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    assert(Iter->first == af_Y);

    XCons *xCons = Iter->second;
    xCons->update_fixed_swin_X_cons(swin_state_id);
}

void EdgeCons::update_fixed_edge_cons(aalta_formula* af_Y)
{
    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    assert(Iter->first == af_Y);

    afY_Xcons_pairs_.erase(Iter);
}

void EdgeCons::update_fixed_edge_cons(ull ewin_state_id)
{
    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        XCons *xCons = it->second;

        if (xCons->exist_ewin(ewin_state_id))
        {
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // delete curItem from afY_Xcons_pairs_
            afY_Xcons_pairs_.erase(it);
        }
        else
            ++it;
    }
}

aalta_formula *EdgeCons::get_fixed_edge_cons()
{
    aalta_formula *fixed_edge_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, fixed_Y_imply_X_cons).unique();
    return fixed_edge_cons;
}

aalta_formula *EdgeCons::choose_afY()
{
    // TODO: consider randomly choose?
    if (afY_Xcons_pairs_.empty())
    {
        if (undecided_visited_idx < afY_Xcons_pairs_undecided_.size())
            return NULL;
        else
            return afY_Xcons_pairs_undecided_[undecided_visited_idx++].first;
    }
    else
        return afY_Xcons_pairs_[0].first;
}

aalta_formula *EdgeCons::choose_afX(aalta_formula *af_Y)
{
    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    assert(Iter->first == af_Y);

    return Iter->second->choose_afX();
}