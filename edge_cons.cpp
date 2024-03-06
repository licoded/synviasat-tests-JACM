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

bool XCons::exist_ewin(ull ewin_state_id)
{
    return state2afX_map_.find(ewin_state_id) != state2afX_map_.end();
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
            state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
        }
    }

    if (curY_status == Status::Unknown && state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Realizable : Status::Undetermined;
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
        state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
    }

    if (curY_status == Status::Unknown && state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Realizable : Status::Undetermined;
    }
}

void XCons::update_fixed_undecided_X_cons(unordered_set<ull> &undecided)
{
    for (auto undecided_state_id : undecided)
    {
        auto state2afX_map_Iter = state2afX_map_.find(undecided_state_id);
        if (state2afX_map_Iter != state2afX_map_.end())
        {
            aalta_formula *afX = state2afX_map_Iter->second;
            // block afX
            aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
            fixed_undecided_X_cons = aalta_formula(aalta_formula::And, fixed_undecided_X_cons, not_afX).unique();
            // delete curItem from state2afX_map_
            state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
            // add curItem to undecided_afX_state_pairs_
            undecided_afX_state_pairs_.insert({undecided_state_id, afX});
        }
    }

    if (curY_status == Status::Unknown && state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Realizable : Status::Undetermined;
    }
}

void XCons::update_fixed_swin_X_cons_repeat_prefix(ull prefix_state_id)
{
    auto state2afX_map_Iter = state2afX_map_.find(prefix_state_id);
    if (state2afX_map_Iter != state2afX_map_.end())
    {
        aalta_formula *afX = state2afX_map_Iter->second;
        // block afX
        aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
        fixed_swin_X_cons = aalta_formula(aalta_formula::And, fixed_swin_X_cons, not_afX).unique();
        // delete curItem from state2afX_map_
        state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
        // add curItem to undecided_afX_state_pairs_
        undecided_afX_state_pairs_.insert({prefix_state_id, afX});
    }
    // NOTE: if not found, maybe because the repeat prefix has been visited before, so do nothing
}

afX_state_pair *XCons::choose_afX()
{
    if (state2afX_map_.empty())
        return NULL;
    // TODO: consider randomly choose?
    auto chosen_aftae2afX_Iter = state2afX_map_.begin();
    afX_state_pair *tmp = new afX_state_pair(chosen_aftae2afX_Iter->second, chosen_aftae2afX_Iter->first);
    return tmp;
}

void EdgeCons::update_fixed_edge_cons(unordered_set<ull> &ewin, unordered_set<ull> &swin, unordered_set<ull> &undecided)
{
    // fixed_Y_imply_X_cons = aalta_formula::TRUE();
    // state_status = Status::Unknown;

    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        shared_ptr<XCons> xCons = it->second;

        if (xCons->exist_ewin(ewin))
        {
            xCons->curY_status = Status::Unrealizable;
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // delete curItem from afY_Xcons_pairs_
            it = afY_Xcons_pairs_.erase(it);
        }
        else
            ++it;
    }

    if (state_status == Status::Unknown && afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Unrealizable : Status::Undetermined;
    }

    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        shared_ptr<XCons> xCons = it->second;

        xCons->update_fixed_swin_X_cons(swin);
        aalta_formula *cur_Y_imply_swin_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_swin_X_cons).unique();
        fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_swin_X_cons).unique();

        xCons->update_fixed_undecided_X_cons(undecided);
        aalta_formula *cur_Y_imply_undecided_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_undecided_X_cons).unique();
        fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_undecided_X_cons).unique();

        if (state_status == Status::Unknown && xCons->curY_status == Status::Realizable)
        {
            state_status = Status::Realizable;
            return;
        }

        if (state_status == Status::Unknown && xCons->curY_status == Status::Undetermined)
        {
            afY_Xcons_pairs_undecided_.push_back(*it);
            it = afY_Xcons_pairs_.erase(it);
        }
        else    // only can be Unknown here, since we have checked Unrealizable in last for loop
            ++it;
    }

    if (state_status == Status::Unknown && afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Unrealizable : Status::Undetermined;
    }
}

/* TODO: consider afY_Xcons_pairs_undetermined!!! */
void EdgeCons::update_fixed_edge_cons_repeat_prefix(aalta_formula *af_Y, ull prefix_state_id)
{
    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    bool isSearchingUndecided = Iter == afY_Xcons_pairs_.end();
    if (isSearchingUndecided)
    {
        for (Iter = afY_Xcons_pairs_undecided_.begin(); Iter != afY_Xcons_pairs_undecided_.end(); Iter++)
        {
            if (Iter->first == af_Y)
                break;
        }
    }
    assert(Iter != afY_Xcons_pairs_undecided_.end());
    assert(Iter->first == af_Y);

    shared_ptr<XCons> xCons = Iter->second;
    xCons->update_fixed_swin_X_cons_repeat_prefix(prefix_state_id);
    if (!isSearchingUndecided)
    {
        afY_Xcons_pairs_undecided_.push_back(*Iter);
        afY_Xcons_pairs_.erase(Iter);
    }
    // NOTE: needn't to check and update Status, because Syn_Frame::checkStatus -> EdgeCons::update_fixed_edge_cons will do this
}

/* TODO: consider afY_Xcons_pairs_undetermined!!! */
void EdgeCons::update_fixed_edge_cons(aalta_formula* af_Y, ull next_state_id, Status next_status)
{
    assert(next_status != Status::Unknown);

    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    bool isSearchingUndecided = Iter == afY_Xcons_pairs_.end();
    if (isSearchingUndecided)
    {
        for (Iter = afY_Xcons_pairs_undecided_.begin(); Iter != afY_Xcons_pairs_undecided_.end(); Iter++)
        {
            if (Iter->first == af_Y)
                break;
        }
    }
    assert(Iter != afY_Xcons_pairs_undecided_.end());
    assert(Iter->first == af_Y);
    // TODO: replace with following codes?
    // if (Iter == afY_Xcons_pairs_.end())
    // {
    //     return;
    // }

    shared_ptr<XCons> xCons = Iter->second;
    switch (next_status)
    {
    case Status::Realizable:
        xCons->update_fixed_swin_X_cons(next_state_id);
        if (state_status == Status::Unknown && xCons->curY_status == Status::Realizable)
        {
            state_status = Status::Realizable;
        }
        break;

    case Status::Unrealizable:
        if (xCons->exist_ewin(next_state_id))
        {
            aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, af_Y).unique();
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            if (isSearchingUndecided)
                afY_Xcons_pairs_undecided_.erase(Iter);
            else
                afY_Xcons_pairs_.erase(Iter);
        }
        break;

    case Status::Undetermined:
        xCons->update_fixed_swin_X_cons_repeat_prefix(next_state_id);
        if (!isSearchingUndecided)
        {
            afY_Xcons_pairs_undecided_.push_back(*Iter);
            afY_Xcons_pairs_.erase(Iter);
        }
        break;
    
    default:
        break;
    }

    if (state_status == Status::Unknown && afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Unrealizable : Status::Undetermined;
    }
}


// void EdgeCons::update_fixed_edge_cons(aalta_formula* af_Y)
// {
//     vector<afY_Xcons_pair>::iterator Iter;
//     for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
//     {
//         if (Iter->first == af_Y)
//             break;
//     }
//     assert(Iter->first == af_Y);

//     afY_Xcons_pairs_.erase(Iter);
// }

// void EdgeCons::update_fixed_edge_cons(ull ewin_state_id)
// {
//     for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
//     {
//         aalta_formula *afY = it->first;
//         aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
//         XCons *xCons = it->second;

//         if (xCons->exist_ewin(ewin_state_id))
//         {
//             fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
//             // delete curItem from afY_Xcons_pairs_
//             afY_Xcons_pairs_.erase(it);
//         }
//         else
//             ++it;
//     }
// }

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
        while (undecided_visited_idx < afY_Xcons_pairs_undecided_.size())
        {
            auto it = afY_Xcons_pairs_undecided_[undecided_visited_idx];
            if (it.second->undecided_afX_search_done())
            {
                undecided_visited_idx++;
                continue;
            }
            return it.first;
        }
        return NULL;
        // if (undecided_visited_idx < afY_Xcons_pairs_undecided_.size())
        //     return NULL;
        // else
        //     return afY_Xcons_pairs_undecided_[undecided_visited_idx++].first;
    }
    else
        return afY_Xcons_pairs_[0].first;
}

afX_state_pair *EdgeCons::choose_afX(aalta_formula *af_Y)
{
    vector<afY_Xcons_pair>::iterator Iter;
    for (Iter = afY_Xcons_pairs_.begin(); Iter != afY_Xcons_pairs_.end(); Iter++)
    {
        if (Iter->first == af_Y)
            break;
    }
    bool isSearchingUndecided = Iter == afY_Xcons_pairs_.end();
    if (isSearchingUndecided)
    {
        for (Iter = afY_Xcons_pairs_undecided_.begin(); Iter != afY_Xcons_pairs_undecided_.end(); Iter++)
        {
            if (Iter->first == af_Y)
                break;
        }
    }
    assert(Iter != afY_Xcons_pairs_undecided_.end());
    assert(Iter->first == af_Y);

    return Iter->second->choose_afX();
}

void XCons::print_map(unordered_map<ull, aalta_formula*> &state2afX_map)
{
    for (auto state2afX_item : state2afX_map)
    {
        cout << "\tX:\t" << state2afX_item.first << " : " << state2afX_item.second->to_string() << endl;
        DdNode *bddP = (DdNode *)state2afX_item.first;
        cout << "\t\t" << Cudd_IsConstant(bddP) 
            << "\t" << Cudd_IsComplement(bddP) 
            << "\t" << (bddP == FormulaInBdd::TRUE_bddP_)
            << "\t" << (bddP == FormulaInBdd::FALSE_bddP_)
            << endl;
    }
}

void EdgeCons::print_vector(vector<afY_Xcons_pair> &afY_Xcons_pairs_vec)
{
    for (auto afY_Xcons_pair : afY_Xcons_pairs_vec)
    {
        aalta_formula *af_Y = afY_Xcons_pair.first;
        auto xCons = afY_Xcons_pair.second;
        cout << "Y:\t" << afY_Xcons_pair.first->to_string() << " : " << endl;
        xCons->print_map(xCons->state2afX_map_);
    }
}

void XCons::print_all_map()
{
    print_map(state2afX_map_);
    print_map(undecided_afX_state_pairs_);
}

void EdgeCons::print_all_vec()
{
    for (auto afY_Xcons_pair : afY_Xcons_pairs_)
    {
        aalta_formula *af_Y = afY_Xcons_pair.first;
        auto xCons = afY_Xcons_pair.second;
        cout << "Y:\t" << afY_Xcons_pair.first->to_string() << " : " << endl;
        xCons->print_all_map();
    }
    for (auto afY_Xcons_pair : afY_Xcons_pairs_undecided_)
    {
        aalta_formula *af_Y = afY_Xcons_pair.first;
        auto xCons = afY_Xcons_pair.second;
        cout << "Y:\t" << afY_Xcons_pair.first->to_string() << " : " << endl;
        xCons->print_all_map();
    }
}

XCons::~XCons()
{
    // for (auto &pair : state2afX_map_)
    // {
    //     delete pair.second;
    // }
    // state2afX_map_.clear();

    // for (auto &pair : undecided_afX_state_pairs_)
    // {
    //     delete pair.second;
    // }
    // undecided_afX_state_pairs_.clear();

    // delete fixed_swin_X_cons;
    // delete fixed_undecided_X_cons;
}

EdgeCons::~EdgeCons()
{
    // for (auto &pair : afY_Xcons_pairs_)
    // {
    //     delete pair.first;
    // }
    // afY_Xcons_pairs_.clear();

    // for (auto &pair : afY_Xcons_pairs_undecided_)
    // {
    //     delete pair.first;
    // }
    // afY_Xcons_pairs_undecided_.clear();

    // delete fixed_Y_cons;
    // delete fixed_Y_imply_X_cons;
}