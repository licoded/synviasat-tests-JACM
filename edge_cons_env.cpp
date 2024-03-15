#include <iostream>
#include <cassert>

#include "edge_cons_env.h"
#include "formula_in_bdd.h"
#include "formula/aalta_formula.h"

bool XCons::exist_swin(unordered_set<ull> &swin)
{
    for (auto stateid2af_item : state2afX_map_)
    {
        ull state_id = stateid2af_item.first;

        if (swin.find(state_id) != swin.end())
            return true;
    }

    return false;
}

bool XCons::exist_swin(ull swin_state_id)
{
    return state2afX_map_.find(swin_state_id) != state2afX_map_.end();
}

void XCons::update_fixed_ewin_X_cons(unordered_set<ull> &ewin)
{
    for (auto swin_state_id : ewin)
    {
        auto state2afX_map_Iter = state2afX_map_.find(swin_state_id);
        if (state2afX_map_Iter != state2afX_map_.end())
        {
            aalta_formula *afX = state2afX_map_Iter->second;
            // block afX
            aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
            fixed_ewin_X_cons = aalta_formula(aalta_formula::And, fixed_ewin_X_cons, not_afX).unique();
            // delete curItem from state2afX_map_
            state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
        }
    }

    if (state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Unrealizable : Status::Undetermined;
    }
}

void XCons::update_fixed_ewin_X_cons(ull ewin_state_id)
{
    auto state2afX_map_Iter = state2afX_map_.find(ewin_state_id);
    if (state2afX_map_Iter != state2afX_map_.end())
    {
        aalta_formula *afX = state2afX_map_Iter->second;
        // block afX
        aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
        fixed_ewin_X_cons = aalta_formula(aalta_formula::And, fixed_ewin_X_cons, not_afX).unique();
        // delete curItem from state2afX_map_
        state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
    }

    if (state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Unrealizable : Status::Undetermined;
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

    if (state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Unrealizable : Status::Undetermined;
    }
}

void XCons::update_fixed_ewin_X_cons_repeat_prefix(ull prefix_state_id)
{
    auto state2afX_map_Iter = state2afX_map_.find(prefix_state_id);
    if (state2afX_map_Iter != state2afX_map_.end())
    {
        aalta_formula *afX = state2afX_map_Iter->second;
        // block afX
        aalta_formula *not_afX = aalta_formula(aalta_formula::Not, NULL, afX).unique();
        fixed_ewin_X_cons = aalta_formula(aalta_formula::And, fixed_ewin_X_cons, not_afX).unique();
        // delete curItem from state2afX_map_
        state2afX_map_Iter = state2afX_map_.erase(state2afX_map_Iter);
        // add curItem to undecided_afX_state_pairs_
        undecided_afX_state_pairs_.insert({prefix_state_id, afX});
    }
    // NOTE: if not found, maybe because the repeat prefix has been visited before, so do nothing

    if (state2afX_map_.empty())
    {
        curY_status = undecided_afX_state_pairs_.empty() ? Status::Unrealizable : Status::Undetermined;
    }
}

afX_state_pair *XCons::choose_afX()
{
    if (state2afX_map_.empty())
        return NULL;
    // TODO: consider randomly choose?
    auto chosen_aftae2afX_Iter = state2afX_map_.begin();
    aalta_formula::af_prt_set afX_set = chosen_aftae2afX_Iter->second->to_or_set();
    afX_state_pair *tmp = new afX_state_pair(*afX_set.begin(), chosen_aftae2afX_Iter->first);
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

        if (xCons->exist_swin(swin))
        {
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // delete curItem from afY_Xcons_pairs_
            it = afY_Xcons_pairs_.erase(it);
        }
        else
            ++it;
    }

    for (auto it = afY_Xcons_pairs_.begin(); it != afY_Xcons_pairs_.end();)
    {
        aalta_formula *afY = it->first;
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, afY).unique();
        shared_ptr<XCons> xCons = it->second;

        xCons->update_fixed_ewin_X_cons(ewin);
        if (xCons->fixed_ewin_X_cons != aalta_formula::TRUE())
        {
            aalta_formula *cur_Y_imply_ewin_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_ewin_X_cons).unique();
            fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_ewin_X_cons).unique();
        }

        xCons->update_fixed_undecided_X_cons(undecided);
        if (xCons->fixed_undecided_X_cons != aalta_formula::TRUE())
        {
            aalta_formula *cur_Y_imply_undecided_X_cons = aalta_formula(aalta_formula::Or, not_afY, xCons->fixed_undecided_X_cons).unique();
            fixed_Y_imply_X_cons = aalta_formula(aalta_formula::And, fixed_Y_imply_X_cons, cur_Y_imply_undecided_X_cons).unique();
        }

        if (xCons->curY_status != Status::Unknown)
        {
            assert(xCons->curY_status != Status::Realizable);
            state_status = xCons->curY_status;

            if (xCons->curY_status == Status::Undetermined)
                afY_Xcons_pairs_undecided_.push_back(*it);
            fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
            // delete curItem from afY_Xcons_pairs_
            it = afY_Xcons_pairs_.erase(it);
            return;
        }
        else    // only can be Unknown here, since we have checked Unrealizable in last for loop
                // TODO: so we can add a assert to check here!
                //       consider whether need? as maybe very easy to infer from above if conds
            ++it;
    }

    if (afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Realizable : Status::Undetermined;
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
    assert(Iter != afY_Xcons_pairs_undecided_.end());
    assert(Iter->first == af_Y);

    shared_ptr<XCons> xCons = Iter->second;
    xCons->update_fixed_ewin_X_cons_repeat_prefix(prefix_state_id);
    // TODO: assert(xCons->curY_status != Status::Realizable);
    if (xCons->curY_status == Status::Undetermined)
    {
        // TODO: one Y(env var) leads to Undetermined state, then cur state is Undetermined!!!
        afY_Xcons_pairs_undecided_.push_back(*Iter);
        afY_Xcons_pairs_.erase(Iter);
    }
    if (afY_Xcons_pairs_.empty())
    {
        state_status = afY_Xcons_pairs_undecided_.empty() ? Status::Realizable : Status::Undetermined;
    }
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
    assert(Iter != afY_Xcons_pairs_undecided_.end());
    assert(Iter->first == af_Y);

    shared_ptr<XCons> xCons = Iter->second;
    switch (next_status)
    {
    case Status::Realizable:
        if (xCons->exist_swin(next_state_id))
        {
            xCons->curY_status = Status::Realizable;
        }
        /*
         * NOTE: we cannot say cur state is Realizable here, because
         *       only all Ys(env vars) exist X to lead to swin states, can we say cur state is Realizable!!!
         */
        break;

    case Status::Unrealizable:
        /* NOTE: will not cause BUG (mistake/overwrite Realizable as Unrealizable),
         *       if we delete xCons immediately after judge it as Realizable
         */
        xCons->update_fixed_ewin_X_cons(next_state_id);
        break;

    case Status::Undetermined:
        xCons->update_fixed_ewin_X_cons_repeat_prefix(next_state_id);
        break;
    }

    // place all needed deletion and update here
    if (xCons->curY_status != Status::Unknown)
    {
        /* STEP1: update state_status */
        if (xCons->curY_status != Status::Realizable)
            state_status = xCons->curY_status;
        /* STEP2: disable cur_afY in fixed_Y_cons */
        aalta_formula *not_afY = aalta_formula(aalta_formula::Not, NULL, af_Y).unique();
        fixed_Y_cons = aalta_formula(aalta_formula::And, fixed_Y_cons, not_afY).unique();
        /* STEP3: delete curItem from afY_Xcons_pairs_ */
        if (xCons->curY_status == Status::Undetermined)
            afY_Xcons_pairs_undecided_.push_back(*Iter);
        // TODO: may consider don't delete when Unrealizable, for debug convience!!!
        afY_Xcons_pairs_.erase(Iter);
    }

    if (!afY_Xcons_pairs_undecided_.empty())
        state_status = Status::Undetermined;
    else if (state_status == Status::Unknown && afY_Xcons_pairs_.empty())
        /*
         * Why check state_status == Status::Unknown? or check state_status != Status::Unrealizable (the two judges ares equivalent here)
         *      Because we can infer cur state is Unrealizable if one Y(env var) leads to ewin state,
         *      and we also delete those Ys(env vars) as Ys can lead to swin state
         */
        state_status = Status::Realizable;
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
        return NULL;
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
    assert(Iter != afY_Xcons_pairs_.end());
    assert(Iter->first == af_Y);

    return Iter->second->choose_afX();
}

void XCons::print_map(unordered_map<ull, aalta_formula*> &state2afX_map)
{
    for (auto state2afX_item : state2afX_map)
    {
        cout << "\tX:\t" << state2afX_item.first << " : " << state2afX_item.second->to_string() << endl;
        DdNode *bddP = (DdNode *)state2afX_item.first;
        aalta_formula *next_state_af = (aalta_formula *)(FormulaInBdd::bddP_to_afP[ull(bddP)]);
        cout << "\t\t\t" << (next_state_af == NULL ? "" : next_state_af->to_string()) << endl;
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