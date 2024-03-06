#include "dfs_search.h"

unordered_map<ull, int> TarjanSearch::dfn;
unordered_map<ull, int> TarjanSearch::low;
int TarjanSearch::time;

void TarjanSearch::tarjan_search_init()
{
    time = 0;
}

bool get_edge_var_set(Syn_Frame *cur_frame, unordered_set<int>& edge_var_set)
{
    // aalta_formula *edge_cons_af = cur_frame->edgeCons_->get_fixed_edge_cons();
    cur_frame->current_Y_= cur_frame->edgeCons_->choose_afY();
    // if (cur_frame->current_Y_ == NULL)
    // {
    //     cur_frame->current_Y_= cur_frame->edgeCons_->choose_afY();
    // }
    if (cur_frame->current_Y_ == NULL)
    {
        return false;
    }
    afX_state_pair *chosen_afX_state_pair = cur_frame->edgeCons_->choose_afX(cur_frame->current_Y_);
    if (chosen_afX_state_pair == NULL)
    {
        /* TODO: replace with following codes? */
        // cur_frame->current_Y_ = NULL;
        // return get_edge_var_set(cur_frame, edge_var_set);
        delete chosen_afX_state_pair;
        return false;
    }
    cur_frame->current_X_ = chosen_afX_state_pair->first;
    cur_frame->current_next_stateid_ = chosen_afX_state_pair->second;
    delete chosen_afX_state_pair;

    aalta_formula *edge_af = aalta_formula(aalta_formula::And, cur_frame->current_Y_, cur_frame->current_X_).unique();
    edge_af = edge_af->simplify();
    dout << edge_af->to_string() << endl;
    edge_af->to_set(edge_var_set);
    return true;
}

void getScc(int cur, std::vector<Syn_Frame*> &scc, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta, unordered_map<ull, int>& prefix_bdd2curIdx_map, unordered_map<ull, int>& sta_bdd2curIdx_map)
{
    int lowTimeId = dfn.at((ull)sta[cur]->GetBddPointer());

    while (!sta.empty() && low.at((ull)sta.back()->GetBddPointer()) == lowTimeId)
    {
        scc.push_back(sta.back());
        /* TODO: assert exist before erase? And may bdd_prt repeat in sta, and when 2nd erase it will? */
        sta_bdd2curIdx_map.erase(ull(sta.back()->GetBddPointer()));
        sta.pop_back();
    }
}

bool sccRoot_isNone(Syn_Frame *cur_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta)
{
    return dfn.at(ull(sta.back()->GetBddPointer())) < low.at(ull(cur_frame->GetBddPointer()));
}

void initial_cur_frame(Syn_Frame *cur_frame, int &time, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    dfn.insert({(ull)(cur_frame->GetBddPointer()), time});
    low.insert({(ull)(cur_frame->GetBddPointer()), time});
    time++;
}

void update_by_low(Syn_Frame *cur_frame, DdNode *next_bddP, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    low.at((ull)cur_frame->GetBddPointer()) = min(low.at((ull)cur_frame->GetBddPointer()), low.at((ull)next_bddP));
}

void update_by_dfn(Syn_Frame *cur_frame, Syn_Frame *next_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    low.at((ull)cur_frame->GetBddPointer()) = min(low.at((ull)cur_frame->GetBddPointer()), dfn.at((ull)next_frame->GetBddPointer()));
}

bool forwardSearch(Syn_Frame *cur_frame)
{
    int time = 0, cur = 0;
    unordered_map<ull, int> dfn, low;   // bddP2time
    dfn.clear(), low.clear();

    // set dfn and low value for cur_frame (init_frame)
    initial_cur_frame(cur_frame, time, dfn, low);

    vector<Syn_Frame *> sta;
    unordered_map<ull, int> prefix_bdd2curIdx_map;
    unordered_map<ull, int> sta_bdd2curIdx_map;
    // unordered_map<ull, int> bdd_to_state_map;   // TODO: use this map to record status!!!!
    sta.push_back(cur_frame);
    prefix_bdd2curIdx_map.insert({(ull)cur_frame->GetBddPointer(), cur});
    sta_bdd2curIdx_map.insert({(ull)cur_frame->GetBddPointer(), cur});
    while (cur >= 0)
    {
        Status cur_state_status = sta[cur]->checkStatus();
        bool decided_flag = cur_state_status != Status::Unknown && cur_state_status != Status::Undetermined;
        bool undecided_search_done_flag = cur_state_status == Status::Undetermined && sta[cur]->edgeCons_->undecided_afY_search_done();
        dout << cur << "\t" << cur_state_status << "\t" << decided_flag << "\t" << undecided_search_done_flag << endl;
        if (decided_flag || undecided_search_done_flag)    // Undetermined state maybe not searched done!!!
        {
            switch (cur_state_status)
            {
            case Status::Realizable:
                Syn_Frame::setSwinState(sta[cur]);
                break;

            case Status::Unrealizable:
                Syn_Frame::setEwinState(sta[cur]);
                break;

            case Status::Undetermined:
                Syn_Frame::insert_undecided_state(sta[cur]);
                break;
            
            default:
                break;
            }

            DdNode *next_bddP = sta[cur]->GetBddPointer();
            if (dfn.at((ull) sta[cur]->GetBddPointer()) == low.at((ull) sta[cur]->GetBddPointer()))
            {
                vector<Syn_Frame *> scc;
                getScc(cur, scc, dfn, low, sta, prefix_bdd2curIdx_map, sta_bdd2curIdx_map);
                backwardSearch(scc);
                scc.clear();
            }
            prefix_bdd2curIdx_map.erase((ull) next_bddP);
            cur--;

            if (cur < 0)
            {
                return cur_state_status == Status::Realizable;
            }
            else
            {
                Status next_state_status = cur_state_status;
                sta[cur]->edgeCons_->update_fixed_edge_cons(sta[cur]->current_Y_, sta[cur]->current_next_stateid_, next_state_status);

                update_by_low(sta[cur], next_bddP, dfn, low);
                continue;
            }
        }

        unordered_set<int> edge_var_set;
        /* TODO: repalce exp in if with following line? */
        // assert(get_edge_var_set(sta[cur], edge_var_set));
        // if no edge, break!!!
        if (!get_edge_var_set(sta[cur], edge_var_set))
        {
            continue;
            // assert(false);
            // if (dfn.at((ull) sta[cur]->GetBddPointer()) == low.at((ull) sta[cur]->GetBddPointer()))
            // {
            //     vector<Syn_Frame *> scc;
            //     getScc(cur, scc, dfn, low, sta, prefix_bdd2curIdx_map);
            //     backwardSearch(scc);
            // }
            // prefix_bdd2curIdx_map.erase((ull) sta[cur]->GetBddPointer());
            // cur--;
        }
        else if (IsAcc(sta[cur]->GetFormulaPointer(), edge_var_set))    // i.e. next_frame is true/swin
        {
            sta[cur]->edgeCons_->update_fixed_edge_cons(sta[cur]->current_Y_, sta[cur]->current_next_stateid_, Status::Realizable);
        }
        else
        {
            aalta_formula *next_af = FormulaProgression(sta[cur]->GetFormulaPointer(), edge_var_set)->simplify();
            Syn_Frame *next_frame = new Syn_Frame(next_af);
            dout << "cur\t" << sta[cur]->GetFormulaPointer()->to_string() << endl;
            dout << "next\t" << next_frame->GetFormulaPointer()->to_string() << endl;

            if (dfn.find((ull) next_frame->GetBddPointer()) == dfn.end())
            {
                initial_cur_frame(next_frame, time, dfn, low);

                sta.push_back(next_frame);
                cur++;
                prefix_bdd2curIdx_map.insert({(ull) next_frame->GetBddPointer(), cur});
                sta_bdd2curIdx_map.insert({(ull) next_frame->GetBddPointer(), cur});

                // cur-- (backward) is done not here, so not update low here!!!
            }
            // explain next line: else if (sccRoot_isNone())
            else 
            {
                // update low
                if (sta_bdd2curIdx_map.find(ull(next_frame->GetBddPointer())) != sta_bdd2curIdx_map.end())
                {
                    update_by_dfn(sta[cur], next_frame, dfn, low);
                }

                // do synthesis feedback
                if (prefix_bdd2curIdx_map.find((ull) next_frame->GetBddPointer()) != prefix_bdd2curIdx_map.end())
                {
                    /**
                     * cur_Y has X -> prefix, cannot make cur_state undetermined
                     * only all Y has X -> prefix, can make cur_state undetermined
                    */
                    // sta[cur]->edgeCons_->update_fixed_edge_cons_repeat_prefix(sta[cur]->current_Y_, (ull)next_frame->GetBddPointer());
                    sta[cur]->edgeCons_->update_fixed_edge_cons_repeat_prefix(sta[cur]->current_Y_, sta[cur]->current_next_stateid_);
                }
                else    // else: has cur-- (moved backward)
                {
                    Status next_state_status = next_frame->checkStatus();
                    /* Because it has cur-- (moved backward), so it must have finished its search!!! */
                    assert(next_state_status != Status::Unknown);   // if not OK, create bdd_to_status_map_
                    sta[cur]->edgeCons_->update_fixed_edge_cons(sta[cur]->current_Y_, sta[cur]->current_next_stateid_, next_state_status);
                }
                delete next_frame;
            }
        }
    }
    assert(false);  // shouldn't reach here, should exit in while loop
}

void backwardSearch(std::vector<Syn_Frame*> &scc)
{
    // NOTE: temporarily set all undetermined states as ewin (as before)
    for (int i = scc.size(); i > 0; i--)
    {
        auto it = scc[i-1];
        if (Syn_Frame::inUndeterminedState(it->GetBddPointer()))
        {
            Syn_Frame::setEwinState(it);
        }
        delete it;
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
