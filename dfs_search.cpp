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
    if (cur_frame->current_Y_ == NULL)
    {
        cur_frame->current_Y_= cur_frame->edgeCons_->choose_afY();
    }
    if (cur_frame->current_Y_ == NULL)
    {
        return false;
    }
    cur_frame->current_X_ = cur_frame->edgeCons_->choose_afX(cur_frame->current_Y_);
    if (cur_frame->current_X_ == NULL)
    {
        return false;
    }

    aalta_formula *edge_af = aalta_formula(aalta_formula::And, cur_frame->current_Y_, cur_frame->current_X_).unique();
    edge_af->to_set(edge_var_set);
    return true;
}

void getScc(int cur, std::vector<Syn_Frame*> &scc, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta, unordered_map<ull, int>& prefix_bdd2curIdx_map)
{
    int lowTimeId = dfn.at((ull)sta[cur]->GetBddPointer());

    while (cur >= sta.size()-1)
    {
        assert(low.at((ull)sta.back()->GetBddPointer()) == lowTimeId);

        scc.push_back(sta.back());
        sta.pop_back();
    }
}

void initial_cur_frame(Syn_Frame *cur_frame, int &time, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    dfn.insert({(ull)(cur_frame->GetBddPointer()), time});
    low.insert({(ull)(cur_frame->GetBddPointer()), time});
    time++;
}

void update_by_low(Syn_Frame *cur_frame, Syn_Frame *next_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    low.at((ull)cur_frame->GetBddPointer()) = min(low.at((ull)cur_frame->GetBddPointer()), low.at((ull)next_frame->GetBddPointer()));
}

void update_by_dfn(Syn_Frame *cur_frame, Syn_Frame *next_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low)
{
    low.at((ull)cur_frame->GetBddPointer()) = min(low.at((ull)cur_frame->GetBddPointer()), dfn.at((ull)next_frame->GetBddPointer()));
}

bool forwardSearch(Syn_Frame &cur_frame)
{
    int time = 0, cur = 0;
    unordered_map<ull, int> dfn, low;   // bddP2time
    dfn.clear(), low.clear();

    // set dfn and low value for cur_frame (init_frame)
    initial_cur_frame(&cur_frame, time, dfn, low);

    vector<Syn_Frame *> sta;
    sta.push_back(&cur_frame);
    unordered_map<ull, int> prefix_bdd2curIdx_map;
    while (cur >= 0)
    {
        Status cur_state_status = sta[cur]->checkStatus();
        bool decided_flag = cur_state_status != Status::Unknown && cur_state_status != Status::Undetermined;
        bool undecided_search_done_flag = cur_state_status == Status::Undetermined && sta[cur]->edgeCons_->undecided_afY_search_done();
        if (decided_flag || undecided_search_done_flag)    // Undetermined state maybe not searched done!!!
        {
            if (dfn.at((ull) sta[cur]->GetBddPointer()) == low.at((ull) sta[cur]->GetBddPointer()))
            {
                vector<Syn_Frame *> scc;
                getScc(cur, scc, dfn, low, sta, prefix_bdd2curIdx_map);
                backwardSearch(scc);
            }
            prefix_bdd2curIdx_map.erase((ull) sta[cur]->GetBddPointer());
            cur--;

            if (cur < 0)
                return cur_state_status == Status::Realizable;
            else
            {
                update_by_low(sta[cur], sta[cur+1], dfn, low);
                continue;
            }
        }

        unordered_set<int> edge_var_set;
        // if no edge, break!!!
        if (!get_edge_var_set(sta[cur], edge_var_set))
        {
            if (dfn.at((ull) sta[cur]->GetBddPointer()) == low.at((ull) sta[cur]->GetBddPointer()))
            {
                vector<Syn_Frame *> scc;
                getScc(cur, scc, dfn, low, sta, prefix_bdd2curIdx_map);
                backwardSearch(scc);
            }
            prefix_bdd2curIdx_map.erase((ull) sta[cur]->GetBddPointer());
            cur--;
        }
        else
        {
            aalta_formula *next_af = FormulaProgression(sta[cur]->GetFormulaPointer(), edge_var_set);
            Syn_Frame *next_frame = new Syn_Frame(next_af);

            if (dfn.find((ull) next_frame->GetBddPointer()) == dfn.end())
            {
                initial_cur_frame(next_frame, time, dfn, low);

                sta.push_back(next_frame);
                cur++;
                prefix_bdd2curIdx_map.insert({(ull) next_frame->GetBddPointer(), cur});
            }
            else if (prefix_bdd2curIdx_map.find((ull) next_frame->GetBddPointer()) != prefix_bdd2curIdx_map.end())
            {
                Syn_Frame::insert_undecided_state(sta[cur]);  // TOOD: right?
                // TODO: update edgeCons_
                // sta[cur]->edgeCons_->update_fixed_edge_cons();
                update_by_dfn(sta[cur], next_frame, dfn, low);
            }
        }
    }
    assert(false);  // shouldn't reach here, should exit in while loop
}

void backwardSearch(std::vector<Syn_Frame*> &scc)
{
    // NOTE: temporarily set all undetermined states as ewin (as before)
    for (auto it : scc)
    {
        Syn_Frame syn_frame = *it;
        if (Syn_Frame::inUndeterminedState(&syn_frame))
        {
            Syn_Frame::setEwinState(&syn_frame);
        }
    }
}