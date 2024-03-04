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
        /* TODO: replace with following codes? */
        // cur_frame->current_Y_ = NULL;
        // return get_edge_var_set(cur_frame, edge_var_set);
        return false;
    }

    aalta_formula *edge_af = aalta_formula(aalta_formula::And, cur_frame->current_Y_, cur_frame->current_X_).unique();
    edge_af = edge_af->simplify();
    cout << edge_af->to_string() << endl;
    edge_af->to_set(edge_var_set);
    return true;
}

void getScc(int cur, std::vector<Syn_Frame*> &scc, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta, unordered_map<ull, int>& prefix_bdd2curIdx_map)
{
    int lowTimeId = dfn.at((ull)sta[cur]->GetBddPointer());

    while (!sta.empty() && low.at((ull)sta.back()->GetBddPointer()) == lowTimeId)
    {
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
    unordered_map<ull, int> prefix_bdd2curIdx_map;
    sta.push_back(&cur_frame);
    prefix_bdd2curIdx_map.insert({(ull)cur_frame.GetBddPointer(), cur});
    while (cur >= 0)
    {
        Status cur_state_status = sta[cur]->checkStatus();
        bool decided_flag = cur_state_status != Status::Unknown && cur_state_status != Status::Undetermined;
        bool undecided_search_done_flag = cur_state_status == Status::Undetermined && sta[cur]->edgeCons_->undecided_afY_search_done();
        if (decided_flag || undecided_search_done_flag)    // Undetermined state maybe not searched done!!!
        {
            Syn_Frame *next_frame = sta[cur];
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
                aalta_formula *afY = sta[cur]->current_Y_;
                sta[cur]->edgeCons_->update_fixed_edge_cons(afY, (ull)next_frame->GetBddPointer(), cur_state_status);

                update_by_low(sta[cur], next_frame, dfn, low);
                continue;
            }
        }

        unordered_set<int> edge_var_set;
        /* TODO: repalce exp in if with following line? */
        // assert(get_edge_var_set(sta[cur], edge_var_set));
        // if no edge, break!!!
        if (!get_edge_var_set(sta[cur], edge_var_set))
        {
            assert(false);
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
            aalta_formula *next_af = FormulaProgression(sta[cur]->GetFormulaPointer(), edge_var_set)->simplify();
            Syn_Frame *next_frame = new Syn_Frame(next_af);
            cout << "cur\t" << sta[cur]->GetFormulaPointer()->to_string() << endl;
            cout << "next\t" << next_frame->GetFormulaPointer()->to_string() << endl;

            if (dfn.find((ull) next_frame->GetBddPointer()) == dfn.end())
            {
                initial_cur_frame(next_frame, time, dfn, low);

                sta.push_back(next_frame);
                cur++;
                prefix_bdd2curIdx_map.insert({(ull) next_frame->GetBddPointer(), cur});
            }
            else if (prefix_bdd2curIdx_map.find((ull) next_frame->GetBddPointer()) != prefix_bdd2curIdx_map.end())
            {
                /**
                 * cur_Y has X -> prefix, cannot make cur_state undetermined
                 * only all Y has X -> prefix, can make cur_state undetermined
                */
                sta[cur]->edgeCons_->update_fixed_edge_cons_repeat_prefix(sta[cur]->current_Y_, (ull)next_frame->GetBddPointer());
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
        if (Syn_Frame::inUndeterminedState(it))
        {
            Syn_Frame::setEwinState(it);
        }
    }
}