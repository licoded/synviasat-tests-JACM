#include "dfs_search.h"

unordered_map<ull, int> TarjanSearch::dfn;
unordered_map<ull, int> TarjanSearch::low;
int TarjanSearch::time;

void TarjanSearch::tarjan_search_init()
{
    time = 0;
}

void getScc(int cur, std::vector<Syn_Frame*> &scc, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta)
{
    // === TODO: popout
    // sta.pop_back();
    // prefix_bdd2curIdx_map.erase(cur+1);
}

bool forwardSearch(Syn_Frame &cur_frame)
{
    int time = 0, cur = 0;
    unordered_map<ull, int> dfn, low;   // bddP2time
    dfn.clear(), low.clear();

    // set dfn and low value for cur_frame (init_frame)
    dfn.insert({(ull)(cur_frame.GetBddPointer()), time});
    low.insert({(ull)(cur_frame.GetBddPointer()), time});
    time++;

    vector<Syn_Frame *> sta;
    sta.push_back(&cur_frame);
    unordered_map<ull, int> prefix_bdd2curIdx_map;
    while (cur >= 0)
    {
        Status cur_state_status = Syn_Frame::checkStatus(cur_frame);
        if (cur_state_status != Status::Unknown)
        {
            cur--;
            // TODO: detect scc
            if (TarjanSearch::isSccRoot(cur_frame))
            {
                std::vector<Syn_Frame *> *scc = TarjanSearch::getScc();
                backwardSearch(*scc);
            }
            if (cur < 0)
                return cur_state_status == Status::Realizable;
            else
            {
                low.at((ull)sta[cur]->GetBddPointer()) = min(low.at((ull)sta[cur]->GetBddPointer()), low.at((ull)sta[cur+1]->GetBddPointer()));
                continue;
            }
        }

        unordered_set<int> *edge_var_set;
        get_edge_var_set(cur_frame, *edge_var_set);

        // if no edge, break!!!
        if (edge_var_set == NULL)
        {
            if (dfn.at((ull) sta[cur]->GetBddPointer()) == low.at((ull) sta[cur]->GetBddPointer()))
            {
                vector<Syn_Frame *> scc;
                getScc(cur, scc, dfn, low, sta);
                backwardSearch(scc);
            }
            cur--;
        }
        else
        {
            aalta_formula *next_af = FormulaProgression(sta[cur]->GetFormulaPointer(), *edge_var_set);
            Syn_Frame *next_frame = new Syn_Frame(next_af);

            if (dfn.find((ull) next_frame->GetBddPointer()) == dfn.end())
            {
                dfn.insert({(ull) next_frame->GetBddPointer(), time});
                low.insert({(ull) next_frame->GetBddPointer(), time});
                time++;

                sta.push_back(next_frame);
                cur++;
                prefix_bdd2curIdx_map.insert({(ull) next_frame->GetBddPointer(), cur});
            }
            else if (prefix_bdd2curIdx_map.find((ull) next_frame->GetBddPointer()) != prefix_bdd2curIdx_map.end())
            {
                low.at((ull)sta[cur]->GetBddPointer()) = min(low.at((ull)sta[cur]->GetBddPointer()), dfn.at((ull)next_frame->GetBddPointer()));
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
        if (Syn_Frame::isUndeterminedState(syn_frame))
        {
            Syn_Frame::setEwinState(syn_frame);
        }
    }
}