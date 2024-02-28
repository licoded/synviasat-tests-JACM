#include "dfs_search.h"

unordered_map<ull, int> TarjanSearch::dfn;
unordered_map<ull, int> TarjanSearch::low;
int TarjanSearch::time;

void TarjanSearch::tarjan_search_init()
{
    time = 0;
}

bool forwardSearch(Syn_Frame &cur_frame)
{
    int time = 0, cur = 0;
    unordered_map<ull, int> dfn, low;
    dfn.clear(), low.clear();

    // set dfn and low value for cur_frame (init_frame)
    dfn.insert({(ull)(&cur_frame), time});
    low.insert({(ull)(&cur_frame), time});
    time++;

    vector<Syn_Frame *> sta;
    unordered_set<ull> prefix_bdd_ptr_set;
    while (true)
    {
        Status cur_state_status = Syn_Frame::checkStatus(cur_frame);
        if (cur_state_status != Status::Unknown)
        {
            cur--;
            // TODO: need detect scc here
            if (cur < 0)
                return cur_state_status == Status::Realizable;
            else
            {
                low.at((ull)sta[cur]) = min(low.at((ull)sta[cur]), low.at((ull)sta[cur+1]));
                continue;
            }
        }

        unordered_set<int> *edge_var_set;
        get_edge_var_set(cur_frame, *edge_var_set);

        // if no edge, break!!!
        if (edge_var_set == NULL)
        {
            if (dfn.at((ull) sta[cur] == low.at((ull) sta[cur])))
            {
                vector<Syn_Frame *> scc;
                getScc(cur, scc, dfn, low, sta);
                backwardSearch(scc);
            }
            cur--;
        }
        else
        {
            aalta_formula *next_af = FormulaProgression(cur_frame.GetFormulaPointer(), *edge_var_set);
            Syn_Frame *next_frame = new Syn_Frame(next_af);

            if (dfn.find((ull) next_frame) == dfn.end())
            {
                dfn.insert({(ull) next_frame, time});
                low.insert({(ull) next_frame, time});
                time++;

                sta.push_back(next_frame);
                cur++;
                prefix_bdd_ptr_set.insert((ull) next_frame->GetBddPointer());
            }
            else if (prefix_bdd_ptr_set.find((ull) next_frame->GetBddPointer()) != prefix_bdd_ptr_set.end())
            {
                low.at((ull)sta[cur]) = min(low.at((ull)sta[cur]), low.at((ull)sta[cur+1]));
            }
        }
    }

    if (TarjanSearch::isSccRoot(cur_frame))
    {
        std::vector<Syn_Frame*> *scc = TarjanSearch::getScc();
        backwardSearch(*scc);
    }
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