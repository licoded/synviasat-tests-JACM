#include "dfs_search.h"

void forwardSearch(Syn_Frame &cur_frame)
{
    while (Syn_Frame::checkStatus(cur_frame) != Status::Unknown)
    {
        unordered_set<int> *edge_var_set;
        get_edge_var_set(cur_frame, *edge_var_set);

        // if no edge, break!!!
        if (edge_var_set == NULL)
            break;
        
        aalta_formula *next_af = FormulaProgression(cur_frame.GetFormulaPointer(), *edge_var_set);
        Syn_Frame next_frame(next_af);

        if (Syn_Frame::isUndeterminedState(next_frame))
            continue;
        
        forwardSearch(next_frame);
    }

    if (TarjanSearch::isSccRoot(cur_frame))
    {
        std::vector<Syn_Frame*> *scc = TarjanSearch::getScc();
        backwardSearch(scc);
    }
}