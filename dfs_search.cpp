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
    Syn_Frame::fill_in_edgeset(edge_var_set);
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
    queue<aalta_formula*> model;
    while (cur >= 0)
    {
        Status cur_state_status = sta[cur]->checkStatus();
        bool decided_flag = cur_state_status != Status::Unknown;
        // TODO: add undetermined_serachdone flag back!!!
        dout << cur << "\t" << cur_state_status << "\t" << decided_flag << "\t" << endl;
        if (decided_flag)    // Undetermined state maybe not searched done!!!
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
                while (!model.empty())
                    model.pop();

                update_by_low(sta[cur], next_bddP, dfn, low);
                continue;
            }
        }

        unordered_set<int> edge_var_set;
        /* TODO: repalce exp in if with following line? */
        // assert(get_edge_var_set(sta[cur], edge_var_set));
        // if no edge, break!!!

        bool exist_edge_to_explorer = false;
        if (Syn_Frame::sat_trace_flag)
        {
            while (!exist_edge_to_explorer && cur_state_status != Status::Unrealizable) {
                exist_edge_to_explorer = getEdge(model, sta[cur], edge_var_set);
                dout << "=== check_conflict ===" << endl;
                dout << "\t" << sta[cur]->current_Y_->to_string() << endl;
                dout << "\t" << sta[cur]->edgeCons_->get_fixed_edge_cons()->to_string() << endl;

                if (!exist_edge_to_explorer)    /* UNSAT -> block current_Y_, TODO: whether need to create a new func? */
                {
                    sta[cur]->edgeCons_->update_fixed_edge_cons(sta[cur]->current_Y_, sta[cur]->current_next_stateid_, Status::Unrealizable);
                    cur_state_status = sta[cur]->checkStatus();
                }
            }
        }
        else
            exist_edge_to_explorer = get_edge_var_set(sta[cur], edge_var_set);

        if (!exist_edge_to_explorer)
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
            while (!model.empty())
                model.pop();
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
                     * TODO: if it is a self loop, just block current edge!!!
                     *          for sys-first, we can block current_Y_
                     *          for env-first, we can only block current_Y_ (env vars) --> current_X_
                    */
                    /**
                     * cur_Y has X -> prefix, cannot make cur_state undetermined
                     * only all Y has X -> prefix, can make cur_state undetermined
                    */
                    // sta[cur]->edgeCons_->update_fixed_edge_cons_repeat_prefix(sta[cur]->current_Y_, (ull)next_frame->GetBddPointer());
                    sta[cur]->edgeCons_->update_fixed_edge_cons_repeat_prefix(sta[cur]->current_Y_, sta[cur]->current_next_stateid_);
                    while (!model.empty())
                        model.pop();
                }
                else    // else: has cur-- (moved backward)
                {
                    Status next_state_status = next_frame->checkStatus();
                    /* Because it has cur-- (moved backward), so it must have finished its search!!! */
                    assert(next_state_status != Status::Unknown);   // if not OK, create bdd_to_status_map_
                    sta[cur]->edgeCons_->update_fixed_edge_cons(sta[cur]->current_Y_, ull(next_frame->GetBddPointer()), next_state_status);
                    while (!model.empty())
                        model.pop();
                    /*
                     * TODO: whether modify ull(next_frame->GetBddPointer()) back to sta[cur]->current_next_stateid_?
                     *              need assign sta[cur]->current_next_stateid_ in getEdge!!!
                     */
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
    // for (int i = scc.size(); i > 0; i--)
    // {
    //     auto it = scc[i-1];
    //     if (Syn_Frame::inUndeterminedState(it->GetBddPointer()))
    //     {
    //         Syn_Frame::setEwinState(it);
    //     }
    //     delete it;
    // }

    using afY_to_afX_map = unordered_map<aalta_formula *, aalta_formula *>;
    using state_to_edge_map = unordered_map<ull, afY_to_afX_map*>;

    unordered_map<int, state_to_edge_map *> state_to_edge_map_map;
    for (int i = 0; i < scc.size(); i++)
    {
        auto it = scc[i];
        if (Syn_Frame::inSwinSet(it->GetBddPointer()) || Syn_Frame::inEwinSet(it->GetBddPointer()))
            continue;
        
        dout << "=== state_to_edge_map_map ===\n";

        aalta_formula *af_state = it->GetFormulaPointer();
        EdgeCons *edgeCons = it->edgeCons_;
        state_to_edge_map *state_to_edge_map_ = new state_to_edge_map();

        for (auto it2 = edgeCons->afY_Xcons_pairs_undecided_.begin(); it2 != edgeCons->afY_Xcons_pairs_undecided_.end(); it2++)
        {
            aalta_formula *af_Y = it2->first;
            for (auto it3 = it2->second->undecided_afX_state_pairs_.begin(); it3 != it2->second->undecided_afX_state_pairs_.end(); it3++)
            {
                aalta_formula *af_X = *(it3->second->to_or_set().begin());
                aalta_formula *edge = aalta_formula(aalta_formula::And, af_Y, af_X).unique();
                unordered_set<int> tmp_edge;
                edge->to_set(tmp_edge);
                aalta_formula *next_af = FormulaProgression(af_state, tmp_edge);
                DdNode *next_bddP = FormulaInBdd(next_af).GetBddPointer();
                int next_stateid = ull(next_bddP);
                if (state_to_edge_map_->find(next_stateid) == state_to_edge_map_->end())
                {
                    state_to_edge_map_->insert({next_stateid, new afY_to_afX_map()});
                }
                state_to_edge_map_->at(next_stateid)->insert({af_Y, it3->second});
                dout << "\n\tnext_stateid: " << ull(next_stateid)
                    << "\n\tnext_af: " << next_af->to_string()
                    << "\n\taf_Y: " << af_Y->to_string()
                    << "\n\taf_X: " << af_X->to_string()
                    << endl;
            }
        }
        state_to_edge_map_map.insert({i, state_to_edge_map_});
    }

    unordered_set<ull> cur_swin = Syn_Frame::swin_state;
    dout << "=== cur_swin ===\n";
    for (auto it = scc.begin(); it != scc.end(); it++)
    {
        if (Syn_Frame::inSwinSet((*it)->GetBddPointer()))
        {
            cur_swin.insert(ull((*it)->GetBddPointer()));
            dout << "\t" << (*it)->GetFormulaPointer()->to_string()
                << "\n\t" << ull((*it)->GetBddPointer())
                << endl;
        }
    }

    do {
        for (auto it : cur_swin)
        {
            for (auto it2 : state_to_edge_map_map)
            {
                auto it2_Iter = it2.second->find(it);
                if (it2_Iter != it2.second->end())
                {
                    for (auto it3 : *(it2_Iter->second))
                    {
                        aalta_formula *af_Y = it3.first;
                        aalta_formula *af_X = it3.second;
                        dout << "update\t\n\t"
                            << "cur_state: " << scc[it2.first]->GetFormulaPointer()->to_string() << "\n\t"
                            << "af_Y: " << af_Y->to_string() << "\n\t"
                            << "af_X: " << af_X->to_string() << "\n\t"
                            << endl;
                        scc[it2.first]->edgeCons_->update_fixed_edge_cons(af_Y, it, Status::Realizable);
                    }
                }
            }
        }
        
        unordered_set<ull> new_swin;
        for (auto it = state_to_edge_map_map.begin(); it != state_to_edge_map_map.end(); ) 
        {
            Syn_Frame *cur_frame = scc[it->first];
            if (cur_frame->checkStatus() == Status::Realizable)
            {
                delete it->second;
                it = state_to_edge_map_map.erase(it);
                new_swin.insert(ull(cur_frame->GetBddPointer()));
                Syn_Frame::setEwinState(cur_frame);
            }
            else
                it++;
        }

        // clear cur_swin and update it with new_swin
        cur_swin.clear();
        if (new_swin.empty())
            break;
        dout << "new_swin.size() = " << new_swin.size() << endl;
        cur_swin = new_swin;
    } while(true);

    // set all remain undecided/undetermined states as ewin
    for (auto it : state_to_edge_map_map)
    {
        Syn_Frame::setEwinState(scc[it.first]);
    }

    // free memory
    for (auto it : scc)
    {
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

bool getEdge(queue<aalta_formula*> &model /* edges */, Syn_Frame *cur_frame, unordered_set<int>& edge_var_set)
{
    bool isTraceBeginning = false;
    if (model.empty())
    {
        /* STEP1: assign current_Y/X */
        cur_frame->current_Y_ = cur_frame->edgeCons_->choose_afY();
        if (cur_frame->current_Y_ == NULL)
            return false;
        shared_ptr<afX_state_pair> chosen_afX_state_pair(cur_frame->edgeCons_->choose_afX(cur_frame->current_Y_));
        if (chosen_afX_state_pair == NULL)
            return false;
        cur_frame->current_X_ = chosen_afX_state_pair->first;
        cur_frame->current_next_stateid_ = chosen_afX_state_pair->second;

        /* STEP2: construct edge_constraint for checker */
        aalta_formula *edge_af = aalta_formula(aalta_formula::And, cur_frame->current_Y_, cur_frame->current_X_).unique();
        edge_af = edge_af->simplify();
        dout << edge_af->to_string() << endl;

        /* STEP3: construct and run checker to get SAT trace */
        aalta_formula *state = cur_frame->GetFormulaPointer();
        aalta_formula *to_check = aalta_formula(aalta_formula::And, state, edge_af).unique();
        to_check = aalta_formula(aalta_formula::And, to_check, cur_frame->edgeCons_->get_fixed_edge_cons()).unique();
        to_check = to_check->add_tail();
        to_check = to_check->remove_wnext();
        to_check = to_check->simplify();
        to_check = to_check->split_next();
        CARChecker checker(to_check, false, true);

        dout << "=== to_check: " << to_check->to_string() << endl;
        if (checker.check())
        {
            /* STEP4: copy model from checker.evidence */
            isTraceBeginning = true;
            std::vector<std::pair<aalta_formula *, aalta_formula *>> *evidence(checker.get_model_for_synthesis());
            dout << "=== evidence ===" << endl;
            for (auto it = evidence->begin(); it != evidence->end(); it++)
            {
                model.push(it->first);
                dout << "\t" << it->first->to_string() << endl;
            }
        }
        else
            return false;
    }

    assert(!model.empty());
    aalta_formula *edge_af = model.front();
    model.pop();
    dout << edge_af->to_string() << endl;
    edge_af->to_set(edge_var_set);
    if (!isTraceBeginning)
        cur_frame->current_Y_ = FormulaInBdd::get_afY_from_edgeset(cur_frame->GetBddPointer(), edge_var_set);
    Syn_Frame::fill_in_edgeset(edge_var_set);
    return true;
}
