#include <iostream>
#include <cassert>
#include <queue>

#include "formula_in_bdd.h"
#include "formula/aalta_formula.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

DdManager *FormulaInBdd::global_bdd_manager_ = NULL;
unordered_map<ull, ull> FormulaInBdd::aaltaP_to_bddP_;
unordered_map<ull, ull> FormulaInBdd::bddP_to_afP;
unordered_map<int, ull> FormulaInBdd::bddVar_to_aaltaP_;
aalta_formula *FormulaInBdd::src_formula_ = NULL;
DdNode *FormulaInBdd::TRUE_bddP_;
DdNode *FormulaInBdd::FALSE_bddP_;
int FormulaInBdd::X_var_nums;
int FormulaInBdd::Y_var_nums;

aalta_formula *xnf(aalta_formula *phi)
{
    if (phi == NULL)
        return NULL;
    int op = phi->oper();
    if ((op == aalta_formula::True || op == aalta_formula::False) || op == aalta_formula::Not || (op == aalta_formula::Next || op == aalta_formula::WNext) || op >= 11)
    {
        return phi;
    }
    if (op == aalta_formula::And || op == aalta_formula::Or)
    {
        return aalta_formula(op, xnf(phi->l_af()), xnf(phi->r_af())).unique();
    }
    else if (op == aalta_formula::Until)
    { // l U r=xnf(r) | (xnf(l) & X(l U r))
        aalta_formula *next_phi = aalta_formula(aalta_formula::Next, NULL, phi).unique();
        aalta_formula *xnf_l_and_next_phi = aalta_formula(aalta_formula::And, xnf(phi->l_af()), next_phi).unique();
        return aalta_formula(aalta_formula::Or, xnf(phi->r_af()), xnf_l_and_next_phi).unique();
    }
    else if (op == aalta_formula::Release)
    { // l R r=xnf(r) & (xnf(l) | WX(l R r))
        aalta_formula *wnext_phi = aalta_formula(aalta_formula::WNext, NULL, phi).unique();
        aalta_formula *xnf_l_or_wnext_phi = aalta_formula(aalta_formula::Or, xnf(phi->l_af()), wnext_phi).unique();
        return aalta_formula(aalta_formula::And, xnf(phi->r_af()), xnf_l_or_wnext_phi).unique();
    }
}

void FormulaInBdd::InitBdd4LTLf(aalta_formula *src_formula, bool is_xnf)
{
    src_formula_ = src_formula;
    global_bdd_manager_ = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    TRUE_bddP_ = Cudd_ReadOne(global_bdd_manager_);
    FALSE_bddP_ = Cudd_ReadLogicZero(global_bdd_manager_);
    Cudd_Ref(TRUE_bddP_);
    Cudd_Ref(FALSE_bddP_);
    // PrintMapInfo();
}

void FormulaInBdd::CreatedMap4AaltaP2BddP(aalta_formula *af, bool is_xnf)
{
    if (af == NULL)
        return;
    int op = af->oper();
    if (op == aalta_formula::True || op == aalta_formula::False)
        return;
    if (op == aalta_formula::And || op == aalta_formula::Or)
    {
        CreatedMap4AaltaP2BddP(af->l_af(), is_xnf);
        CreatedMap4AaltaP2BddP(af->r_af(), is_xnf);
        return;
    }
    if (op == aalta_formula::Not)
    {
        CreatedMap4AaltaP2BddP(af->r_af(), is_xnf);
        return;
    }
    af = af->unique();
    if (is_xnf)
        GetPaOfXnf(af);
    else
    {
        if (aaltaP_to_bddP_.find(ull(af)) == aaltaP_to_bddP_.end())
        {
            aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
            bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
            {
                // add bddP_to_afP for !af
                DdNode *tmp = Cudd_Not((DdNode*)(aaltaP_to_bddP_[ull(af)]));
                bddP_to_afP[(ull)tmp] = af->oper() == aalta_formula::Not
                    ? ull(af->r_af())
                    : ull(aalta_formula(aalta_formula::Not, NULL, af).unique());
            }
            Cudd_Ref((DdNode*)(aaltaP_to_bddP_[ull(af)]));
        }
    }
    if (op == aalta_formula::Next || op == aalta_formula::WNext)
    {
        CreatedMap4AaltaP2BddP(af->r_af(), is_xnf);
        return;
    }
    else if (op == aalta_formula::Until || op == aalta_formula::Release)
    {
        CreatedMap4AaltaP2BddP(af->l_af(), is_xnf);
        CreatedMap4AaltaP2BddP(af->r_af(), is_xnf);
        return;
    }
    else if (op >= 11)
    {
        return;
    }
}

void FormulaInBdd::GetPaOfXnf(aalta_formula *psi)
{
    if (psi == NULL)
        return;
    int op = psi->oper();
    assert(op != aalta_formula::True && op != aalta_formula::False);
    assert(op != aalta_formula::And && op != aalta_formula::Or && op != aalta_formula::Not);
    if (op == aalta_formula::Next || op == aalta_formula::WNext || op >= 11)
    {
        if (aaltaP_to_bddP_.find(ull(psi)) == aaltaP_to_bddP_.end())
            aaltaP_to_bddP_[ull(psi)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        return;
    }
    else if (op == aalta_formula::Until)
    {
        // X_U=X(psi)
        aalta_formula *X_U = aalta_formula(aalta_formula::Next, NULL, psi).unique();
        if (aaltaP_to_bddP_.find(ull(X_U)) == aaltaP_to_bddP_.end())
            aaltaP_to_bddP_[ull(X_U)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        return;
    }
    else if (op == aalta_formula::Release)
    {
        // N_R=N(psi)
        aalta_formula *N_R = aalta_formula(aalta_formula::WNext, NULL, psi).unique();
        if (aaltaP_to_bddP_.find(ull(N_R)) == aaltaP_to_bddP_.end())
            aaltaP_to_bddP_[ull(N_R)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        return;
    }
}

void FormulaInBdd::fixXYOrder(std::set<int> &X_vars, std::set<int> &Y_vars)
{
    X_var_nums = X_vars.size();
    Y_var_nums = Y_vars.size();
    int var_cnt = 0;
    for (auto item : Y_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
        DdNode *ithVar = Cudd_bddIthVar(global_bdd_manager_, var_cnt);
        assert(ithVar == (DdNode*)(aaltaP_to_bddP_[ull(af)]));
        bddVar_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode*)(aaltaP_to_bddP_[ull(af)]));
    }
    for (auto item : X_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
        DdNode *ithVar = Cudd_bddIthVar(global_bdd_manager_, var_cnt);
        assert(ithVar == (DdNode*)(aaltaP_to_bddP_[ull(af)]));
        bddVar_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode*)(aaltaP_to_bddP_[ull(af)]));
    }
}

DdNode *FormulaInBdd::ConstructBdd(aalta_formula *af)
{
    if (af == NULL)
        return NULL;
    int op = af->oper();
    if (op == aalta_formula::True)
    {
        Cudd_Ref(TRUE_bddP_);
        return TRUE_bddP_;
    }
    else if (op == aalta_formula::False)
    {
        Cudd_Ref(FALSE_bddP_);
        return FALSE_bddP_;
    }
    else if (op == aalta_formula::Not)
    {
        DdNode *tmp = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_Not(tmp);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmp);
        return cur;
    }
    else if (op == aalta_formula::Or)
    {
        DdNode *tmpL = ConstructBdd(af->l_af());
        DdNode *tmpR = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_bddOr(global_bdd_manager_, tmpL, tmpR);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpL);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpR);
        return cur;
    }
    else if (op == aalta_formula::And)
    {
        DdNode *tmpL = ConstructBdd(af->l_af());
        DdNode *tmpR = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_bddAnd(global_bdd_manager_, tmpL, tmpR);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpL);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpR);
        return cur;
    }
    else
    {
        DdNode *cur_bdd_ptr = (DdNode *)(aaltaP_to_bddP_[ull(af)]);
        Cudd_Ref(cur_bdd_ptr);
        return cur_bdd_ptr;
    }
}

// check whether af1 implies af2
bool FormulaInBdd::Implies(aalta_formula *af1, aalta_formula *af2)
{
    DdNode *f1 = ConstructBdd(af1);
    DdNode *f2 = ConstructBdd(af2);
    DdNode *not_f2 = Cudd_Not(f2);
    Cudd_Ref(not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f2);
    DdNode *f1_and_not_f2 = Cudd_bddAnd(global_bdd_manager_, f1, not_f2);
    Cudd_Ref(f1_and_not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1);
    Cudd_RecursiveDeref(global_bdd_manager_, not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1_and_not_f2);
    return (f1_and_not_f2 == FALSE_bddP_);
}

bool FormulaInBdd::Implies(DdNode *f1, DdNode *f2)
{
    DdNode *not_f2 = Cudd_Not(f2);
    Cudd_Ref(not_f2);
    DdNode *f1_and_not_f2 = Cudd_bddAnd(global_bdd_manager_, f1, not_f2);
    Cudd_Ref(f1_and_not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1_and_not_f2);
    return (f1_and_not_f2 == FALSE_bddP_);
}

void FormulaInBdd::PrintMapInfo()
{
    cout << "src formula:" << src_formula_->to_string() << "\nPropositional Atoms:\n";
    for (auto it = FormulaInBdd::aaltaP_to_bddP_.begin(); it != FormulaInBdd::aaltaP_to_bddP_.end(); ++it)
        cout << ((aalta_formula *)(it->first))->to_string() << endl;
}

void FormulaInBdd::get_EdgeCons_DFS(DdNode* node, aalta_formula* af_Y, std::unordered_map<DdNode*, shared_ptr<XCons>>& bdd_XCons_map, EdgeCons& edgeCons, bool is_complement)
{
    if (!is_Y_var(node))
    {
        DdNode *true_node = is_complement ? Cudd_Not(node) : node;
        shared_ptr<XCons> xCons;
        if (bdd_XCons_map.find(true_node) == bdd_XCons_map.end())
        {
            shared_ptr<XCons> xCons_(get_XCons(true_node));
            bdd_XCons_map.insert({true_node, xCons_});
        }
        xCons = bdd_XCons_map.at(true_node);

        assert(af_Y != NULL);
        edgeCons.afY_Xcons_pairs_.push_back({af_Y, xCons});
        return;
    }
    
    aalta_formula *cur_Y = (aalta_formula*)bddVar_to_aaltaP_[Cudd_NodeReadIndex(node)];
    aalta_formula *not_cur_Y = aalta_formula(aalta_formula::Not, NULL, cur_Y).unique();
    aalta_formula *T_afY = af_Y == NULL ? cur_Y : aalta_formula(aalta_formula::And, af_Y, cur_Y).unique();
    aalta_formula *E_afY = af_Y == NULL ? not_cur_Y : aalta_formula(aalta_formula::And, af_Y, not_cur_Y).unique();

    get_EdgeCons_DFS(Cudd_T(node), T_afY, bdd_XCons_map, edgeCons, is_complement ^ Cudd_IsComplement(node));
    get_EdgeCons_DFS(Cudd_E(node), E_afY, bdd_XCons_map, edgeCons, is_complement ^ Cudd_IsComplement(node));
}

EdgeCons *FormulaInBdd::get_EdgeCons(DdNode* root)
{
    EdgeCons *edgeCons = new EdgeCons();
    std::unordered_map<DdNode*, shared_ptr<XCons>> bdd_XCons_map;
    get_EdgeCons_DFS(root, aalta_formula::TRUE(), bdd_XCons_map, *edgeCons, false);
    return edgeCons;
}

EdgeCons *FormulaInBdd::get_EdgeCons(FormulaInBdd *state_in_bdd)
{
    EdgeCons *edgeCons = new EdgeCons();
    std::unordered_map<DdNode*, shared_ptr<XCons>> bdd_XCons_map;

    aalta_formula *root_af = state_in_bdd->GetFormulaPointer();
    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    q.push({state_in_bdd->GetBddPointer(), aalta_formula::TRUE(), false});

    while (!q.empty())    /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.back());
        aalta_formula *af_Y = std::get<1>(q.back());
        bool is_complement = std::get<2>(q.back());
        q.pop();

        if (!is_Y_var(node))
        {
            DdNode *true_node = is_complement ? Cudd_Not(node) : node;
            shared_ptr<XCons> xCons;

            // if (true /* TODO: replace it with env_first_flag! */)
            // {
            //     if (has_win_edge(root_af, af_Y))
            //     {
            //         /* if has Y_win_edge (only check TRUE, omitting other swin state), we don't need to record/insert in edgeCons.afY_Xcons_pairs_ */
            //         continue;
            //     }
            // }

            if (bdd_XCons_map.find(true_node) == bdd_XCons_map.end())
            {
                shared_ptr<XCons> xCons_(get_XCons(true_node));
                bdd_XCons_map.insert({true_node, xCons_});
            }
            xCons = bdd_XCons_map.at(true_node);

            /* TODO: if exist swin state, don't record/insert in edgeCons.afY_Xcons_pairs_, when with env_first_flag*/

            assert(af_Y != NULL);
            edgeCons->afY_Xcons_pairs_.push_back({af_Y, xCons});
            continue;
        }

        aalta_formula *cur_Y = (aalta_formula*)bddVar_to_aaltaP_[Cudd_NodeReadIndex(node)];
        aalta_formula *not_cur_Y = aalta_formula(aalta_formula::Not, NULL, cur_Y).unique();
        aalta_formula *T_afY = af_Y == NULL ? cur_Y : aalta_formula(aalta_formula::And, af_Y, cur_Y).unique();
        aalta_formula *E_afY = af_Y == NULL ? not_cur_Y : aalta_formula(aalta_formula::And, af_Y, not_cur_Y).unique();

        q.push({Cudd_T(node), T_afY, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afY, is_complement ^ Cudd_IsComplement(node)});
    }

    return edgeCons;
}

void FormulaInBdd::get_XCons_DFS(DdNode* node, aalta_formula* af_X, XCons& xCons, bool is_complement)
{
    if (!is_X_var(node))
    {
        DdNode *true_node = is_complement ? Cudd_Not(node) : node;
        ull state_id = ull(true_node);
        if (xCons.state2afX_map_.find(state_id) == xCons.state2afX_map_.end())
            xCons.state2afX_map_.insert({state_id, af_X});
        else
            xCons.state2afX_map_.at(state_id) = aalta_formula(aalta_formula::Or, xCons.state2afX_map_.at(state_id), af_X).unique();
        return;
    }

    aalta_formula *cur_X = (aalta_formula*)bddVar_to_aaltaP_[Cudd_NodeReadIndex(node)];
    aalta_formula *not_cur_X = aalta_formula(aalta_formula::Not, NULL, cur_X).unique();
    aalta_formula *T_afX = af_X == NULL ? cur_X : aalta_formula(aalta_formula::And, af_X, cur_X).unique();
    aalta_formula *E_afX = af_X == NULL ? not_cur_X : aalta_formula(aalta_formula::And, af_X, not_cur_X).unique();

    get_XCons_DFS(Cudd_T(node), T_afX, xCons, is_complement ^ Cudd_IsComplement(node));
    get_XCons_DFS(Cudd_E(node), E_afX, xCons, is_complement ^ Cudd_IsComplement(node)); 
}

// XCons *FormulaInBdd::get_XCons(DdNode* root)
// {
//     XCons *xCons = new XCons();     // TODO: whether need to modify to shared_ptr???
//     get_XCons_DFS(root, NULL, *xCons, false);
//     return xCons;
// }

XCons *FormulaInBdd::get_XCons(DdNode* root)
{
    XCons *xCons = new XCons();     // TODO: whether need to modify to shared_ptr???

    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    q.push({root, aalta_formula::TRUE(), false});

    while (!q.empty())    /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.back());
        aalta_formula *af_X = std::get<1>(q.back());
        bool is_complement = std::get<2>(q.back());
        q.pop();

        if (!is_X_var(node))
        {
            DdNode *true_node = is_complement ? Cudd_Not(node) : node;
            ull state_id = ull(true_node);
            if (xCons->state2afX_map_.find(state_id) == xCons->state2afX_map_.end())
                xCons->state2afX_map_.insert({state_id, af_X});
            else
                xCons->state2afX_map_.at(state_id) = aalta_formula(aalta_formula::Or, xCons->state2afX_map_.at(state_id), af_X).unique();
            continue;
        }

        aalta_formula *cur_X = (aalta_formula*)bddVar_to_aaltaP_[Cudd_NodeReadIndex(node)];
        aalta_formula *not_cur_X = aalta_formula(aalta_formula::Not, NULL, cur_X).unique();
        aalta_formula *T_afX = af_X == NULL ? cur_X : aalta_formula(aalta_formula::And, af_X, cur_X).unique();
        aalta_formula *E_afX = af_X == NULL ? not_cur_X : aalta_formula(aalta_formula::And, af_X, not_cur_X).unique();

        q.push({Cudd_T(node), T_afX, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afX, is_complement ^ Cudd_IsComplement(node)});
    }

    return xCons;
}

/* suppose current is tail (the last state/transition) */
aalta_formula *reduce_state_with_tail(aalta_formula *af)
{
    if (af == NULL)
        return NULL;

    aalta_formula *res, *l, *r;
    switch (af->oper())
    {
    case aalta_formula::WNext:
        return aalta_formula::TRUE();
        break;

    case aalta_formula::Next:
        return aalta_formula::FALSE();
        break;

    case aalta_formula::Until:
        l = reduce_state_with_tail(af->l_af());
        r = reduce_state_with_tail(af->r_af());
        res = aalta_formula(aalta_formula::Or, l, r).unique();
        return res;
        break;

    case aalta_formula::Release:
        res = reduce_state_with_tail(af->r_af());
        return res;
        break;

    // case aalta_formula::Global:
    // no Global oper!!! It is represented by false R phi in aalta_formula

    default:    /* others */
        l = reduce_state_with_tail(af->l_af());
        r = reduce_state_with_tail(af->r_af());
		res = aalta_formula(af->oper(), l, r).unique ();
        return res;
        // cerr << "shouldn't reach here!" << endl;
        // exit(1);
        break;
    }
}

/* this func only consider TRUE, omitting other swin states */
bool has_win_edge(aalta_formula *state, aalta_formula *afY /*env_edge*/ )
{
    aalta_formula *state_and_afY = aalta_formula(aalta_formula::And, state, afY).unique();
    aalta_formula *state_and_afY_with_tail = reduce_state_with_tail(state_and_afY);
    shared_ptr<FormulaInBdd> state_and_afY_with_tail_in_bdd(new FormulaInBdd(state_and_afY_with_tail));
    return state_and_afY_with_tail_in_bdd->GetBddPointer() != FormulaInBdd::FALSE_bddP_;
}