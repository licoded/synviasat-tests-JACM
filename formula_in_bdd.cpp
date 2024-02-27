#include <iostream>
#include <cassert>

#include "formula_in_bdd.h"
#include "formula/aalta_formula.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

DdManager *FormulaInBdd::global_bdd_manager_ = NULL;
unordered_map<ull, ull> FormulaInBdd::aaltaP_to_bddP_;
unordered_map<int, ull> FormulaInBdd::bddVar_to_aaltaP_;
aalta_formula *FormulaInBdd::src_formula_ = NULL;
DdNode *FormulaInBdd::TRUE_bddP_;
DdNode *FormulaInBdd::FALSE_bddP_;

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

void FormulaInBdd::fixXYOrder(std::set<int> &X_vars, std::set<int> &Y_vars)
{
    X_var_nums = X_vars.size();
    Y_var_nums = Y_vars.size();
    int var_cnt = 0;
    for (auto item : Y_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        bddVar_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode*)(aaltaP_to_bddP_[ull(af)]));
    }
    for (auto item : X_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        bddVar_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode*)(aaltaP_to_bddP_[ull(af)]));
    }
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
        Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(af)]));
        return (DdNode *)(aaltaP_to_bddP_[ull(af)]);
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

bool FormulaInBdd::DFS(DdNode* node, std::unordered_map<DdNode*, int>& visited) {
    if (visited.find(node) != visited.end()) {
        return visited.at(node);
    }

    if (Cudd_IsConstant(node)) {
        if (Cudd_IsComplement(node)) {
            printf("Visiting 0 terminal node\n");
            return true;
        } else {
            printf("Visiting 1 terminal node\n");
            return false;
        }
    } else {
        printf("Visiting node with index %d\n", Cudd_NodeReadIndex(node));
        bool exist_env_win = false;
        /* TODO: note the feature of || will lead to no execution!!! And that's just ok now. */
        exist_env_win = exist_env_win || DFS(Cudd_T(node), visited);  // Traverse the then-child
        exist_env_win = exist_env_win || DFS(Cudd_E(node), visited);  // Traverse the else-child
        visited.insert({node, exist_env_win});
        return exist_env_win;
    }
    cout << "Error: shouldn't reach here!!!" << endl;
}

void FormulaInBdd::DFS_BDD(DdNode* root) {
    if (root == NULL) {
        cout << "Error: root is NULL!!!" << endl;
        return ;
    }
    std::unordered_map<DdNode*, int> visited;
    DFS(root, visited);
}

bool FormulaInBdd::exist_ewin_DFS(DdNode* node, std::unordered_map<DdNode*, bool>& exist_ewin_map)
{
    if (exist_ewin_map.find(node) != exist_ewin_map.end()) {
        return exist_ewin_map.at(node);
    }

    if (Cudd_IsConstant(node)) {
        bool is_Zero_Terminal = Cudd_IsComplement(node);
        exist_ewin_map.insert({node, is_Zero_Terminal});
        return is_Zero_Terminal;
    } else {
        bool exist_env_win = false;
        /* TODO: note the feature of || will lead to no execution!!! And that's just ok now. */
        exist_env_win = exist_env_win || exist_ewin_DFS(Cudd_T(node), exist_ewin_map);  // Traverse the then-child
        exist_env_win = exist_env_win || exist_ewin_DFS(Cudd_E(node), exist_ewin_map);  // Traverse the else-child
        exist_ewin_map.insert({node, exist_env_win});
        return exist_env_win;
    }
}

void FormulaInBdd::get_Y_constraint_DFS(DdNode* node, std::unordered_map<DdNode*, bool>& exist_ewin_map, aalta_formula_wrapper& af_wrapper, aalta_formula* cur_af_Y)
{
    assert(exist_ewin_map.find(node) != exist_ewin_map.end());
    if (exist_ewin_map.at(node))
        return;
    if (is_X_var(node)) {
        af_wrapper.af = aalta_formula(aalta_formula::Or, af_wrapper.af, cur_af_Y).unique();
    } else {
        aalta_formula *cur_Y = (aalta_formula*)bddVar_to_aaltaP_[Cudd_NodeReadIndex(node)];
        aalta_formula *not_cur_Y = aalta_formula(aalta_formula::Not, NULL, cur_Y).unique();
        get_Y_constraint_DFS(Cudd_T(node), exist_ewin_map, af_wrapper, aalta_formula(aalta_formula::And, cur_af_Y, cur_Y).unique());
        get_Y_constraint_DFS(Cudd_E(node), exist_ewin_map, af_wrapper, aalta_formula(aalta_formula::And, cur_af_Y, not_cur_Y).unique());
    }
}

aalta_formula *FormulaInBdd::get_Y_constraint(DdNode* root)
{
    assert(root != NULL);
    std::unordered_map<DdNode*, bool> exist_ewin_map;
    exist_ewin_DFS(root, exist_ewin_map);
    aalta_formula_wrapper Y_constraint_wrapper = aalta_formula_wrapper(aalta_formula::FALSE());
    get_Y_constraint_DFS(root, exist_ewin_map, Y_constraint_wrapper, aalta_formula::TRUE());
    return Y_constraint_wrapper.af;
}

void FormulaInBdd::PrintMapInfo()
{
    cout << "src formula:" << src_formula_->to_string() << "\nPropositional Atoms:\n";
    for (auto it = FormulaInBdd::aaltaP_to_bddP_.begin(); it != FormulaInBdd::aaltaP_to_bddP_.end(); ++it)
        cout << ((aalta_formula *)(it->first))->to_string() << endl;
}