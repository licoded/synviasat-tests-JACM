#ifndef __FORMULA_IN_BDD__
#define __FORMULA_IN_BDD__

#include <unordered_map>
#include <iostream>

#include "formula/aalta_formula.h"
#include "edge_cons_env.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

aalta_formula *xnf(aalta_formula *af);
aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge);
bool BaseWinningAtY(aalta_formula *end_state, unordered_set<int> &Y);
bool IsAcc(aalta_formula *predecessor, unordered_set<int> &tmp_edge);

class FormulaInBdd
{
private:
    static DdManager *global_bdd_manager_;
    static unordered_map<ull, ull> aaltaP_to_bddP_;
    static unordered_map<int, ull> bddVar_to_aaltaP_;
    static aalta_formula *src_formula_;

    static void CreatedMap4AaltaP2BddP(aalta_formula *af, bool is_xnf);

    // used in CreatedMap4AaltaP2BddP(aalta_formula *af)
    // for \psi\in cl(af), init the map of PA(xnf(\psi))
    static void GetPaOfXnf(aalta_formula *psi);

    aalta_formula *formula_;
    aalta_formula *xnf_formula_;
    DdNode *bdd_;

    static DdNode *ConstructBdd(aalta_formula *af);
    static int X_var_nums, Y_var_nums;
    static bool is_X_var(DdNode* node) { return Cudd_NodeReadIndex(node) >= Y_var_nums && Cudd_NodeReadIndex(node) < Y_var_nums + X_var_nums; }
    static bool is_Y_var(DdNode* node) { return Cudd_NodeReadIndex(node) < Y_var_nums; }
    static bool is_notXY_var(DdNode* node) { return Cudd_NodeReadIndex(node) >= Y_var_nums + X_var_nums; }
    static bool is_Next_var(DdNode* node) { return is_notXY_var(node) && !Cudd_IsConstant(node); }

public:
    static DdNode *TRUE_bddP_;
    static DdNode *FALSE_bddP_;

    static unordered_map<ull, ull> bddP_to_afP;

    static void InitBdd4LTLf(aalta_formula *src_formula, bool is_xnf);
    static void QuitBdd4LTLf() { Cudd_Quit(global_bdd_manager_); }
    static void fixXYOrder(std::set<int> &X_vars, std::set<int> &Y_vars);

    FormulaInBdd(aalta_formula *af) : formula_(af) {
        xnf_formula_ = xnf(af);
        CreatedMap4AaltaP2BddP(xnf_formula_, false);
        bdd_ = ConstructBdd(xnf_formula_);
        cout << af->to_string() << endl;
        cout << xnf_formula_->to_string() << endl;
        cout << (ull)bdd_ << "\t" << bdd_ << endl;
    }
    inline DdNode *GetBddPointer() { return bdd_; }
    inline aalta_formula *GetFormulaPointer() { return formula_; }

    // if (af1 -> af2) in Boolean semantics, it returns true
    static bool Implies(aalta_formula *af1, aalta_formula *af2);
    static bool Implies(DdNode *af1, DdNode *af2);

    static void PrintMapInfo();

private:
    static XCons *get_XCons(DdNode* root, aalta_formula *state_af, aalta_formula *af_Y);

public:
    static EdgeCons *get_EdgeCons(FormulaInBdd *state_in_bdd);
    static aalta_formula *get_afY_from_edgeset(DdNode *root, unordered_set<int> &edge_var_set);
    static bool check_conflict(aalta_formula *af1, aalta_formula *af2);
};

#endif