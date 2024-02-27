#ifndef __FORMULA_IN_BDD__
#define __FORMULA_IN_BDD__

#include <unordered_map>

#include "formula/aalta_formula.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

class FormulaInBdd
{
private:
    static DdManager *global_bdd_manager_;
    static unordered_map<ull, ull> aaltaP_to_bddP_;
    static unordered_map<int, ull> bddVar_to_aaltaP_;
    static aalta_formula *src_formula_;

    // used in CreatedMap4AaltaP2BddP(aalta_formula *af)
    // for \psi\in cl(af), init the map of PA(xnf(\psi))
    static void GetPaOfXnf(aalta_formula *psi);

    aalta_formula *formula_;
    DdNode *bdd_;

    static DdNode *ConstructBdd(aalta_formula *af);
    static bool DFS(DdNode* node, std::unordered_map<DdNode*, int>& visited);
    static bool exist_ewin_DFS(DdNode* node, std::unordered_map<DdNode*, bool>& exist_ewin_map);
    static void get_Y_constraint_DFS(DdNode* node, std::unordered_map<DdNode*, bool>& exist_ewin_map, aalta_formula_wrapper& af_wrapper, aalta_formula* cur_af_Y);

    static int X_var_nums, Y_var_nums;
    static bool is_X_var(DdNode* node) { return Cudd_NodeReadIndex(node) >= Y_var_nums && Cudd_NodeReadIndex(node) < X_var_nums + Y_var_nums; };
    static bool is_Y_var(DdNode* node) { return Cudd_NodeReadIndex(node) < Y_var_nums; };

public:
    static DdNode *TRUE_bddP_;
    static DdNode *FALSE_bddP_;

    static void InitBdd4LTLf(aalta_formula *src_formula, bool is_xnf);
    static void QuitBdd4LTLf() { Cudd_Quit(global_bdd_manager_); }

    static void fixXYOrder(std::set<int> &X_vars, std::set<int> &Y_vars);
    static void CreatedMap4AaltaP2BddP(aalta_formula *af, bool is_xnf);

    FormulaInBdd(aalta_formula *af) : formula_(af) { bdd_ = ConstructBdd(af); }
    inline DdNode *GetBddPointer() { return bdd_; }
    inline aalta_formula *GetFormulaPointer() { return formula_; }

    // if (af1 -> af2) in Boolean semantics, it returns true
    static bool Implies(aalta_formula *af1, aalta_formula *af2);
    static bool Implies(DdNode *af1, DdNode *af2);

    static void DFS_BDD(DdNode* root);
    static aalta_formula *get_Y_constraint(DdNode* root);

    static void PrintMapInfo();
};

#endif