#ifndef __DFS_SEARCH__
#define __DFS_SEARCH__

#include <unordered_map>

#include "formula/aalta_formula.h"
#include "synthesis.h"
#include "edge_cons.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

class TarjanSearch
{
public:
    static bool isSccRoot(Syn_Frame syn_frame);
    static std::vector<Syn_Frame*> *getScc();

    static unordered_map<ull, int> dfn;
    static unordered_map<ull, int> low;
    static int time;

    static void tarjan_search_init();

private:

};

bool get_edge_var_set(Syn_Frame *cur_frame, unordered_set<int>& edge_var_set);
void getScc(int cur, std::vector<Syn_Frame*> &scc, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta, unordered_map<ull, int>& prefix_bdd2curIdx_map, unordered_map<ull, int>& sta_bdd2curIdx_map);
bool sccRoot_isNone(Syn_Frame *cur_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low, vector<Syn_Frame *> &sta);

void initial_cur_frame(Syn_Frame *cur_frame, int &time, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low);
void update_by_low(Syn_Frame *cur_frame, DdNode *next_bddP, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low);
void update_by_dfn(Syn_Frame *cur_frame, Syn_Frame *next_frame, unordered_map<ull, int> &dfn, unordered_map<ull, int> &low);

bool forwardSearch(Syn_Frame *cur_frame);
void backwardSearch(std::vector<Syn_Frame*> &scc);


#endif