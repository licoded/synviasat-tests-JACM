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

void get_edge_var_set(Syn_Frame &cur_frame, unordered_set<int>& edge_var_set);

void forwardSearch(Syn_Frame &cur_frame);
void backwardSearch(std::vector<Syn_Frame*> &scc);


#endif