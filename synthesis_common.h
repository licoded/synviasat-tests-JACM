#ifndef __SYNTHESIS_COMMON__
#define __SYNTHESIS_COMMON__

#include <set>

using namespace std;

typedef enum
{
    Unknown,
    Realizable,
    Unrealizable
} Status;

typedef enum
{
    To_winning_state,
    To_failure_state,
    Accepting_edge,
    NoWay,
    // for Y, there is some X such that \delta(s,X\cup Y) has no successor
    Incomplete_Y
} Signal;

typedef enum
{
    SAT_Trace,
    One_Step,
} SearchMode;

class Syn_Common
{
public:
    // number of variables
    static int num_varX_;
    static int num_varY_;

    // set of X- Y- variables
    static set<int> var_X;
    static set<int> var_Y;
};

#endif