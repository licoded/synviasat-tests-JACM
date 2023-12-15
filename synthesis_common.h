#ifndef __SYNTHESIS_COMMON__
#define __SYNTHESIS_COMMON__

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

#endif