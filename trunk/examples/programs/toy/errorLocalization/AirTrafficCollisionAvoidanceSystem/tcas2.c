#include <stdio.h>

int nondet_int (void) 
{
  int nd;
  return nd;
}


#define OLEV       600		/* in feets/minute */
#define MAXALTDIFF 600		/* max altitude difference in feet */
#define MINSEP     300          /* min separation in feet */
#define NOZCROSS   100		/* in feet */
				/* variables */

typedef int bool;

int Cur_Vertical_Sep;
int High_Confidence;
bool Two_of_Three_Reports_Valid;
int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate;
int Other_Tracked_Alt;
int Alt_Layer_Value;		/* 0, 1, 2, 3 */
int Positive_RA_Alt_Thresh_0;
int Positive_RA_Alt_Thresh_1;
int Positive_RA_Alt_Thresh_2;
int Positive_RA_Alt_Thresh_3;
int Up_Separation;
int Down_Separation;

				/* state variables */
int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
#define NO_INTENT 0
#define DO_NOT_CLIMB 1
#define DO_NOT_DESCEND 2

int Other_Capability;		/* TCAS_TA, OTHER */
#define TCAS_TA 1
#define OTHER 2

int Climb_Inhibit;		/* true/false */

#define UNRESOLVED 0
#define UPWARD_RA 1
#define DOWNWARD_RA 2

int Positive_RA_Alt_Thresh(int Alt)
{
  int res = 0;
  if( Alt == 0 )
    { res = Positive_RA_Alt_Thresh_0; }
  if( Alt == 1 )
    { res = Positive_RA_Alt_Thresh_1; }
  if( Alt == 2 )
    { res = Positive_RA_Alt_Thresh_2; }
  if( Alt == 3 )
    { res = Positive_RA_Alt_Thresh_3; }
  return(res);
}

int ALIM ()
{
 return Positive_RA_Alt_Thresh(Alt_Layer_Value);
}

int Inhibit_Biased_Climb ()
{
    return (Climb_Inhibit ? Up_Separation + MINSEP /* error mutation NOZCROSS */ : Up_Separation); 
}

bool Non_Crossing_Biased_Climb()
{
    int upward_preferred;
    int upward_crossing_situation;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred)
    {
	result = !(Own_Below_Threat()) || ((Own_Below_Threat()) && (!(Down_Separation >= ALIM())));
    }
    else
    {	
	result = Own_Above_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= ALIM());
    }
    return result;
}

bool Non_Crossing_Biased_Descend()
{
    int upward_preferred;
    int upward_crossing_situation;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred)
    {
	result = Own_Below_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= ALIM());
    }
    else
    {
	result = !(Own_Above_Threat()) || ((Own_Above_Threat()) && (Up_Separation >= ALIM()));
    }
    return result;
}

bool Own_Below_Threat()
{
    return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Own_Above_Threat()
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

int alt_sep_test()
{
    bool enabled, tcas_equipped, intent_not_known;
    bool need_upward_RA, need_downward_RA;
    int alt_sep;

    enabled = High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF);
    tcas_equipped = Other_Capability == TCAS_TA;
    intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == NO_INTENT;
    
    alt_sep = UNRESOLVED;
    
    if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped))
    {
	need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat();
	need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat();
	if (need_upward_RA && need_downward_RA)
	    alt_sep = UNRESOLVED;
	else if (need_upward_RA)
	    alt_sep = UPWARD_RA;
	else if (need_downward_RA)
	    alt_sep = DOWNWARD_RA;
	else
	    alt_sep = UNRESOLVED;
    }

    return alt_sep;
}

void initializep2b(){
	/* Up_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value] &&
	Down_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value] &&
	Up_Separation < Down_Separation; */
	Positive_RA_Alt_Thresh_0 = 400;
    Positive_RA_Alt_Thresh_1 = 500;
    Positive_RA_Alt_Thresh_2 = 640;
    Positive_RA_Alt_Thresh_3 = 740;
    Cur_Vertical_Sep = 46766;
    High_Confidence = 1;
    Two_of_Three_Reports_Valid = 1;
    Own_Tracked_Alt_Rate = 574;
    Own_Tracked_Alt = 2000; 
    Other_Tracked_Alt = 4000;
    Alt_Layer_Value = 2;
    Up_Separation = 301;
    Down_Separation = 600;
    Other_RAC = 0;
    Other_Capability = 0;
    Climb_Inhibit = 1;
}

int main()
{
	int res;
    initializep2b(); /*Initial values, such that p2b is satisfied*/
    res = alt_sep_test(); 
    if(res == UPWARD_RA) __VERIFIER_error(); /* if p2b is satisfied; ensures alt_step != upward_RA() */ 

    return 0;
}
