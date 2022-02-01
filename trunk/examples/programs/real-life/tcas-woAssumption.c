int Positive_RA_Alt_Thresh( int idx ) {
    
    switch(idx) {
        case 0:
            return 400;
        case 1:
            return 500;
        case 2:
            return 640;
        case 3:
            return 740;
        default:
            return 0;
    }
}

//int alt_sep_test(int Cur_Vertical_Sep, int High_Confidence, int Two_of_Three_Reports_Valid, int Own_Tracked_Alt, int Own_Tracked_Alt_Rate, int Other_Tracked_Alt, int Alt_Layer_Value, int Up_Separation, int Down_Separation, int Other_RAC, int Other_Capability, int Climb_Inhibit) {
int main() {
// RANDOM input
	int Cur_Vertical_Sep;
	int High_Confidence;
	int Two_of_Three_Reports_Valid;
	int Own_Tracked_Alt;
	int Own_Tracked_Alt_Rate;
	int Other_Tracked_Alt;
	int Alt_Layer_Value;
	int Up_Separation;
	int Down_Separation;
	int Other_RAC;
	int Other_Capability;
	int Climb_Inhibit;
// predefined constants
	int OLEV;
	int MAXALTDIFF;
	int MINSEP;
	int NOZCROSS;
	int NO_INTENT;
	int DO_NOT_CLIMB;
	int DO_NOT_DESCEND;
	int TCAS_TA;
	int OTHER;
	int UNRESOLVED;
	int UPWARD_RA;
	int DOWNWARD_RA;
	// local variables
	int enabled; 
	int tcas_equipped;
	int intent_not_known;
	int need_upward_RA; 
	int need_downward_RA;
	int alt_sep;
    int ret;
    
	int inhibitBiasedClimb;
	int ownBelowThreat;
	int ownAboveThreat;
	int upward_preferred;
	int upward_crossing_situation;
	int nonCrossingBiasedClimb;
	int nonCrossingBiasedDescend;

	OLEV = 600;
	MAXALTDIFF = 600;
	MINSEP = 300;
	NOZCROSS = 300;
	NO_INTENT = 0;
	DO_NOT_CLIMB = 1;
	DO_NOT_DESCEND = 2;
	TCAS_TA = 1;
	OTHER = 2;
	UNRESOLVED = 0;
	UPWARD_RA = 1;
	DOWNWARD_RA = 2;

	if (Alt_Layer_Value < 0 && Alt_Layer_Value > 3) {
        return 0;
    }

	enabled = High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF);
	tcas_equipped = (Other_Capability == TCAS_TA);
	intent_not_known = (Two_of_Three_Reports_Valid && (Other_RAC == NO_INTENT));

	alt_sep = UNRESOLVED;

	if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)) {

	//inline: int Inhibit_Biased_Climb () line 61  
	if (Climb_Inhibit) {
		inhibitBiasedClimb = Up_Separation + NOZCROSS;
	} else {
		inhibitBiasedClimb = Up_Separation;
	}
	// end inline

	//inline: int Own_Below_Threat() line 102
	ownBelowThreat = (Own_Tracked_Alt < Other_Tracked_Alt);
	//end inline

	//inline: int Own_Above_Threat() line 107
	ownAboveThreat = (Other_Tracked_Alt < Own_Tracked_Alt);
	//end inline

	//inline: int Non_Crossing_Biased_Climb() line 66

	upward_preferred = (inhibitBiasedClimb > Down_Separation);
	if (upward_preferred) {
		nonCrossingBiasedClimb = !(ownBelowThreat) || ((ownBelowThreat) && (!(Down_Separation > Positive_RA_Alt_Thresh(Alt_Layer_Value)))); /* opertor mutation */
	} else {	
		nonCrossingBiasedClimb = ownAboveThreat && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value));
	}	
	//end inline

	need_upward_RA = nonCrossingBiasedClimb && ownBelowThreat;


	//inline: int Non_Crossing_Biased_Descend() line 84

	upward_preferred = inhibitBiasedClimb > Down_Separation;
	if (upward_preferred) {
		nonCrossingBiasedDescend = ownBelowThreat && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value));
	} else {
		nonCrossingBiasedDescend = !(ownAboveThreat) || ((ownAboveThreat) && (Up_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value)));
	}
	//end inline

	need_downward_RA = nonCrossingBiasedDescend && ownAboveThreat;
	if (need_upward_RA && need_downward_RA) {
		alt_sep = UNRESOLVED;
	} else if (need_upward_RA) {
		assert (!((Up_Separation < Positive_RA_Alt_Thresh(Alt_Layer_Value)) && (Down_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value))));
		alt_sep = UPWARD_RA;
	} else if (need_downward_RA) {
		alt_sep = DOWNWARD_RA;
	} else {
		alt_sep = UNRESOLVED;
	}
		ret = alt_sep;  
	}
    return ret;
}

