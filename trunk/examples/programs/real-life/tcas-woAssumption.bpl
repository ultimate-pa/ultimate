function Positive_RA_Alt_Thresh(idx : int ) returns (val : int );

procedure alt_sep_test(Cur_Vertical_Sep : int, High_Confidence : bool , Two_of_Three_Reports_Valid : bool , Own_Tracked_Alt : int , Own_Tracked_Alt_Rate : int , Other_Tracked_Alt : int , Alt_Layer_Value : int , Up_Separation : int , Down_Separation : int , Other_RAC : int , Other_Capability : int , Climb_Inhibit : bool ) returns (ret: int )  {
// predefined constants
	var OLEV : int ;
	var MAXALTDIFF : int ;
	var MINSEP : int ;
	var NOZCROSS : int ;
	var NO_INTENT : int ;
	var DO_NOT_CLIMB : int ;
	var DO_NOT_DESCEND : int ;
	var TCAS_TA : int ;
	var OTHER : int ;
	var UNRESOLVED : int ;
	var UPWARD_RA : int ;
	var DOWNWARD_RA : int ;
	// local variables
	var enabled : bool ; 
	var tcas_equipped : bool ;
	var intent_not_known : bool ;
	var need_upward_RA : bool ; 
	var need_downward_RA : bool ;
	var alt_sep : int ;

	var inhibitBiasedClimb : int ;
	var ownBelowThreat : bool ;
	var ownAboveThreat : bool ;
	var upward_preferred : bool ;
	var upward_crossing_situation : int ;
	var nonCrossingBiasedClimb : bool ;
	var nonCrossingBiasedDescend : bool ;

	OLEV := 600;
	MAXALTDIFF := 600;
	MINSEP := 300;
	NOZCROSS := 300;
	NO_INTENT := 0;
	DO_NOT_CLIMB := 1;
	DO_NOT_DESCEND := 2;
	TCAS_TA := 1;
	OTHER := 2;
	UNRESOLVED := 0;
	UPWARD_RA := 1;
	DOWNWARD_RA := 2;

	// inlined initialize method
	assume (Positive_RA_Alt_Thresh(0) == 400 );
	assume (Positive_RA_Alt_Thresh(1) == 500 );
	assume (Positive_RA_Alt_Thresh(2) == 640 );
	assume (Positive_RA_Alt_Thresh(3) == 740 );

	assume (Alt_Layer_Value <= 4 && Alt_Layer_Value >= 0);
	//assume (Up_Separation < Positive_RA_Alt_Thresh(Alt_Layer_Value));
	//assume (Down_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value));

	enabled := High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF);
	tcas_equipped := (Other_Capability == TCAS_TA);
	intent_not_known := (Two_of_Three_Reports_Valid && (Other_RAC == NO_INTENT));

	alt_sep := UNRESOLVED;

	if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)) {

	//inline: int Inhibit_Biased_Climb () line 61  
	if (Climb_Inhibit) {
		inhibitBiasedClimb:=Up_Separation + NOZCROSS;
	} else {
		inhibitBiasedClimb:=Up_Separation;
	}
	// end inline

	//inline: bool Own_Below_Threat() line 102
	ownBelowThreat := (Own_Tracked_Alt < Other_Tracked_Alt);
	//end inline

	//inline: bool Own_Above_Threat() line 107
	ownAboveThreat := (Other_Tracked_Alt < Own_Tracked_Alt);
	//end inline

	//inline: bool Non_Crossing_Biased_Climb() line 66

	upward_preferred := (inhibitBiasedClimb > Down_Separation);
	if (upward_preferred) {
		nonCrossingBiasedClimb := !(ownBelowThreat) || ((ownBelowThreat) && (!(Down_Separation > Positive_RA_Alt_Thresh(Alt_Layer_Value)))); /* opertor mutation */
	} else {	
		nonCrossingBiasedClimb := ownAboveThreat && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value));
	}	
	//end inline

	need_upward_RA := nonCrossingBiasedClimb && ownBelowThreat;


	//inline: bool Non_Crossing_Biased_Descend() line 84

	upward_preferred := inhibitBiasedClimb > Down_Separation;
	if (upward_preferred) {
		nonCrossingBiasedDescend := ownBelowThreat && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value));
	} else {
		nonCrossingBiasedDescend := !(ownAboveThreat) || ((ownAboveThreat) && (Up_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value)));
	}
	//end inline

	need_downward_RA := nonCrossingBiasedDescend && ownAboveThreat;
	if (need_upward_RA && need_downward_RA) {
		alt_sep := UNRESOLVED;
	} else if (need_upward_RA) {
		assert (!((Up_Separation < Positive_RA_Alt_Thresh(Alt_Layer_Value)) && (Down_Separation >= Positive_RA_Alt_Thresh(Alt_Layer_Value))));
		alt_sep := UPWARD_RA;
	} else if (need_downward_RA) {
		alt_sep := DOWNWARD_RA;
	} else {
		alt_sep := UNRESOLVED;
	}
		ret := alt_sep;  
	}
}

