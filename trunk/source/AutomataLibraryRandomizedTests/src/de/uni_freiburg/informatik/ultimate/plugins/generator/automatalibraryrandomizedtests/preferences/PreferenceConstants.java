package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.preferences;

/**
 * Constant definitions for plug-in preferences
 */
public class PreferenceConstants {

	public static final String Name_WriteToFile = "writeToFile";
	public static final boolean Default_WriteToFile = false;
	
	public static final String Name_Operation = "operation";
	
	public static final String[] operations = {
		"buchiComplementSVW",
		"minimizeSevpa",
		"buchiComplementComparison"
	};
	
	public static final String Name_NumberOfLetters= "numberOfLetters";
	
	public static final String Name_NumberOfStates= "numberOfStates";
	
	public static final String Name_ProbabilityInitial= "probabilityIntial";
	public static final String Name_ProbabilityFinal= "probabilityFinal";
	public static final String Name_ProbabilityInternalTransition= "probabilityInternalTransition";
	public static final String Name_ProbabilityCallTransition= "probabilityCallTransition";
	public static final String Name_ProbabilityReturnTransition= "probabilityReturnTransition";
		
	public static final String Default_Operation = "buchiComplementSVW";
	
	public static final int Default_NumberOfLetters = 2;
	public static final int Default_NumberOfStates = 10;
	public static final int Default_ProbabilityInitial= 10;
	public static final int Default_ProbabilityFinal= 10;
	public static final int Default_ProbabilityInternalTransition= 10;
	public static final int Default_ProbabilityCallTransition= 0;
	public static final int Default_ProbabilityReturnTransition= 0;
	

	
}
