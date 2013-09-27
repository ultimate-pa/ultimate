package MayBeDeleted;

import java.util.Vector;

import PatternLanguage.PL_PatternToLTL;
import PatternLanguage.PL_initiatedPattern;

//This class is responsible for the transformation of PL_Patterns to Logic
// Sie soll einerseits anhand der Requirements prüfen, wohin übersetzt werden soll, und dann 
// je nach Entscheidung nach LTL, CTL oder TCTL übersetzen (über PL_PatternToLTL, PL_PatternToCTL und PL_PatternToTCTL)

public class PL_PatternToLogic {
	
	//Constructor
	public PL_PatternToLogic(){
		
	}
	
	
	//Diese Funktion transformiert die Requirements in das LTL-satisfiability Problem, um die Requirements
	//auf Konsistenz zu checken; Wenn der ModelChecker ein Gegenbeispiel findet, dann sind die Anforderungen konsistent

	public String getSpecInLTL(Vector<String> requirementsSet){
		 PL_PatternToLTL testToLTL = new PL_PatternToLTL();
		 //String satisfiabilityCheck = "LTLSPEC !(";
		 String satisfiabilityCheck = "(";
		//Für satisfiability checking muß die Formel noch negiert werden!
		 //Die erste Formel muß so angehängt werden, die danach müssen mit UND verknüpft werden
		 
		 if (requirementsSet.size() <1) {
			 System.out.println("ERROR: ACCRequirements: There is no requirement that could be transformed to logic :(");
		 }
		 else 
			 {String requirement = requirementsSet.elementAt(0);
			 PL_initiatedPattern test = new PL_initiatedPattern(requirement);
			 String transformedPattern = testToLTL.transformPatternToLTL(test);
			 
			 satisfiabilityCheck = satisfiabilityCheck + "("+ transformedPattern +")";
		 
			 //get requirements
			 for (int i=1; i< requirementsSet.size();i++){
				 String nextRequirement = requirementsSet.elementAt(i);
				 PL_initiatedPattern next = new PL_initiatedPattern(nextRequirement);
				 String nextTransformedPattern = testToLTL.transformPatternToLTL(next);
				 satisfiabilityCheck = satisfiabilityCheck + "& ("+ nextTransformedPattern +")";
			 }		
		}
		 satisfiabilityCheck = satisfiabilityCheck + ")";
		 System.out.println(satisfiabilityCheck);
		 return satisfiabilityCheck;
	}

}
