package srParse.pattern;

import pea.CDD;

public class UniversalityPattern extends PatternType
{
	public void transform()
	{
		/*
		CDD p_cdd = BooleanDecision.create("ANB_Request_valid = 1");
		CDD q_cdd = BooleanDecision.create("ANB_Teilbremsung_Freigabe = 1").and( BooleanDecision.create("ANB_info_Teilbremsung = 1") ); 
		CDD r_cdd = p_cdd;
		*/
		
		
		CDD p_cdd = cdds.get(0); 
		CDD q_cdd = scope.getCdd1(); 
		CDD r_cdd = scope.getCdd2();
					
		pea = peaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}
	
	public String toString()
	{
		String res=new String();
		
		res="it is always the case that \""+cdds.get(0)+"\" holds";
		
		return res;
	}
}
