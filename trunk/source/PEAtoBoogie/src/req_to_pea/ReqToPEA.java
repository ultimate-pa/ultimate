package req_to_pea;


import java.util.ArrayList;
import java.util.List;

import java_cup.runtime.Symbol;
import pea.PhaseEventAutomata;
import pea.modelchecking.J2UPPAALConverter;
import srParse.ReqParser;
import srParse.pattern.PatternType;

public class ReqToPEA {
    public PatternType[] genPatterns(String reqFileName) {
    	try {
    		ReqParser parser = new ReqParser(reqFileName);
    		Symbol goal = parser.parse();
    		PatternType[] patterns = (PatternType[]) goal.value;
    		return patterns;
    	} catch (Exception ex) {
    		ex.printStackTrace();
    		return new PatternType[0];
    	}
    }
    
	public PhaseEventAutomata[] genPEA(PatternType[] patterns){
		List<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();
			
		for(PatternType pat : patterns)
		{
			// ignore patterns with syntax errors
			if (pat == null)
				continue;
			PhaseEventAutomata pea=pat.transformToPea();
			peaList.add(pea);
		}
		
		PhaseEventAutomata[] peaArray = peaList.toArray(new PhaseEventAutomata[peaList.size()]);
	    return peaArray;	
	}

	public void genPEAforUPPAAL(PatternType[] patterns, String xmlFilePath) {

		PhaseEventAutomata pea=null;				
		
		for(PatternType pat : patterns)
		{
			if (pea == null)
			{
				pea = pat.transformToPea();

			}
			else
			{	
				PhaseEventAutomata pea2 = pat.transformToPea();
				if (pea2 == null)
					continue;					
				pea=pea.parallel( pea2 );
			
			}								
		}			
		J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
		uppaalConverter.writePEA2UppaalFile(xmlFilePath, pea);									
	}
}


