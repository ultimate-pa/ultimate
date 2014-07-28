package req_to_pea;


import pea.modelchecking.J2UPPAALConverter;
import pea.reqCheck.PatternToPEA;

import java.util.ArrayList;
import java.util.List;
import java_cup.runtime.Symbol;

import pea.*;

import srParse.*;

public class ReqToPEA {
    public srParsePattern[] genPatterns(String reqFileName) {
    	try {
    		ReqParser parser = new ReqParser(reqFileName);
    		Symbol goal = parser.parse();
    		srParsePattern[] patterns = (srParsePattern[]) goal.value;
    		return patterns;
    	} catch (Exception ex) {
    		ex.printStackTrace();
    		return new srParsePattern[0];
    	}
    }
    
	public PhaseEventAutomata[] genPEA(srParsePattern[] patterns){
		List<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();
			
		PatternToPEA peaTrans=new PatternToPEA();
		for(srParsePattern pat : patterns)
		{
			// ignore patterns with syntax errors
			if (pat == null)
				continue;
			pat.setPeaTransformator( peaTrans );
			PhaseEventAutomata pea=pat.transformToPea();
			peaList.add(pea);
		}
		
		PhaseEventAutomata[] peaArray = peaList.toArray(new PhaseEventAutomata[peaList.size()]);
	    return peaArray;	
	}

	public void genPEAforUPPAAL(srParsePattern[] patterns, String xmlFilePath) {

		PhaseEventAutomata pea=null;				
		
		PatternToPEA peaTrans=new PatternToPEA();
		
		for(srParsePattern pat : patterns)
		{
			pat.setPeaTransformator( peaTrans );
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


