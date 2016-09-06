package req_to_pea;


import java.util.ArrayList;
import java.util.List;

import com.github.jhoenicke.javacup.runtime.Symbol;
import pea.PhaseEventAutomata;
import pea.modelchecking.J2UPPAALConverter;
import pea.reqCheck.PatternToPEA;
import srParse.ReqParser;
import srParse.pattern.PatternType;

public class ReqToPEA {
    public PatternType[] genPatterns(String reqFileName) {
    	try {
    		ReqParser parser = new ReqParser(reqFileName);
    		Symbol goal = parser.parse();
    		PatternType[] patterns = (PatternType[]) goal.value;
    		return patterns;
    	} catch (final Exception ex) {
    		ex.printStackTrace();
    		return new PatternType[0];
    	}
    }
    
	public PhaseEventAutomata[] genPEA(PatternType[] patterns){
		final List<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();
		
		PatternToPEA peaTrans=new PatternToPEA();
		for(PatternType pat : patterns)
		{
			// ignore patterns with syntax errors
			if (pat == null) {
				continue;
			}
			pat.setPeaTransformator( peaTrans );
			final PhaseEventAutomata pea=pat.transformToPea();
			peaList.add(pea);
		}
		
		final PhaseEventAutomata[] peaArray = peaList.toArray(new PhaseEventAutomata[peaList.size()]);
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
				final PhaseEventAutomata pea2 = pat.transformToPea();
				if (pea2 == null) {
					continue;					
				}					
				pea=pea.parallel( pea2 );
			
			}								
		}			
		final J2UPPAALConverter uppaalConverter = new J2UPPAALConverter();
		uppaalConverter.writePEA2UppaalFile(xmlFilePath, pea);									
	}
}


