/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission 
 * to convey the resulting work.
 */
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


