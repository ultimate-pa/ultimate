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
package de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea;


import java.util.ArrayList;
import java.util.List;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.J2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqCheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParsePattern;

public class ReqToPEA {
	private ILogger mLogger = null;
	
	public ReqToPEA(ILogger logger){
		mLogger = logger;
	}
	
    public srParsePattern[] genPatterns(String reqFileName) {
    	try {
    		final ReqParser parser = new ReqParser(reqFileName);
    		final Symbol goal = parser.parse();
    		final srParsePattern[] patterns = (srParsePattern[]) goal.value;
    		return patterns;
    	} catch (final Exception ex) {
    		ex.printStackTrace();
    		return new srParsePattern[0];
    	}
    }
    
	public PhaseEventAutomata[] genPEA(srParsePattern[] patterns){
		final List<PhaseEventAutomata> peaList = new ArrayList<PhaseEventAutomata>();
			
		final PatternToPEA peaTrans=new PatternToPEA(mLogger);
		for(final srParsePattern pat : patterns)
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

	public void genPEAforUPPAAL(srParsePattern[] patterns, String xmlFilePath) {

		PhaseEventAutomata pea=null;				
		
		final PatternToPEA peaTrans=new PatternToPEA(mLogger);
		
		for(final srParsePattern pat : patterns)
		{
			pat.setPeaTransformator( peaTrans );
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


