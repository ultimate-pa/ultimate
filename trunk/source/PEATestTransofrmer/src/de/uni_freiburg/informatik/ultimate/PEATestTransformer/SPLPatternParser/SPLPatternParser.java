package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SPLPatternParser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Activator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer.PatternTransformerTypes;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.PatternToPea;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.SimplePositiveTest;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.ClosedWorldTransformator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import java_cup.runtime.Symbol;
import pea.PhaseEventAutomata;
import srParse.ReqParser;
import srParse.pattern.PatternType;

/***
 * This class supplies batch methods for parsing requirements files
 * and transforming patterns To PEAs. 
 * 
 * @author Langenfeld
 *
 */
public class SPLPatternParser {
	
	/***
	 * Parse requirements file to array of SPL pattern types.
	 * @param text file containing requirements as SPL patterns
	 * @return requirements as patterns
	 */
	public PatternType[] parseReqirementsFile(String file){
    	try {
    		ReqParser parser = new ReqParser(file);
    		Symbol goal = parser.parse();
    		PatternType[] patterns = (PatternType[]) goal.value;
    		return patterns;
    	} catch (Exception ex) {
    		ex.printStackTrace();
    		return new PatternType[0];
    	}
	} 
	
	/***
	 * Transform the patterns returned by the parser into Phase Event Automata
	 * @param requirements as patterns
	 * @return requirements as peas
	 */
	public PhaseEventAutomata[] generatePEA(ArrayList<PatternType> patterns){
		PatternTransformerTypes ttype =  new UltimatePreferenceStore(Activator.PLUGIN_ID)
			.getEnum(PreferenceInitializer.LABEL_TRANSFORMER, PreferenceInitializer.PatternTransformerTypes.class);
		SystemInformation sysInfo = new SystemInformation(); //TODO: this will be parsed from elsewhere!
		PatternToPea patternToPea;
		switch(ttype){
			case None: patternToPea = new PatternToPea(); 
					break;
			case SimplePositiveTest: patternToPea = new SimplePositiveTest(sysInfo);
				break;
			case ClosedWorld: patternToPea = new ClosedWorldTransformator(sysInfo);
				break;
			default:
				throw new UnsupportedOperationException("Non supported test Transformer");
		}
		List<PhaseEventAutomata> peas = patternToPea.translate(patterns);
		return peas.toArray(new PhaseEventAutomata[peas.size()]);
	}
	

}




















