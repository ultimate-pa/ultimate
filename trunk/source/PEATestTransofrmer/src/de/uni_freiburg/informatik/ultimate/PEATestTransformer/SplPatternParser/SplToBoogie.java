package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Activator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer.PatternTransformerTypes;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.BasicTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.SimplePositiveTest;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.BasicTranslator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.ClosedWorldTransformator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
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
public class SplToBoogie {
	
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
	public Unit generatePEA(ArrayList<PatternType> patterns){
		PatternTransformerTypes ttype =  new UltimatePreferenceStore(Activator.PLUGIN_ID)
			.getEnum(PreferenceInitializer.LABEL_TRANSFORMER, PreferenceInitializer.PatternTransformerTypes.class);
		SystemInformation sysInfo = new SystemInformation(); //TODO: this will be parsed from elsewhere!
		BasicTransformer patternToPea;
		switch(ttype){
			case None: patternToPea = new BasicTransformer(); 
					break;
			case SimplePositiveTest: patternToPea = new SimplePositiveTest(sysInfo);
				break;
			case ClosedWorld: patternToPea = new ClosedWorldTransformator(sysInfo);
				break;
			default:
				throw new UnsupportedOperationException("Non supported test Transformer");
		}
		List<PhaseEventAutomata> peasList = patternToPea.translate(patterns);
		PhaseEventAutomata[] peas = peasList.toArray(new PhaseEventAutomata[peasList.size()]);
		//TODO: set parser for peas depending on ttype --> a tranlation type is a combination of pea transformations
		// and boogie translation
		BasicTranslator peaToBoogie;
		switch(ttype){
		case None: peaToBoogie = new BasicTranslator(peas); 
				break;
		case SimplePositiveTest: peaToBoogie = new BasicTranslator(peas);
			break;
		case ClosedWorld: peaToBoogie = new BasicTranslator(peas);
			break;
		default:
			throw new UnsupportedOperationException("Non supported test Transformer");
		}
	return peaToBoogie.generateBoogieTranslation();
	}
	

}




















