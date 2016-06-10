package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Activator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer.PatternTransformerTypes;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.BasicTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.SimplePositiveTestTransformer;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.BasicTranslator;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.SimplePositiveTestTranslator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.ClosedWorldTransformator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.DeductionGuardTransromation;
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
	
	private final IUltimateServiceProvider mService;
	private final ILogger logger;
	
	public SplToBoogie(IUltimateServiceProvider service, ILogger logger){
		mService = service;
		this.logger = logger;
	}
	
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
		PatternTransformerTypes ttype =  mService.getPreferenceProvider(Activator.PLUGIN_ID)
			.getEnum(PreferenceInitializer.LABEL_TRANSFORMER, PreferenceInitializer.PatternTransformerTypes.class);
		SystemInformation sysInfo = new SystemInformation(); //TODO: this will be parsed from elsewhere!
		BasicTransformer patternToPea;
		logger.debug("Running Transformation mode: "+ ttype.toString());
		switch(ttype){
			case None: patternToPea = new BasicTransformer(); 
					break;
			case SimplePositiveTest: patternToPea = new SimplePositiveTestTransformer(sysInfo);
				break;
			case ClosedWorld: patternToPea = new ClosedWorldTransformator(sysInfo);
				break;
			case DeductionMonitor: patternToPea = new DeductionGuardTransromation(this.logger, sysInfo);
				break;
			default:
				throw new UnsupportedOperationException("Non supported test Transformer");
		}
		List<PhaseEventAutomata> peasList = patternToPea.translate(patterns);
		PhaseEventAutomata[] peas = peasList.toArray(new PhaseEventAutomata[peasList.size()]);
		//TODO: set parser for peas depending on ttype --> a tranlation type is a combination of pea transformations
		// and boogie translation
		BasicTranslator peaToBoogie;
		logger.debug("Running T mode: "+ ttype.toString());
		switch(ttype){
		case None: peaToBoogie = new BasicTranslator(peas); 
				break;
		case SimplePositiveTest: peaToBoogie = new SimplePositiveTestTranslator(peas, sysInfo);
			break;
		case ClosedWorld: peaToBoogie = new BasicTranslator(peas);
			break;
		case DeductionMonitor: peaToBoogie = new BasicTranslator(peas);
			break;
		default:
			throw new UnsupportedOperationException("Non supported test Transformer");
		}
	return peaToBoogie.generateBoogieTranslation();
	}
	

}




















