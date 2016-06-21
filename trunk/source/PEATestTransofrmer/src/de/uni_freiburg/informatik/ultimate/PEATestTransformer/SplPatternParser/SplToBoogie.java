package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Activator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer.PatternTransformerTypes;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.NullTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.SimplePositiveTestTransformer;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.BasicTranslator;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.SimplePositiveTestTranslator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.ClosedWorldTransformator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.DeductionGuardTransformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.IPeaTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.PatternToDc;
import java_cup.runtime.Symbol;
import pea.CounterTrace;
import pea.PhaseEventAutomata;
import pea.Trace2PEACompiler;
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
		logger.debug("Transforming to DCTraces");
		ArrayList<CounterTrace> counterTraces = this.translateToDc(patterns);
		ArrayList<PhaseEventAutomata> peas = this.translateToPea(counterTraces);
		logger.debug("Running Transformation mode: "+ ttype.toString());
		IPeaTransformer peaTransformer;
		switch(ttype){
			case None: peaTransformer = new NullTransformer(); 
					break;
			case DeductionMonitor: peaTransformer = new DeductionGuardTransformation(this.logger, sysInfo);
				break; 
			default:
				throw new UnsupportedOperationException("Non supported test Transformer");
		}
		List<PhaseEventAutomata> peasList = peaTransformer.translate(patterns, counterTraces, peas);
		//TODO: set parser for peas depending on ttype --> a tranlation type is a combination of pea transformations
		// and boogie translation
		BasicTranslator peaToBoogie;
		logger.debug("Running Boogie Encoding mode: "+ ttype.toString());
		switch(ttype){
		case None: peaToBoogie = new BasicTranslator(peas); 
				break;
		case DeductionMonitor: peaToBoogie = new SimplePositiveTestTranslator(counterTraces, peas, sysInfo);
			break;
		default:
			throw new UnsupportedOperationException("Non supported test Transformer");
		}
	return peaToBoogie.generateBoogieTranslation();
	}
	
	
	private ArrayList<CounterTrace> translateToDc(ArrayList<PatternType> patterns){
		PatternToDc patternToDc = new PatternToDc();
		// Translate to Counter Traces
		ArrayList<CounterTrace> counterTraces = new ArrayList<CounterTrace>();
		for(PatternType pattern : patterns){
			CounterTrace counterTrace = patternToDc.translate(pattern);
			
			counterTraces.add(counterTrace);
		}
		return counterTraces;
	}
	
	private ArrayList<PhaseEventAutomata> translateToPea(ArrayList<CounterTrace> counterTraces){
		Trace2PEACompiler compiler = new Trace2PEACompiler();
		ArrayList<PhaseEventAutomata> peas = new ArrayList<PhaseEventAutomata>();
		for(CounterTrace ct : counterTraces){
			peas.add(compiler.compile(ct.toString(), ct));
		}
		return peas;	
	}
	

}




















