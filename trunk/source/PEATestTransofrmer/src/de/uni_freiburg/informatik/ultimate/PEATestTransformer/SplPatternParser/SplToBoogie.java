package de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Activator;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PeaSystemModel;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.PreferenceInitializer.PatternTransformerTypes;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.DeductionGuardTransformation;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.IPeaTransformer;
import de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer.NullTransformer;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.BasicTranslator;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.SimplePositiveTestTranslator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import com.github.jhoenicke.javacup.runtime.Symbol;
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
		//TODO: correctly parse system information
		PeaSystemModel model = new PeaSystemModel(this.logger, new SystemInformation(), patterns);
		
		PatternTransformerTypes ttype =  mService.getPreferenceProvider(Activator.PLUGIN_ID)
			.getEnum(PreferenceInitializer.LABEL_TRANSFORMER, PreferenceInitializer.PatternTransformerTypes.class);
		this.logger.info("Running Transformation mode: "+ ttype.toString());
		IPeaTransformer peaTransformer;
		switch(ttype){
			case None: peaTransformer = new NullTransformer(); 
					break;
			case DeductionMonitor: peaTransformer = new DeductionGuardTransformation(this.logger, model);
				break; 
			default:
				throw new UnsupportedOperationException("Non supported test Transformer");
		}
		peaTransformer.translate();
		//TODO: set parser for peas depending on ttype --> a tranlation type is a combination of pea transformations
		// and boogie translation
		BasicTranslator peaToBoogie;
		logger.debug("Running Boogie Encoding mode: "+ ttype.toString());
		switch(ttype){
		case None: peaToBoogie = new BasicTranslator(model); 
				break;
		case DeductionMonitor: peaToBoogie = new SimplePositiveTestTranslator(model);
			break;
		default:
			throw new UnsupportedOperationException("Non supported test Transformer");
		}
	return peaToBoogie.generateBoogieTranslation();
	}
	
	

	

}




















