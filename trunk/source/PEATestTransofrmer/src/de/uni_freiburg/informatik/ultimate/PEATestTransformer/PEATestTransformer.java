package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.io.File;
import java.util.ArrayList; 
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser.SplToBoogie;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import srParse.pattern.PatternType; 

public class PEATestTransformer implements ISource { 
	private List<String> fileNames = new ArrayList<String>();
	private boolean previousToolFoundErrors;
	private SystemInformation sysInfo;
	private IUltimateServiceProvider mServices; 
	private ILogger logger;
	
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		this.logger = this.mServices.getLoggingService().getLogger(getPluginID());
		this.sysInfo= new SystemInformation(this.logger);
		Collection<CounterExampleResult> cex = ResultUtil.filterResults(services.getResultService().getResults(),
				CounterExampleResult.class);
		previousToolFoundErrors = !cex.isEmpty();
		PeaTestBackTranslator backtranslator = new PeaTestBackTranslator(BoogieASTNode.class, Expression.class, this.sysInfo, "", "");
		if (!previousToolFoundErrors && mServices.getPreferenceProvider(this.getPluginID())
				.getBoolean(PreferenceInitializer.LABEL_DOBACKTRANSLATE)) {
			services.getBacktranslationService().addTranslator(backtranslator);
		}
		
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}
	
	@Override
	public ModelType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Hardcoded");

		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.AST, filenames);
	}

	@Override
	public String getPluginName() {
		return "PEATestTransformer";
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public boolean parseable(File[] files) {
		return false;
	}

	@Override
	public boolean parseable(File file) {
		return file.getName().endsWith(".testreq");
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		SplToBoogie parser = new SplToBoogie(this.mServices, this.logger);
		//parse all files with reqs into one list of filled in patterns
		ArrayList<PatternType> filledPatterns = new ArrayList<PatternType>();
		for(File f: files){
			filledPatterns.addAll(Arrays.asList(parser.parseReqirementsFile(f.getAbsolutePath())));
		}
		//parse test definition file into a test definition and a system definition
		//TODO: how to switch transformer? 
		return parser.generatePEA(filledPatterns, this.sysInfo);
	}
 
	@Override
	public IElement parseAST(File file) throws Exception {
		return this.parseAST(new File[]{file});
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".testreq" };
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

}
