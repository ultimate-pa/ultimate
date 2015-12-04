package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SplPatternParser.SplPatternParser;
import de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator.Translator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import pea.PhaseEventAutomata;
import srParse.pattern.PatternType; 

public class PeaTestTransformer implements ISource {
	protected Logger mLogger;
	List<String> m_FileNames = new ArrayList<String>();
	
	
	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
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
	public GraphType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Hardcoded");

		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.AST, filenames);
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
		SplPatternParser parser = new SplPatternParser();
		//parse all files with reqs into one list of filled in patterns
		ArrayList<PatternType> filledPatterns = new ArrayList<PatternType>();
		for(File f: files){
			filledPatterns.addAll(Arrays.asList(parser.parseReqirementsFile(f.getAbsolutePath())));
		}
		//parse test definition file into a test definition and a system definition
		//TODO: how to switch transformer? 
		PhaseEventAutomata[] peas = parser.generatePEA(filledPatterns);
		//transform to boogie
		//TODO:write more modifiable translator
		Translator translator = new Translator();
		BitSet vacuityChecks = new BitSet(peas.length);
		vacuityChecks.set(0, peas.length);
		translator.setInputFilePath("dummy");
		Unit u = translator.genBoogie(peas);
		return u; 
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
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
}
