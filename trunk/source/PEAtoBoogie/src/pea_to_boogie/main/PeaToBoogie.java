package pea_to_boogie.main;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import pea_to_boogie.Activator;
import pea_to_boogie.translator.Translator;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class PeaToBoogie implements ISource {
	protected Logger mLogger;
	List<String> m_FileNames = new ArrayList<String>();

	@Override
	public void init() {
	}

	@Override
	public String getPluginName() {
		return "PEA to Boogie";
	}

	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public boolean parseable(File[] files) {
		return false;
	}

	@Override
	public boolean parseable(File file) {
		return file.getName().endsWith(".req");
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		throw new UnsupportedOperationException();
	}

	@Override
	public IElement parseAST(File file) throws Exception {
		Translator translator = new Translator();
		String inputPath = file.getAbsolutePath();
		m_FileNames = new ArrayList<String>();
		m_FileNames.add(inputPath);
		mLogger.info("Parsing: '" + inputPath + "'");
		srParsePattern[] patterns = new ReqToPEA().genPatterns(inputPath);
		int combinationNum = Math.min(patterns.length, 3); // TODO preference
		translator.setCombinationNum(combinationNum);
		translator.setInputFilePath(inputPath);
		return translator.genBoogie(patterns);
	}

	@Override
	public String[] getFileTypes() {
		// TODO Auto-generated method stub
		return new String[] { ".req" };
	}

	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, m_FileNames);
		} catch (Exception ex) {
			mLogger.log(Level.FATAL, "syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
}
