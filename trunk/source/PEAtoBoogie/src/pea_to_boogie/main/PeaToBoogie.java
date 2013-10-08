package pea_to_boogie.main;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import pea.PhaseEventAutomata;
import pea_to_boogie.Activator;
import pea_to_boogie.translator.Translator;
import req_to_pea.ReqToPEA;
import srParse.srParsePattern;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;

public class PeaToBoogie implements ISource {
    protected static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
    List<String> m_FileNames = new ArrayList<String>();

	@Override
	public int init(Object params) {
		return 0;
	}

	@Override
	public String getName() {
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
    	s_Logger.info("Parsing: '"+inputPath+"'");
    	srParsePattern[] patterns = new ReqToPEA().genPatterns(inputPath);
    	int combinationNum = Math.min(patterns.length, 3); //TODO preference
 		translator.setCombinationNum(combinationNum);
 		translator.setInputFilePath(inputPath);
 		Unit unit = translator.genBoogie(patterns);	
 		return new WrapperNode(null, unit);
	}

	@Override
	public String[] getTokens() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String[] getFileTypes() {
		// TODO Auto-generated method stub
		return new String[] { ".req" };
	}

	@Override
	public TokenMap getTokenMap() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST, m_FileNames);
		} catch (Exception ex) {
			s_Logger.log(Level.FATAL,"syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub

	}

}
