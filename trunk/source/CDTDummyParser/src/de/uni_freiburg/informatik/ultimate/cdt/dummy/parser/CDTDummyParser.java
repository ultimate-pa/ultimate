/**
 */
package de.uni_freiburg.informatik.ultimate.cdt.dummy.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * This dummy parser is used to pass the already parsed AST through Ultimate!
 * This is needed because we have to start Ultimate with a Source Plugin, which
 * should generate some Output. So here we only use the pre set AST and give it
 * back.
 * 
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 18.03.2012
 */
public class CDTDummyParser implements ISource {
	/**
	 * Supported file types.
	 */
	protected String[] m_FileTypes;
	/**
	 * The logger instance.
	 */
	protected static Logger s_Logger = UltimateServices.getInstance()
			.getLogger(Activator.PLUGIN_ID);
	/**
	 * List of file names.
	 */
	protected List<String> m_FileNames;

	/**
	 * Public constructor of this parser.
	 */
	public CDTDummyParser() {
		m_FileTypes = new String[] { "dummy" };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java
	 * .lang.Object)
	 */
	@Override
	public int init() {
		m_FileNames = new ArrayList<String>();
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return "CDTDummyParser";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID
	 * ()
	 */
	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java
	 * .io.File[])
	 */
	@Override
	public boolean parseable(File[] files) {
		for (File f : files) {
			if (!parseable(f)) {
				return false;
			}
		}
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseable(java
	 * .io.File)
	 */
	@Override
	public boolean parseable(File file) {
		for (String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java
	 * .io.File[])
	 */
	@Override
	public IElement parseAST(File[] files) throws Exception {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#parseAST(java
	 * .io.File)
	 */
	@Override
	public IElement parseAST(File file) throws Exception {
		Object ast = UltimateServices.getInstance().getParsedAST();
		if (ast == null) {
			s_Logger.error("There is no AST set in UltimateServices!");
			throw new RuntimeException();
		}
		if (!(ast instanceof IASTTranslationUnit)) {
			s_Logger.fatal("Parsed AST is not an instance of IASTTranslationUnit");
			throw new RuntimeException();
		}

		return new WrapperNode(null, (IASTTranslationUnit) ast);
	}


	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getFileTypes()
	 */
	@Override
	public String[] getFileTypes() {
		return m_FileTypes;
	}


	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#getOutputDefinition
	 * ()
	 */
	@Override
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST,
					this.m_FileNames);
		} catch (Exception ex) {
			s_Logger.log(Level.FATAL, ex.getMessage());
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource#setPreludeFile
	 * (java.io.File)
	 */
	@Override
	public void setPreludeFile(File prelude) {
		// not required
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
}
