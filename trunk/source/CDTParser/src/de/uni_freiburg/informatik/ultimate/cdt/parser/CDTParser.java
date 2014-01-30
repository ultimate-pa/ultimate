/**
 * CDTParser Plugin, it starts the CDT-Parser on a given C-File(s).
 * The resources are taken out of the lib-Folder, these should be 
 * updated manually.
 */
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.parser.c.GCCParserExtensionConfiguration;
import org.eclipse.cdt.core.dom.parser.c.GCCScannerExtensionConfiguration;
import org.eclipse.cdt.core.parser.DefaultLogService;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IScannerInfo;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ParserLanguage;
import org.eclipse.cdt.core.parser.ParserMode;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.cdt.internal.core.dom.parser.c.GNUCSourceParser;
import org.eclipse.cdt.internal.core.indexer.StandaloneIndexerFallbackReaderFactory;
import org.eclipse.cdt.internal.core.parser.scanner.CPreprocessor;

import de.uni_freiburg.informatik.ultimate.cdt.parser.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.02.2012
 */
@SuppressWarnings({ "deprecation", "restriction" })
public class CDTParser implements ISource {
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
	public CDTParser() {
		m_FileTypes = new String[] { "c", "i" };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java
	 * .lang.Object)
	 */
	@Override
	public int init(Object params) {
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
		return "CDTParser";
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

		IParserLogService log = new DefaultLogService();

		FileContent fContent = FileContent.createForExternalFileLocation(file
				.getAbsolutePath());

		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		String path = prefs.getString(PreferenceInitializer.INCLUDE_PATHS);
		String[] includePaths;
		IncludeFileContentProvider includeProvider;
		if (!path.equals("")) {
			s_Logger.debug("INCLUDE-PATHS:" + path);
			includePaths = path.split(";");
			/* If there are some paths specified we have to use the this
			 * deprecated code. In the used Version of EclipseCDT 
			 * (see CDTLibrary) there is no other way in doing this, maybe
			 * in further versions this will be improved.
			 */
			includeProvider = IncludeFileContentProvider
					.adapt(new StandaloneIndexerFallbackReaderFactory());
		} else {
			includePaths = new String[0];
			includeProvider = IncludeFileContentProvider
					.getEmptyFilesProvider();
		}

		Map<String, String> definedSymbols = new HashMap<String, String>();
		IScannerInfo info = new ScannerInfo(definedSymbols, includePaths);

		GCCScannerExtensionConfiguration config = GCCScannerExtensionConfiguration
				.getInstance();
		CPreprocessor cprep = new CPreprocessor(fContent, info,
				ParserLanguage.C, log, config, includeProvider);

		// Here we our defined macros to the preproccessor
//		Map<String, String> macroMap = defineUserMacros();
//		for (String key : macroMap.keySet()) {
//			String value = macroMap.get(key);
//			cprep.addMacroDefinition(key.toCharArray(), value.toCharArray());
//		}

		GCCParserExtensionConfiguration p_config = GCCParserExtensionConfiguration
				.getInstance();
		GNUCSourceParser parser = new GNUCSourceParser(cprep,
				ParserMode.COMPLETE_PARSE, log, p_config);

		parser.setSkipTrivialExpressionsInAggregateInitializers(false);
		
		IASTTranslationUnit translationUnit = parser.parse();
		return new WrapperNode(null, translationUnit);
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
		return new PreferenceInitializer();
	}
}
