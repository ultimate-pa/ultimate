/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTParser plug-in.
 *
 * The ULTIMATE CDTParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTParser plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * CDTParser Plugin, it starts the CDT-Parser on a given C-File(s).
 * The resources are taken out of the lib-Folder, these should be
 * updated manually.
 */
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.IPDOMIndexer;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.internal.core.pdom.IPDOM;
import org.eclipse.cdt.internal.core.pdom.PDOMManager;
import org.eclipse.cdt.core.dom.parser.c.GCCParserExtensionConfiguration;
import org.eclipse.cdt.core.dom.parser.c.GCCScannerExtensionConfiguration;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICProject;
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
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;

import de.uni_freiburg.informatik.ultimate.cdt.parser.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

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
	protected String[] mFileTypes;
	/**
	 * The logger instance.
	 */
	protected ILogger mLogger;
	/**
	 * List of file names.
	 */
	protected List<String> mFileNames;
	private IUltimateServiceProvider mServices;

	/**
	 * Public constructor of this parser.
	 */
	public CDTParser() {
		mFileTypes = new String[] { "c", "i" };
	}

	@Override
	public void init() {
		mFileNames = new ArrayList<>();
	}

	@Override
	public String getPluginName() {
		return "CDTParser";
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	private boolean parseable(final File file) {
		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				return true;
			}
		}
		return false;
	}
	
	//created by Hamiz for entering multiple files
	private ICProject createCDTProjectFromFiles(File[] files)
			throws OperationCanceledException, CoreException, FileNotFoundException {
		IProject cdtProject = createNewCDTProject("Test Project 6");

		for (File file : files) {
			ResourceHelper.createFile(cdtProject, file);
		}
		
		CoreModel model = CoreModel.getDefault();
		ICProject icdtProject =  model.create(cdtProject);
		return icdtProject;
	}
	
	private void performCDTProjectOperations(File[] files)
			throws OperationCanceledException, FileNotFoundException, CoreException {
		ICProject icdtProject = createCDTProjectFromFiles(files);
		createPDOM(icdtProject);
	}
	
	private IProject createNewCDTProject(String name) throws OperationCanceledException, CoreException {
		return ResourceHelper.createCDTProject(name);
	}
	
	private void createPDOM(ICProject icdtProject) throws CoreException {
		PDOMManager pdomManager = new PDOMManager();
//		IPDOM ipdom = pdomManager.getPDOM(icdtProject);
		pdomManager.startup();
		pdomManager.reindex(icdtProject);
		IIndex inde = pdomManager.getIndex(icdtProject);
		boolean a = pdomManager.isProjectIndexed(icdtProject);
		System.out.println("oo");
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files.length == 1) {
			return parseAST(files[0]);
		}
		
		performCDTProjectOperations(files);
		
//		throw new UnsupportedOperationException("Cannot parse multiple C files");
		return null;
		
	}

	private IElement parseAST(final File file) throws Exception {

		final IParserLogService log = new DefaultLogService();

		final FileContent fContent = FileContent.createForExternalFileLocation(file.getAbsolutePath());

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String path = prefs.getString(PreferenceInitializer.INCLUDE_PATHS);
		String[] includePaths;
		IncludeFileContentProvider includeProvider;
		if (!path.equals("")) {
			mLogger.debug("INCLUDE-PATHS:" + path);
			includePaths = path.split(";");
			/*
			 * If there are some paths specified we have to use the this deprecated code. In the used Version of
			 * EclipseCDT (see CDTLibrary) there is no other way in doing this, maybe in further versions this will be
			 * improved.
			 */
			includeProvider = IncludeFileContentProvider.adapt(new StandaloneIndexerFallbackReaderFactory());
		} else {
			includePaths = new String[0];
			includeProvider = IncludeFileContentProvider.getEmptyFilesProvider();
		}

		final Map<String, String> definedSymbols = new HashMap<>();
		final IScannerInfo info = new ScannerInfo(definedSymbols, includePaths);

		final GCCScannerExtensionConfiguration config = GCCScannerExtensionConfiguration.getInstance();
		final CPreprocessor cprep = new CPreprocessor(fContent, info, ParserLanguage.C, log, config, includeProvider);

		// Here we our defined macros to the preproccessor
		// Map<String, String> macroMap = defineUserMacros();
		// for (String key : macroMap.keySet()) {
		// String value = macroMap.get(key);
		// cprep.addMacroDefinition(key.toCharArray(), value.toCharArray());
		// }

		final GCCParserExtensionConfiguration parserConfig = GCCParserExtensionConfiguration.getInstance();
		final GNUCSourceParser parser = new GNUCSourceParser(cprep, ParserMode.COMPLETE_PARSE, log, parserConfig);

		// The following methods was introduced in CDT8. Before there was the
		// following method that took a boolean parameter
		// parser.setSkipTrivialExpressionsInAggregateInitializers(false);
		// Matthias changed this on 2014-10-01.
		// If there are no problems you may delete this comment.
		parser.setMaximumTrivialExpressionsInAggregateInitializers(Integer.MAX_VALUE);

		final IASTTranslationUnit translationUnit = parser.parse();
		return new WrapperNode(null, translationUnit);
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mFileNames);
		} catch (final Exception ex) {
			mLogger.fatal(ex.getMessage());
			return null;
		}
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		// not necessary
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

	}

	@Override
	public void finish() {
		// not necessary
	}
}
