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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Scanner;
import java.util.UUID;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.dom.IPDOMManager;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.index.IIndexManager;
import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.model.ICContainer;
import org.eclipse.cdt.core.model.ICElement;
import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.cdt.core.model.IPathEntry;
import org.eclipse.cdt.core.model.ISourceRoot;
import org.eclipse.cdt.core.model.ITranslationUnit;
import org.eclipse.cdt.core.parser.util.ASTPrinter;
import org.eclipse.cdt.core.settings.model.CSourceEntry;
import org.eclipse.cdt.core.settings.model.ICSettingEntry;
import org.eclipse.cdt.core.settings.model.ICSourceEntry;
import org.eclipse.cdt.internal.core.pdom.indexer.IndexerPreferences;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.content.IContentTypeSettings;
import org.eclipse.core.runtime.jobs.Job;

import de.uni_freiburg.informatik.ultimate.cdt.CommentParser;
import de.uni_freiburg.informatik.ultimate.cdt.FunctionLineVisitor;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.parser.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 02.02.2012
 */
public class CDTParser implements ISource {
	/**
	 * Whether to print the AST and some debug information for the parsed translation units, or not.
	 */
	private static final boolean EXTENDED_DEBUG_OUTPUT = false;
	/**
	 * Because filenames need to be normalized and it would be impractical to pass on the CDT project to later stages of
	 * translation, a special 'flag' directory is included in the path to mark the end of the non-relevant path entries.
	 */
	private static final String CDT_PROJECT_HIERARCHY_FLAG =
			"FLAG" + UUID.randomUUID().toString().substring(0, 10).replace("-", "");

	private static final IProgressMonitor NULL_MONITOR = new NullProgressMonitor();
	private final String[] mFileTypes;
	private ILogger mLogger;
	private List<String> mFileNames;
	private IUltimateServiceProvider mServices;
	private IProject mCdtProject;

	public CDTParser() {
		mFileTypes = new String[] { "c", "i", "h" };
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

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		final Collection<IASTTranslationUnit> tuCollection = performCDTProjectOperations(files);

		if (EXTENDED_DEBUG_OUTPUT) {
			for (final IASTTranslationUnit tu : tuCollection) {
				mLogger.info("Printing AST for TU: " + tu.getFilePath());
				ASTPrinter.print(tu);
			}
		}

		final MultiparseSymbolTable mps = new MultiparseSymbolTable(mLogger);
		for (final IASTTranslationUnit tu : tuCollection) {
			mLogger.info("Scanning " + normalizeCDTFilename(tu.getFilePath()));
			tu.accept(mps);
		}

		// Print the mappings to the logger for debugging purposes
		mps.printMappings();

		final ASTDecorator decorator = decorateTranslationUnits(mps, tuCollection);
		decorator.setSymbolTable(mps);

		return new WrapperNode(null, decorator);
	}

	/**
	 * Normalizes a CDT project file name to the part just after the source folder (/src/<...>)
	 *
	 * @param in
	 *            the CDT file name
	 * @return the normalized file name
	 */
	public static String normalizeCDTFilename(final String in) {
		// Let's just assume that this string (FLAG-.../src/) is unique in the path...
		final String lookingFor = CDT_PROJECT_HIERARCHY_FLAG + File.separator + "src" + File.separator;
		final int posInInput = in.indexOf(lookingFor);
		if (posInInput < 0) {
			// The name is already normalized
			return in;
		}

		return in.substring(posInInput + lookingFor.length());
	}

	private ASTDecorator decorateTranslationUnits(final MultiparseSymbolTable mst,
			final Collection<IASTTranslationUnit> translationUnits) {
		final ASTDecorator decorator = new ASTDecorator();
		final IncludeSorter sorter = new IncludeSorter(mLogger, translationUnits, mst);
		for (final IASTTranslationUnit tu : sorter.getResult()) {
			final FunctionLineVisitor visitor = new FunctionLineVisitor();
			tu.accept(visitor);
			final CommentParser parser =
					new CommentParser(tu.getComments(), visitor.getLineRange(), mLogger, mServices);
			final List<ACSLNode> acslNodes = parser.processComments();

			// validateLTLProperty(acslNodes); See comment at method below
			decorator.provideAcslASTs(acslNodes);
			final DecoratorNode rootNode = decorator.mapASTs(tu);

			final DecoratedUnit unit = new DecoratedUnit(rootNode, tu);
			decorator.addDecoratedUnit(unit);
		}
		return decorator;
	}

	// created by Hamiz for entering multiple files
	private ICProject createCDTProjectFromFiles(final File[] files) throws CoreException, FileNotFoundException {
		final IProject proj = createCDTProject();
		mCdtProject = proj;
		mLogger.info("Created temporary CDT project at " + getFullPath(mCdtProject));

		final IFolder sourceFolder = mCdtProject.getFolder("src");
		sourceFolder.create(true, true, NULL_MONITOR);
		final ICSourceEntry entrySrc = new CSourceEntry(sourceFolder, null, ICSettingEntry.RESOLVED);
		for (final File file : files) {
			createCopyOfFileInProject(mCdtProject, sourceFolder, file);
		}

		final CoreModel model = CoreModel.getDefault();
		final ICProject icdtProject = model.create(mCdtProject);
		return icdtProject;
	}

	public static List<IASTTranslationUnit> getProjectTranslationUnits(final ICProject cproject) throws CoreException {
		final List<IASTTranslationUnit> tuList = new ArrayList<>();

		// get source folders
		try {
			for (final ISourceRoot sourceRoot : cproject.getSourceRoots()) {
				// get all elements
				for (final ICElement element : sourceRoot.getChildren()) {
					// if it is a container (i.e., a source folder)
					if (element.getElementType() == ICElement.C_CCONTAINER) {
						recursiveContainerTraversal((ICContainer) element, tuList);
					} else {
						final ITranslationUnit tu = (ITranslationUnit) element;
						tuList.add(tu.getAST());
					}
				}
			}
		} catch (final CModelException e) {
			e.printStackTrace();
		}
		return tuList;
	}

	private static void recursiveContainerTraversal(final ICContainer container, final List<IASTTranslationUnit> tuList)
			throws CoreException {
		for (final ICContainer inContainer : container.getCContainers()) {
			recursiveContainerTraversal(inContainer, tuList);
		}

		for (final ITranslationUnit tu : container.getTranslationUnits()) {
			tuList.add(tu.getAST());
		}
	}

	/**
	 * Multifiles: Parsing is now almost completely in the hands of the standard CDT-way of doing it. We create a CDT
	 * project from the given files and CDT returns a list of translation units for that project. These only need to be
	 * decorated and can then be passed to the CACSL2BoogieTranslation.
	 */
	private Collection<IASTTranslationUnit> performCDTProjectOperations(final File[] files)
			throws FileNotFoundException, CoreException {
		final ICProject icdtProject = createCDTProjectFromFiles(files);

		// useful: http://cdt-devel-faq.wikidot.com/#toc23

		final IIndexManager indexManager = CCorePlugin.getIndexManager();
		final boolean isIndexed = indexManager.isProjectIndexed(icdtProject);
		final List<IASTTranslationUnit> listTu = getProjectTranslationUnits(icdtProject);

		mLogger.info("IsIndexed: " + isIndexed);
		mLogger.info("Found " + listTu.size() + " translation units.");

		return listTu;
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
		if (mCdtProject != null) {
			try {
				mCdtProject.delete(true, true, null);
				mLogger.info("Deleted temporary CDT project at " + getFullPath(mCdtProject));
			} catch (final CoreException e) {
				mLogger.fatal("Failed to delete temporary CDT project:", e);
			}
		}
	}

	private static String getFullPath(final IProject project) {
		if (project == null) {
			return "NULL";
		}
		final IPath outerPath = project.getWorkspace().getRoot().getLocation();
		final IPath innerPath = project.getFullPath();
		return outerPath.append(innerPath).toOSString();
	}

	private static IProject createCDTProject() throws CoreException {
		// It would be nicer to have the project in a tmp directory, but this seems not to be trivially
		// possible with the current CDT parsing.
		final String projectName = CDT_PROJECT_HIERARCHY_FLAG;
		final String projectNamespace = UUID.randomUUID().toString().replace("-", "");

		final CCorePlugin cdtCorePlugin = CCorePlugin.getDefault();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IWorkspaceRoot root = workspace.getRoot();

		IProject project = root.getProject(projectName);
		IndexerPreferences.set(project, IndexerPreferences.KEY_INDEX_ALL_FILES, IPDOMManager.ID_FAST_INDEXER);

		final IProjectDescription prjDescription = workspace.newProjectDescription(projectName);
		prjDescription.setLocation(root.getLocation().append(projectNamespace + File.separator + projectName));
		final File namespaceDiretory = new File(prjDescription.getLocationURI()).getParentFile();
		namespaceDiretory.deleteOnExit();

		project = cdtCorePlugin.createCDTProject(prjDescription, project, NULL_MONITOR);
		project.open(null);

		final IContentType contentType = org.eclipse.core.runtime.Platform.getContentTypeManager()
				.getContentType(CCorePlugin.CONTENT_TYPE_CSOURCE);
		try {
			contentType.addFileSpec("i", IContentTypeSettings.FILE_EXTENSION_SPEC);
		} catch (final CoreException e) {
			throw new IllegalStateException("Could not add .i to C extensions.", e);
		}

		CoreModel.getDefault().create(project)
				.setRawPathEntries(new IPathEntry[] { CoreModel.newSourceEntry(project.getFullPath()) }, NULL_MONITOR);

		waitForProjectRefreshToFinish();
		// Assert.assertNotNull(project);

		// Assert.assertTrue(project.isOpen());

		return project;
	}

	public static IFile createCopyOfFileInProject(final IProject project, final IFolder sourceFolder, final File file)
			throws CoreException, FileNotFoundException {

		final Path filePath = new Path(file.getName());
		if (filePath.segmentCount() > 1) {
			throw new IllegalArgumentException("File has to be a single file");
		}

		final IPath relativeFilePath = sourceFolder.getProjectRelativePath().append(filePath);

		// TODO: Do not copy file, use links instead
		final String content = new Scanner(file).useDelimiter("\\Z").next();
		final IFile file1 = project.getFile(relativeFilePath);
		final InputStream inputStream = new ByteArrayInputStream(content.getBytes());
		file1.create(inputStream, true, NULL_MONITOR);
		return file1;
	}

	private static void waitForProjectRefreshToFinish() {
		try {
			// CDT opens the Project with BACKGROUND_REFRESH enabled which
			// causes the
			// refresh manager to refresh the project 200ms later. This Job
			// interferes
			// with the resource change handler firing see: bug 271264
			Job.getJobManager().join(ResourcesPlugin.FAMILY_AUTO_REFRESH, null);
		} catch (final Exception e) {
			// Ignore
		}
	}
}
