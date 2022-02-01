/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 *
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * This class is basically the interface between Codan and Ultimate
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.HashMap;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.codan.core.model.CheckerLaunchMode;
import org.eclipse.cdt.codan.core.model.IProblemWorkingCopy;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.cdt.codan.extension.AbstractFullAstChecker;
import de.uni_freiburg.informatik.ultimate.cdt.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 31.01.2012
 */
public class UltimateCChecker extends AbstractFullAstChecker {
	/**
	 * The identifier.
	 */
	public static final String ID = "de.uni_freiburg.informatik.ultimate.cdt." + "codan.UltimateCChecker";

	/**
	 * In this map we store the listed files out of the directory.
	 */
	private final HashMap<String, File> mToolchainFiles;

	private IUltimateServiceProvider mServices;

	private static IToolchainStorage sStorage;

	private final CDTController mController;

	/**
	 * The Constructor of this Checker
	 *
	 * @throws Exception
	 */
	public UltimateCChecker() throws Throwable {
		super();
		mToolchainFiles = new HashMap<String, File>();
		mController = new CDTController(this);
	}

	@Override
	protected void finalize() throws Throwable {
		mController.close();
		super.finalize();
	}

	@Override
	public void processAst(final IASTTranslationUnit ast) {
		// first, clear all old results
		CDTResultStore.clearHackyResults();
		CDTResultStore.clearResults();

		// run ultimate
		try {
			mController.runToolchain(getToolchainPath(), ast);
		} catch (final Exception e) {
			e.printStackTrace();
		}

		// After the run, we can obtain the results
		// -> so we have to prepare them for displaying to the user
		// reportProblem(...) --> is used for displaying
		// new CodanProblem("...", "...")
		// CodanSeverity.Error;
		// CodanSeverity.Warning;
		// CodanSeverity.Info;
		final String completePath = ast.getFilePath();
		reportProblems(completePath);
		updateFileView(completePath);
		mController.complete();

	}

	private String getToolchainPath() {
		// obtain selected toolchain from preferences
		final String selectedToolchain =
				mServices.getPreferenceProvider(Activator.PLUGIN_ID).getString(PreferencePage.TOOLCHAIN_SELECTION_TEXT);

		final File tc = mToolchainFiles.get(selectedToolchain);
		String path = null;
		if (tc != null) {
			path = tc.getAbsolutePath();
		}
		return path;
	}

	private void updateFileView(final String completePath) {
		// After finishing the Ultimate run we update the FileView
		// We have to do this in this asynch manner, because otherwise we would
		// get a NullPointerException, because we are not in the UI Thread
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			@Override
			public void run() {
				// Present results of the actual run!
				final IViewPart vpart =
						PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView(ResultList.ID);
				if (vpart instanceof ResultList) {
					((ResultList) vpart).setViewerInput(completePath);
				}
				// open the file on which the actual run happened!
				final File fileToOpen = new File(completePath);
				if (fileToOpen.exists() && fileToOpen.isFile()) {
					final IFileStore fileStore = EFS.getLocalFileSystem().getStore(fileToOpen.toURI());
					final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();

					try {
						IDE.openEditorOnFileStore(page, fileStore);
					} catch (final PartInitException e) {
						// Put your exception handler here if you wish to
					}
				}
			}
		});
	}

	/**
	 * Method for reporting Problems to Eclipse
	 *
	 * @param fileName
	 *            the FileName
	 */
	private void reportProblems(final String fileName) {
		final ILogger log = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		// we obtain the results by UltimateServices
		final Set<String> tools = mServices.getResultService().getResults().keySet();

		// we iterate over the key set, each key represents the name
		// of the tool, which created the results
		for (final String toolID : tools) {
			final List<IResult> resultsOfTool = mServices.getResultService().getResults().get(toolID);
			CDTResultStore.addResults(fileName, toolID, resultsOfTool);
			if (resultsOfTool == null) {
				log.debug("No results for " + toolID);
				continue;
			}
			for (final IResult result : resultsOfTool) {
				if (result instanceof IResultWithLocation) {
					reportProblemWithLocation((IResultWithLocation) result, log);
				} else {
					reportProblemWithoutLocation(result, log);
				}
			}
		}
	}

	private void reportProblemWithoutLocation(final IResult result, final ILogger log) {
		if (result instanceof ExceptionOrErrorResult) {
			reportProblem(CCheckerDescriptor.GENERIC_ERROR_RESULT_ID, getFile(), 0, result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		} else {
			reportProblem(CCheckerDescriptor.GENERIC_INFO_RESULT_ID, getFile(), 0, result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		}
	}

	private void reportProblemWithLocation(final IResultWithLocation result, final ILogger log) {
		if (result.getLocation() == null) {
			log.warn("Result type should have location, but has none: " + result.getShortDescription() + " ("
					+ result.getClass() + ")");
			return;
		}

		if (!(result.getLocation() instanceof LocationFactory)) {
			log.warn("Result type has location, but no CACSLLocation: " + result.getShortDescription() + " ("
					+ result.getClass() + ")");
			return;
		}

		final CACSLLocation loc = (CACSLLocation) result.getLocation();
		// seems legit, start the reporting

		if (result instanceof CounterExampleResult) {
			reportProblem(CCheckerDescriptor.CE_ID, result, loc);
		} else if (result instanceof UnprovableResult) {
			reportProblem(CCheckerDescriptor.UN_ID, result, loc);
		} else if (result instanceof ProcedureContractResult) {
			reportProblem(CCheckerDescriptor.IN_ID, result, loc);
		} else if (result instanceof InvariantResult) {
			reportProblem(CCheckerDescriptor.IN_ID, result, loc);
		} else if (result instanceof TerminationArgumentResult) {
			reportProblem(CCheckerDescriptor.IN_ID, result, loc);
		} else if (result instanceof PositiveResult) {
			reportProblem(CCheckerDescriptor.POS_ID, result, loc);
		} else if (result instanceof SyntaxErrorResult) {
			reportProblem(CCheckerDescriptor.SYNERR_ID, result, loc);
		} else if (result instanceof UnsupportedSyntaxResult) {
			// TODO: Introduce new String in CCheckerDescriptor for
			// unsupported Syntax?
			reportProblem(CCheckerDescriptor.SYNERR_ID, result, loc);
		} else if (result instanceof TypeErrorResult) {
			// TODO: Introduce new String in CCheckerDescriptor for
			// type error?
			reportProblem(CCheckerDescriptor.SYNERR_ID, result, loc);
		} else if (result instanceof TimeoutResultAtElement) {
			reportProblem(CCheckerDescriptor.TIMEOUT_ID, result, loc);
		} else if (result instanceof GenericResultAtElement<?>) {
			reportProblem(severityToCheckerDescriptor(((GenericResultAtElement<?>) result).getSeverity()), result, loc);
		} else if (result instanceof GenericResultAtLocation) {
			reportProblem(severityToCheckerDescriptor(((GenericResultAtLocation) result).getSeverity()), result, loc);
		} else {
			log.warn("Result type unknown: " + result.getShortDescription() + " (" + result.getClass() + ")");
		}
	}

	private void reportProblem(final String descriptorId, final IResult result, final CACSLLocation loc) {
		if (loc instanceof CLocation) {
			final IASTNode node = ((CLocation) loc).getNode();
			if (node != null) {
				reportProblem(descriptorId, node, result.getShortDescription(), CDTResultStore.addHackyResult(result));
				return;
			}
		}
		reportProblem(descriptorId, getFile(), loc.getStartLine(), result.getShortDescription(),
				CDTResultStore.addHackyResult(result));
	}

	private String severityToCheckerDescriptor(final Severity severity) {
		if (severity.equals(Severity.INFO)) {
			return CCheckerDescriptor.GENERIC_INFO_RESULT_ID;
		} else if (severity.equals(Severity.WARNING)) {
			return CCheckerDescriptor.GENERIC_WARNING_RESULT_ID;
		} else if (severity.equals(Severity.ERROR)) {
			return CCheckerDescriptor.GENERIC_ERROR_RESULT_ID;
		} else {
			throw new IllegalArgumentException("unknown severity");
		}
	}

	@Override
	public void initPreferences(final IProblemWorkingCopy problem) {
		super.initPreferences(problem);
		// per default we set the Launch Mode to "on demand"
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_AS_YOU_TYPE, false);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_DEMAND, true);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_FULL_BUILD, false);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_INC_BUILD, false);
		// we want to choose the toolchains which we use!
		// we read out the Directory "Toolchains", and create prefs
		File toolchainDir = null;
		final URL url = FileLocator.find(Platform.getBundle(Activator.PLUGIN_ID), new Path("toolchains"), null);
		try {
			final URI uri = new URI(FileLocator.toFileURL(url).toString().replace(" ", "%20"));
			toolchainDir = new File(uri);
		} catch (final IOException e2) {
			e2.printStackTrace();
		} catch (final URISyntaxException e) {
			e.printStackTrace();
		}

		// Iterate over all Files in the Directory
		// to create the internal map of all possible toolchains!
		for (final File f : toolchainDir.listFiles()) {
			final String[] params = f.getName().split("\\.");
			final String tName = params[0];
			if (tName.equals("") || params.length < 2 || !params[1].equals("xml")) {
				continue;
			}

			mToolchainFiles.put(tName, f);
		}
	}

	public void setServices(final IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
	}

	public void setStorage(final IToolchainStorage storage) {
		sStorage = storage;
	}

	public static IToolchainStorage getStorage() {
		return sStorage;
	}

}
