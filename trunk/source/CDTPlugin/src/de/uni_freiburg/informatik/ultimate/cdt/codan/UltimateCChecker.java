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
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;
import org.eclipse.cdt.codan.core.model.CheckerLaunchMode;
import org.eclipse.cdt.codan.core.model.IProblemWorkingCopy;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.cdt.codan.extension.AbstractFullAstChecker;
import de.uni_freiburg.informatik.ultimate.cdt.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtLocation;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

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
	public static String ID = "de.uni_freiburg.informatik.ultimate.cdt." + "codan.UltimateCChecker";

	/**
	 * In this map we store the listed files out of the directory.
	 */
	private HashMap<String, File> mToolchainFiles;

	private static CDTController sController;

	/**
	 * The Constructor of this Checker
	 * 
	 * @throws Exception
	 */
	public UltimateCChecker() throws Exception {
		super();
		mToolchainFiles = new HashMap<String, File>();

		sController = new CDTController();
		sController.startUltimate();
	}

	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		sController.close();
	}

	@Override
	public void processAst(IASTTranslationUnit ast) {
		// first, clear all old results
		CDTResultStore.clearHackyResults();
		CDTResultStore.clearResults();

		// run ultimate
		try {
			sController.runToolchain(getToolchainPath(), ast);
		} catch (Exception e) {
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

	}

	private String getToolchainPath() {
		// obtain selected toolchain from preferences
		File toolChain = null;
		IEclipsePreferences prefs = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		String selectedToolchain = prefs.get(PreferencePage.TOOLCHAIN_SELECTION_TEXT, "");

		for (Entry<String, File> entry : mToolchainFiles.entrySet()) {
			if (selectedToolchain.equals(entry.getKey())) {
				toolChain = entry.getValue();
				break;
			}
		}
		return toolChain.getAbsolutePath();
	}

	private void updateFileView(final String completePath) {
		// After finishing the Ultimate run we update the FileView
		// We have to do this in this asynch manner, because otherwise we would
		// get a NullPointerException, because we are not in the UI Thread
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			public void run() {
				// Present results of the actual run!
				IViewPart vpart = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage()
						.findView(ResultList.ID);
				if (vpart instanceof ResultList) {
					((ResultList) vpart).setViewerInput(completePath);
				}
				// open the file on which the actual run happened!
				File fileToOpen = new File(completePath);
				if (fileToOpen.exists() && fileToOpen.isFile()) {
					IFileStore fileStore = EFS.getLocalFileSystem().getStore(fileToOpen.toURI());
					IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();

					try {
						IDE.openEditorOnFileStore(page, fileStore);
					} catch (PartInitException e) {
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
	private void reportProblems(String fileName) {
		Logger log = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		// we obtain the results by UltimateServices
		Set<String> tools = UltimateServices.getInstance().getResultMap().keySet();

		// we iterate over the key set, each key represents the name
		// of the tool, which created the results
		for (String toolID : tools) {
			CDTResultStore.addResults(fileName, toolID, UltimateServices.getInstance().getResultMap().get(toolID));
			List<IResult> resultsOfTool = UltimateServices.getInstance().getResultMap().get(toolID);
			if(resultsOfTool == null){
				log.debug("No results for " + toolID);
				continue;
			}
			for (IResult result : resultsOfTool) {
				if (result instanceof IResultWithLocation) {
					reportProblemWithLocation((IResultWithLocation) result, log);
				} else {
					reportProblemWithoutLocation(result, log);
				}
			}
		}
	}

	private void reportProblemWithoutLocation(IResult result, Logger log) {
		if (result instanceof ExceptionOrErrorResult) {
			reportProblem(CCheckerDescriptor.GENERIC_ERROR_RESULT_ID, getFile(), 0, result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		} else {
			reportProblem(CCheckerDescriptor.GENERIC_INFO_RESULT_ID, getFile(), 0, result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		}
	}

	private void reportProblemWithLocation(IResultWithLocation result, Logger log) {
		if(result.getLocation() == null){
			log.warn("Result type should have location, but has none: " + result.getShortDescription() + " ("
					+ result.getClass() + ")");
			return;
		}
		
		if (!(result.getLocation() instanceof CACSLLocation)) {
			log.warn("Result type has location, but no CACSLLocation: " + result.getShortDescription() + " ("
					+ result.getClass() + ")");
			return;
		}
		
		CACSLLocation loc = (CACSLLocation) result.getLocation();
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
			//TODO: Introduce new String in CCheckerDescriptor for 
			// unsupported Syntax?
			reportProblem(CCheckerDescriptor.SYNERR_ID, result, loc);
		} else if (result instanceof TypeErrorResult) {
			//TODO: Introduce new String in CCheckerDescriptor for 
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

	private void reportProblem(String descriptorId, IResult result, CACSLLocation loc) {
		if (loc.getcNode() != null) {
			reportProblem(descriptorId, loc.getcNode(), result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		} else {
			reportProblem(descriptorId, getFile(), loc.getStartLine(), result.getShortDescription(),
					CDTResultStore.addHackyResult(result));
		}
	}

	private String severityToCheckerDescriptor(Severity severity) {
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
	public void initPreferences(IProblemWorkingCopy problem) {
		super.initPreferences(problem);
		// per default we set the Launch Mode to "on demand"
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_AS_YOU_TYPE, false);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_DEMAND, true);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_FULL_BUILD, false);
		getLaunchModePreference(problem).setRunningMode(CheckerLaunchMode.RUN_ON_INC_BUILD, false);
		// we want to choose the toolchains which we use!
		// we read out the Directory "Toolchains", and create prefs
		File toolchainDir = null;
		URL url = FileLocator.find(Platform.getBundle(Activator.PLUGIN_ID), new Path("toolchains"), null);
		try {
			URI uri = new URI(FileLocator.toFileURL(url).toString().replace(" ", "%20"));
			toolchainDir = new File(uri);
		} catch (IOException e2) {
			e2.printStackTrace();
		} catch (URISyntaxException e) {
			e.printStackTrace();
		}

		// Iterate over all Files in the Directory
		// to create the internal map of all possible toolchains!
		for (File f : toolchainDir.listFiles()) {
			String[] params = f.getName().split("\\.");
			String tName = params[0];
			if (tName.equals("") || params.length < 2 || !params[1].equals("xml")) {
				continue;
			}

			mToolchainFiles.put(tName, f);
		}
	}
}
