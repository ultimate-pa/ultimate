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
import org.osgi.framework.Bundle;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.cdt.codan.extension.AbstractFullAstChecker;
import de.uni_freiburg.informatik.ultimate.cdt.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

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
	public static String ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.UltimateCChecker";

	/**
	 * In this map we store the listed files out of the directory.
	 */
	private HashMap<String, File> toolchainFiles;

	/**
	 * The Constructor of this Checker
	 */
	public UltimateCChecker() {
		super();
		this.toolchainFiles = new HashMap<String, File>();
	}

	@Override
	public void processAst(IASTTranslationUnit ast) {		
		UltimateCore app = Activator.app;
		// First we have to set the AST of the Applicationstem.err.println(e);
		app.setM_ParsedAST(ast);
		// Second we need to set the .dummy-File
		// We cannot use absolute Paths here, because we are in
		// Plugin-Development
//		File file = new File("/home/matthias/stalin/trunk/examples/settings/buchiAutomizer/staged300");
//		app.setSettingsFile(file);

		File dummyFile = null;
		Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
		URL url = FileLocator.find(bundle, new Path("dummyFile/cdt.dummy"),
				null);
		try {
			URI uri = new URI(FileLocator.toFileURL(url).toString()
					.replace(" ", "%20"));
			dummyFile = new File(uri);
		} catch (IOException e2) {
			e2.printStackTrace();
		} catch (URISyntaxException e) {
			e.printStackTrace();
		}

		app.setM_InputFile(dummyFile);
		// Third thing is that we have to set the toolchain
		File toolChain = null;
		IEclipsePreferences prefs = InstanceScope.INSTANCE
				.getNode(Activator.PLUGIN_ID);
		String selectedToolchain = prefs.get(PreferencePage.TOOLCHAIN_SELECTION_TEXT, "");
		
		for (Entry<String, File> entry : toolchainFiles.entrySet()) {
			if (selectedToolchain.equals(entry.getKey())) {
				toolChain = entry.getValue();
				break;
			}
		}

		app.setToolchainXML(toolChain);
		// Now we start Ultimate
		// ApplicationContext = null ... maybe this is could be a problem
		try {
			app.start(null);
		} catch (Exception e) {
			e.printStackTrace();
		}
		// So after this run, we can obtain the results
		// -> so we have to prepare them for displaying to the user
		// reportProblem(...) --> is used for displaying
		// new CodanProblem("...", "...")
		// CodanSeverity.Error;
		// CodanSeverity.Warning;
		// CodanSeverity.Info;
		final String completePath = ast.getFilePath();
		reportProblems(completePath);
		// After finishing the Ultimate run we update the FileView
		// We have to do this in this asynch manner, because otherwise we would
		// get a NullPointerException, because we are not in the UI Thread
		PlatformUI.getWorkbench().getDisplay().asyncExec(new Runnable() {
			public void run() {
				// Present results of the actual run!
				IViewPart vpart = PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow().getActivePage()
						.findView(ResultList.ID);
				if (vpart instanceof ResultList) {
					((ResultList) vpart).setViewerInput(completePath);
				}
				// open the file on which the actual run happened!
				File fileToOpen = new File(completePath);
				if (fileToOpen.exists() && fileToOpen.isFile()) {
					IFileStore fileStore = EFS.getLocalFileSystem().getStore(
							fileToOpen.toURI());
					IWorkbenchPage page = PlatformUI.getWorkbench()
							.getActiveWorkbenchWindow().getActivePage();

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
		// we obtain the results by UltimateServices
		Set<String> tools = UltimateServices.getInstance().getResultMap()
				.keySet();
		// we iterate over the key set, each key represents the name
		// of the tool, which created the results
		for (String toolID : tools) {
			CDTResultStore.addResults(fileName, toolID, UltimateServices.getInstance()
					.getResultMap().get(toolID));
			List<IResult> resultsOfTool = UltimateServices.getInstance().getResultMap()
					.get(toolID);
			for (IResult iresult : resultsOfTool) {
				if (!(iresult instanceof IResultWithLocation)) {
					//FIXME: implement result without location
					throw new UnsupportedOperationException(
							"result without location not implemented yet");
				}
				IResultWithLocation result = (IResultWithLocation) iresult;
				if (!(result.getLocation() instanceof CACSLLocation)) {
					continue;
				}
				CACSLLocation loc = (CACSLLocation) result.getLocation();
				if (loc == null) {
					// so we have a result with no valid location
					// --> so we jump over this result
					continue;
				}
				if (result instanceof CounterExampleResult) {
					CounterExampleResult cer = (CounterExampleResult) result;
					// We found a counterexample so we have an error!
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.CE_ID, loc.getcNode(),
								cer.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.CE_ID, this.getFile(),
								loc.getStartLine(), cer.getShortDescription());
					}
				} else if (result instanceof ProcedureContractResult) {
					ProcedureContractResult pContr = (ProcedureContractResult) result;
					// We found an invariant, this information for the user!
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.IN_ID, loc.getcNode(),
								pContr.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.IN_ID, this.getFile(),
								loc.getStartLine(),
								pContr.getShortDescription());
					}
				} else if (result instanceof InvariantResult) {
					InvariantResult invar = (InvariantResult) result;
					// We found an invariant, this information for the user!
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.IN_ID, loc.getcNode(),
								invar.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.IN_ID, this.getFile(),
								loc.getStartLine(),
								invar.getShortDescription());
					}
				} else if (result instanceof TerminationArgumentResult) {
					TerminationArgumentResult invar = (TerminationArgumentResult) result;
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.IN_ID, loc.getcNode(),
								invar.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.IN_ID, this.getFile(),
								loc.getStartLine(),
								invar.getShortDescription());
					}
				} else if (result instanceof UnprovableResult) {
					UnprovableResult unprov = (UnprovableResult) result;
					// We cannot prove this, might be wrong or right...
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.UN_ID, loc.getcNode(),
								unprov.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.UN_ID, this.getFile(),
								loc.getStartLine(),
								unprov.getShortDescription());
					}
				} else if (result instanceof PositiveResult) {
					PositiveResult pos = (PositiveResult) result;
					// We found a positive result, this was proved by Ultimate
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.POS_ID,
								loc.getcNode(), pos.getShortDescription());
					} else {
						// We have ann AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.POS_ID,
								this.getFile(), loc.getStartLine(),
								pos.getShortDescription());
					}
				} else if (result instanceof SyntaxErrorResult) {
					SyntaxErrorResult err = (SyntaxErrorResult) result;
					// We found a positive result, this was proved by Ultimate
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.SYNERR_ID,
								loc.getcNode(), err.getShortDescription());
					} else {
						// We have ann AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.SYNERR_ID,
								this.getFile(), loc.getStartLine(),
								err.getShortDescription());
					}
				} else if (result instanceof TimeoutResultAtElement) {
					TimeoutResultAtElement err = (TimeoutResultAtElement) result;
					// We found a positive result, this was proved by Ultimate
					if (loc.getcNode() != null) {
						reportProblem(CCheckerDescriptor.TIMEOUT_ID,
								loc.getcNode(), err.getShortDescription());
					} else {
						// We have ann AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(CCheckerDescriptor.TIMEOUT_ID,
								this.getFile(), loc.getStartLine(),
								err.getShortDescription());
					}
				} else if (result instanceof GenericResultAtElement<?>) {
					GenericResultAtElement<?> err = (GenericResultAtElement<?>) result;
					String id;
					if (err.getSeverity().equals(Severity.INFO)) {
						id = CCheckerDescriptor.GENERIC_INFO_RESULT_ID;
					} else if (err.getSeverity().equals(Severity.WARNING)) {
						id = CCheckerDescriptor.GENERIC_WARNING_RESULT_ID;
					} else if (err.getSeverity().equals(Severity.ERROR)) {
						id = CCheckerDescriptor.GENERIC_ERROR_RESULT_ID;
					} else {
						throw new IllegalArgumentException("unknown severity");
					}
					// We found an unsoundness warning, this was proved by Ultimate
					if (loc.getcNode() != null) {
						reportProblem(id,
								loc.getcNode(), err.getShortDescription());
					} else {
						// We have an AST-Node
						// ACSLNode acslNode = loc.getAcslNode();
						reportProblem(id,
								this.getFile(), loc.getStartLine(),
								err.getShortDescription());
					}
				} else {
					throw new UnsupportedOperationException(
							"Result Type not specified!");
				}
			}
		}
	}

	@Override
	public void initPreferences(IProblemWorkingCopy problem) {
		super.initPreferences(problem);
		// per default we set the Launch Mode to "on demand"
		getLaunchModePreference(problem).setRunningMode(
				CheckerLaunchMode.RUN_AS_YOU_TYPE, false);
		getLaunchModePreference(problem).setRunningMode(
				CheckerLaunchMode.RUN_ON_DEMAND, true);
		getLaunchModePreference(problem).setRunningMode(
				CheckerLaunchMode.RUN_ON_FULL_BUILD, false);
		getLaunchModePreference(problem).setRunningMode(
				CheckerLaunchMode.RUN_ON_INC_BUILD, false);
		// we want to choose the toolchains which we use!
		// we read out the Directory "Toolchains", and create prefs
		File toolchainDir = null;
		URL url = FileLocator.find(Platform.getBundle(Activator.PLUGIN_ID),
				new Path("toolchains"), null);
		try {
			URI uri = new URI(FileLocator.toFileURL(url).toString()
					.replace(" ", "%20"));
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
			if (tName.equals("") || params.length < 2
					|| !params[1].equals("xml")) {
				continue;
			}
			
			this.toolchainFiles.put(tName, f);		
		}
	}
}
