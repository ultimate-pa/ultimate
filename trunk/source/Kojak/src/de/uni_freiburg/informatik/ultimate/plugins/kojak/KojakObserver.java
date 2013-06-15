/**
 *
 */
package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.IErrorTrace;
import de.uni_freiburg.informatik.ultimate.plugins.kojak.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

/**
 * This class is the main class of the Kojak Model Checker.
 * 
 */

public class KojakObserver implements IUnmanagedObserver {
	
	public enum Result { CORRECT, TIMEOUT , MAXEDITERATIONS , UNKNOWN , INCORRECT }
	
	protected static Logger sLogger =
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	RootNode mRoot;
	
	@Override
	public boolean process(IElement root) {
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();
		TAPreferences taPrefs = rootAnnot.getTaPrefs();
		IEclipsePreferences kojakPrefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		
		int maxStepNumber = kojakPrefs.getInt(PreferenceValues.NAME_MAXSTEPNUMBER, PreferenceValues.VALUE_MAXSTEPNUMBER_DEFAULT);
		sLogger.info("Maximum number of iterations is set to " + maxStepNumber);

		int timeout = kojakPrefs.getInt(PreferenceValues.NAME_TIMEOUT, PreferenceValues.VALUE_TIMEOUT_DEFAULT);
		sLogger.info("Timeout is set to " + timeout + "seconds");
		
		boolean libmode = kojakPrefs.getBoolean(PreferenceValues.NAME_LIBRARYMODE, PreferenceValues.VALUE_LIBRARYMODE_DEFAULT);
		sLogger.info("Library mode is " + (libmode?"on.":"off."));
		
		String dumpPath = kojakPrefs.get(PreferenceValues.NAME_DUMPPATH, PreferenceValues.VALUE_DUMPPATH_DEFAULT);
		if (dumpPath != ""){
			dumpPath += (dumpPath.endsWith(System.getProperty("file.separator"))?"":System.getProperty("file.separator"));
		}
		// 2nd, 4th and 5th parameter of SmtManager Constructor have no effect.
		SmtManager smtManager = new SmtManager(rootAnnot.getBoogie2Smt(), 
				Solver.SMTInterpol, rootAnnot.getGlobalVars(), rootAnnot.getModGlobVarManager(),
				false, "");
		
		Map<String, Collection<ProgramPoint>> proc2errNodes = 
				rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}
		
		
		long timoutMilliseconds = timeout * 1000;
		UltimateServices.getInstance().setDeadline(
				System.currentTimeMillis() + timoutMilliseconds);
		//wird noch nicht gecheckt. Plugin muss continueProcessing() aufrufen. Wie deaktiviert man das Timeout?
		
		Result overallResult = Result.CORRECT;	

		KojakEngine kojak = new KojakEngine(
				((RootNode) root), smtManager, taPrefs);

		Pair<Result, IErrorTrace> kojakResult = kojak.run(maxStepNumber, libmode);
		Result result = kojakResult.getEntry1();
		mRoot = kojak.getRoot();
		
		
		switch (result) {
		case CORRECT:
			PositiveResult pResult = 
				new PositiveResult<RcfgElement>(
						null,
						Activator.PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence(),
						null);
			pResult.setShortDescription("Program is correct.");
			reportResult(pResult);
			sLogger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:SAFE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			break;
		case INCORRECT:
			IErrorTrace errorTrace = kojakResult.getEntry2();
			CounterExampleResult ctxRes = 
					new CounterExampleResult<RcfgElement>(
							null,
							Activator.PLUGIN_ID,
							UltimateServices.getInstance().getTranslatorSequence(),
							errorTrace.getErrorLocation(),
							null);
			ctxRes.setFailurePath(errorTrace.getLocations());
			ctxRes.setShortDescription("Program is incorrect." +
					"Found error at location " + errorTrace.getErrorLocation());
			ctxRes.setLongDescription(errorTrace.toString());
			reportResult(ctxRes);
			overallResult = result;
			sLogger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:UNSAFE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			break;
		case TIMEOUT:
			TimeoutResult timeOutRes = 
				new TimeoutResult<RcfgElement>(
						null,
						Activator.PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence(),
						null,
						"Program could not be checked. Kojak timed out.");
			reportResult(timeOutRes);
			if (overallResult != Result.INCORRECT) {
				overallResult = result;
			}
			sLogger.info("!-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:TIMEOUT(" + timeout +
					" secs.):-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			break;
		case UNKNOWN:
			IErrorTrace unknownTrace = kojakResult.getEntry2();
			UnprovableResult uknRes = 
					new UnprovableResult<RcfgElement>(
							null,
							Activator.PLUGIN_ID,
							UltimateServices.getInstance().getTranslatorSequence(),
							unknownTrace.getErrorLocation());
			uknRes.setFailurePath(unknownTrace.getLocations());
			uknRes.setShortDescription("SMT solver returned unknown result.");
			uknRes.setLongDescription(unknownTrace.toString());
			reportResult(uknRes);
			if (overallResult != Result.INCORRECT) {
				overallResult = result;
			}
			sLogger.info("!-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:UNKNOWN:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			break;
		case MAXEDITERATIONS:
			TimeoutResult maxedIterationsRes = 
				new TimeoutResult<RcfgElement>(
						null,
						Activator.PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence(),
						null,
						"Program could not be checked. Kojak timed out.");
			reportResult(maxedIterationsRes);
			if (overallResult != Result.INCORRECT) {
				overallResult = result;
			}
			sLogger.info("!-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:MAXSTEPS(" + maxStepNumber +
					" steps):-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			break;
		}
			
		this.dumpStatsToConsole(smtManager);
		return false;
	}	
		
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.PLUGIN_ID, res);
	}
	
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
	
	private void dumpStatsToConsole(SmtManager smtManager) {
		sLogger.warn("PC#: "+ smtManager.getInterpolQueries());
		sLogger.warn("TIME#: "+ smtManager.getInterpolQuriesTime());
		sLogger.warn("EC#: "+ smtManager.getNontrivialSatQueries());
		sLogger.warn("TIME#: "+ smtManager.getSatQuriesTime());
	}
	
	public IElement getRoot() {
		return mRoot;
	}
}
