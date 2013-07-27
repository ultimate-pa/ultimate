package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.IErrorTrace;
import de.uni_freiburg.informatik.ultimate.plugins.kojak.KojakObserver.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;

public class KojakEngine {

	private RootNode mRoot, mOriginalRoot;
	private SmtManager mSmtManager;
	private Logger mLogger;
	private TAPreferences mTAPrefs;
	private static IPredicate mTruePredicate;
	private static IPredicate mFalsePredicate;
	
	public KojakEngine(RootNode rootNode,
			SmtManager smtManager, TAPreferences taPrefs) {
		mOriginalRoot = rootNode;
		mRoot = rootNode;
		mSmtManager = smtManager;
		mLogger =  UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		mTAPrefs = taPrefs;
		mTruePredicate = mSmtManager.newTruePredicate();
		mFalsePredicate = mSmtManager.newFalsePredicate();
	}
	
	public Pair<Result, IErrorTrace> run(int maxIterations, boolean libmode) {
		IErrorTrace errorTrace = new ErrorTrace(mSmtManager.getScript(),
				new ArrayList<IElement>(), new Term[0]);

		for (RCFGEdge edge : mRoot.getOutgoingEdges()) {
			if (!libmode && mRoot.getOutgoingEdges().size() > 1) {
				if(!edge.getTarget().getPayload().getName().contains("main")) {
					continue;
				}
			}
			int iteration = 0;
			do {
				ErrorPathBuilder epBuilder = new ErrorPathBuilder();	
				Pair<KojakProgramPoint[], NestedWord<CodeBlock>> errorNW = 
						epBuilder.getErrorPathAsNestedWord(edge);
				
				//START: Output error path
				if (errorNW != null) {
					mLogger.debug("found an error path in method " + 
							edge.getTarget().toString().replaceAll("INIT", ""));
					for (int i = 0; i < errorNW.getEntry2().length(); i++) {
						if (errorNW.getEntry2().getSymbol(i) instanceof Call) {
							mLogger.debug("CALL");
							mLogger.debug(errorNW.getEntry1()[i]);
						}
						else if (errorNW.getEntry2().getSymbol(i) instanceof Return) {
							mLogger.debug("RETURN");
							mLogger.debug(errorNW.getEntry1()[i]);
						}
						else {
							mLogger.debug(errorNW.getEntry2().getSymbol(i).
									getPrettyPrintedStatements());
							mLogger.debug(errorNW.getEntry1()[i]);
						}
					}
				} else {
					mLogger.debug("no error path found in method " + 
							edge.getTarget().toString().replaceAll("INIT", ""));
					return new Pair<Result, IErrorTrace>(
							Result.CORRECT, errorTrace);
				}
				
				if(errorNW != null) {
					IPredicate[] interpolants = getInterpolants(errorNW.getEntry2());
					if (interpolants != null) {
						Split splitter = new Split(mSmtManager);
						HashSet<CodeBlock> slicableEdges = splitter.split(errorNW, interpolants);
						Slicing slicer = new Slicing(mSmtManager);
						slicer.slice(slicableEdges);
						break;
					} else {
						return new Pair<Result, IErrorTrace>(
								Result.INCORRECT, errorTrace);
					}
				}
			} while(++iteration != maxIterations);
		}
		return new Pair<Result, IErrorTrace>(
				Result.MAXEDITERATIONS, errorTrace);
	}
	
	private IPredicate[] getInterpolants(NestedWord<CodeBlock> errorPathNW) {
		TraceChecker traceChecker = new TraceChecker(mSmtManager, 
				mOriginalRoot.getRootAnnot().getModGlobVarManager(), 
				dumpInitialize());
		
		LBool isSafe = traceChecker.checkTrace(mTruePredicate, 
				mFalsePredicate, errorPathNW);
		if(isSafe == LBool.UNSAT) {
			PredicateUnifier pu = new PredicateUnifier(mSmtManager, mTruePredicate, mFalsePredicate);
			traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu);
			IPredicate[] interpolants = traceChecker.getInterpolants();
			return interpolants;
		}
			
		return null;
	}
	
	public static IPredicate getTruePredicate() {
		return mTruePredicate;
	}
	
	public static IPredicate getFalsePredicate() {
		return mFalsePredicate;
	}
	
	private PrintWriter dumpInitialize() {
		File file = 
			new File(mTAPrefs.dumpPath() + "/" + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			return new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
		return null;
	}

	public RootNode getRoot() {
		return mRoot;
	}
}
