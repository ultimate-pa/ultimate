package de.uni_freiburg.informatik.ultimate.reqtotest;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlob;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.BndResponsePatternUT;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InvariantPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class ReqToBuchi {

	private final ILogger mLogger;
	private final ReqSymbolExpressionTable mReqSymbolExpressionTable;
	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;
	private final ManagedScript mManagedScript;
	private final Boogie2SMT mBoogie2Smt;
	private final CddToSmt mCddToSmt;
	private final BoogieDeclarations mBoogieDeclarations;
	
	public ReqToBuchi(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final ReqSymbolExpressionTable reqSymbolExpressionTable){
		mLogger = logger;
		mReqSymbolExpressionTable = reqSymbolExpressionTable;
		final SolverSettings settings = SolverBuilder.constructSolverSettings("", SolverMode.External_DefaultMode,
				false, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, false, null);
		mScript = SolverBuilder.buildAndInitializeSolver(services, storage, SolverMode.External_DefaultMode, settings,
				false, false, Logics.ALL.toString(), "RtInconsistencySolver");
		mManagedScript = new ManagedScript(services, mScript);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mBoogieDeclarations = 	new BoogieDeclarations(reqSymbolExpressionTable.constructVariableDeclarations(), logger);
		mBoogie2Smt = new Boogie2SMT(mManagedScript, mBoogieDeclarations, false, services, false);
		mCddToSmt = new CddToSmt(services, storage, mScript, mBoogie2Smt,
				mBoogieDeclarations, mReqSymbolExpressionTable);
	}
	
	public List<ReqGuardGraph<String>> patternListToBuechi(List<PatternType> patternList){
		final List<ReqGuardGraph<String>> gs = new ArrayList<ReqGuardGraph<String>>();
		for (PatternType pattern: patternList) {
			if (! (pattern instanceof InitializationPattern)) {
				gs.add(patternToBuechi(pattern));
			} 
		}
		return gs;
	}

	public ReqGuardGraph<String> patternToBuechi(PatternType pattern){
		if(pattern instanceof InvariantPattern){
			return getInvariantPatternToBuechi(pattern);
		} else if(pattern instanceof BndResponsePatternUT){
			return getBndResponsePatternUTPatternToAutomaton(pattern);
		} else {
			throw new RuntimeException("Pattern type not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds after at most "c1" time units.
	 */
	private ReqGuardGraph<String> getBndResponsePatternUTPatternToAutomaton(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final Term S = mCddToSmt.toSmt(args.get(0));
			
			Term RandS = SmtUtils.and(mScript, R, S);
			Term notR = SmtUtils.not(mScript, R);
			Term notRandS = SmtUtils.and(mScript, notR, S);
			
			final ReqGuardGraph<String> q0 = new ReqGuardGraph<String>("q_0");
			final ReqGuardGraph<String> q1 = new ReqGuardGraph<String>("q_1");
			q0.connectOutgoing(q0, notR);
			q0.connectOutgoing(q1, R);
			q1.connectOutgoing(q1, RandS);
			q1.connectOutgoing(q0, notRandS);
			return q0;
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	/*
	 *  * {scope}, it is always the case that if "R" holds, then "S" holds as well.
	 */
	private ReqGuardGraph<String> getInvariantPatternToBuechi(PatternType pattern){
		if(pattern.getScope() instanceof SrParseScopeGlob) {
			final List<CDD> args = pattern.getCdds();
			final Term R = mCddToSmt.toSmt(args.get(1));
			final ReqGuardGraph<String> q0 = new ReqGuardGraph<String>("q_0");
			q0.connectOutgoing(q0, R);
			return q0;
		} else {
			throw new RuntimeException("Scope not implemented");
		}
	}
	
	
}
