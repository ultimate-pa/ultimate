package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class ConsistencyChecker {

	private final Term mResult;
	private final boolean mSuccess;
	ManagedScript mManagedScript;
	ILogger mLogger;
	IUltimateServiceProvider mServices;
	
	public ConsistencyChecker(ILogger logger, ManagedScript managedScript, IUltimateServiceProvider services, UnmodifiableTransFormula formula, int b, int c) {
		mLogger = logger;
		mServices = services;
		mManagedScript = managedScript;
		Script script = mManagedScript.getScript();
		mResult = check(formula, b, c, script);
		mSuccess = (mResult.equals(null) ? true : false);
	}

	private Term check(UnmodifiableTransFormula formula, int b, int c, Script script) {
		for (int k = 0; k <= 2; k++) {
			if(!solve(formula, b, c, k, script)) {
				// return S1
				return null;	
			}
		}
		
		return null;
	}
	
	private boolean solve(UnmodifiableTransFormula formula, int b, int c, int k, Script script) {
		UnmodifiableTransFormula toCheck = FastUPRUtils.composition(mLogger, mServices, mManagedScript, formula, b + (k * c));
		return (script.checkSatAssuming(toCheck.getFormula()).equals(LBool.SAT));
	}
	
	public boolean isSuccess() {
		return mSuccess;
	}

	public Term getResult() {
		return mResult;
	}

}
