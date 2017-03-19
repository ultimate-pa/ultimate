package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.awt.List;
import java.util.ArrayList;
import java.util.logging.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class FastUprCore {

	private final Term mRelation;
	private final UnmodifiableTransFormula mFormula;
	private final UnmodifiableTransFormula mResult;
	private final ILogger mLogger;
	ReplacementVarFactory mReplacementVarFactory;
	ManagedScript mManagedScript;
	IUltimateServiceProvider mServices;
	
	public FastUprCore(UnmodifiableTransFormula formula, ReplacementVarFactory factory, ManagedScript managedScript, ILogger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mFormula = formula;
		mRelation = formula.getFormula();
		mResult = prefixLoop();
		mServices = services;
	}
	
	
	
	
	private UnmodifiableTransFormula prefixLoop() {
		int b = 0;
		boolean resultFound = false;
		while(!resultFound) {
			periodLoop(b++);
		}
		
		return null;
	}
	
	private void periodLoop(int b) {
		for (int c = 0; c <= b; c++) {
			ConsistencyChecker checker = new ConsistencyChecker(mLogger, mManagedScript, mServices, mFormula, b, c);
			if(checker.isSuccess()) {
				checker.getResult();
				return;
			}
			
		}
	}
}
