package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class HCPredicateFactory extends PredicateFactory {

	private ManagedScript mBackendSmtSolverScript;

	public HCPredicateFactory(IUltimateServiceProvider services, ManagedScript mgdScript, IIcfgSymbolTable symbolTable,
			SimplificationTechnique simplificationTechnique, XnfConversionTechnique xnfConversionTechnique) {
		super(services, mgdScript, symbolTable, simplificationTechnique, xnfConversionTechnique);
		mBackendSmtSolverScript = mgdScript;
	}

	
	public HCPredicate createDontCarePredicate(final HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = new HCPredicate(loc, 
				mBackendSmtSolverScript.term(this, HornUtilConstants.DONTCARE), 
				new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate createPredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = new HCPredicate(loc, mBackendSmtSolverScript.term(this, loc.toString()), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate truePredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = new HCPredicate(loc, mBackendSmtSolverScript.term(this, "true"), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}

	public HCPredicate falsePredicate(HornClausePredicateSymbol loc) {
		mBackendSmtSolverScript.lock(this); 
		final HCPredicate result = new HCPredicate(loc, mBackendSmtSolverScript.term(this, "false"), new HashMap<>());
		mBackendSmtSolverScript.unlock(this); 
		return result;
	}	
}
