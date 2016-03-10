package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <LOCATION>
 */
public class RcfgDebugHelper<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>, LOCATION>
		implements IDebugHelper<STATE, CodeBlock, IBoogieVar, LOCATION> {

	private final Boogie2SMT mBoogie2Smt;
	private final ModifiableGlobalVariableManager mGlobalVariableManager;
	private final Script mScript;
	private final Logger mLogger;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final RootAnnot rootAnnot, final IUltimateServiceProvider services) {
		mScript = rootAnnot.getScript();
		mBoogie2Smt = rootAnnot.getBoogie2SMT();
		mGlobalVariableManager = rootAnnot.getModGlobVarManager();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean isPostSound(final STATE pre, final List<STATE> postStates, final CodeBlock transition) {
		if (transition instanceof Call || transition instanceof Return) {
			// TODO: The current hoare triple checker is not usable for call/return, so we just say its sound (but it
			// should be anyways)
			return true;
		}
		final IPredicate precond = createPredicateFromState(Collections.singletonList(pre));
		final IPredicate postcond = createPredicateFromState(postStates);
		final TransFormula tf = transition.getTransitionFormula();
		final Set<BoogieVar> modifiableGlobalsBefore = mGlobalVariableManager
				.getModifiedBoogieVars(transition.getPreceedingProcedure());
		final Set<BoogieVar> modifiableGlobalsAfter = mGlobalVariableManager
				.getModifiedBoogieVars(transition.getSucceedingProcedure());

		final LBool result = PredicateUtils.isInductiveHelper(mBoogie2Smt, precond, postcond, tf,
				modifiableGlobalsBefore, modifiableGlobalsAfter);
		if (result != LBool.UNSAT) {
			mLogger.fatal("Soundness check failed for the following triple:");
			mLogger.fatal("Pre: {" + precond.getFormula().toStringDirect() + "}");
			mLogger.fatal(tf.getFormula().toStringDirect());
			mLogger.fatal("Post: {" + postcond.getFormula().toStringDirect() + "}");
		}
		return result == LBool.UNSAT;
	}

	private IPredicate createPredicateFromState(Collection<STATE> states) {
		Term acc = mScript.term("false");

		for (final STATE state : states) {
			acc = Util.or(mScript, acc, state.getTerm(mScript, mBoogie2Smt));
		}

		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mBoogie2Smt);
		return new BasicPredicate(sIllegalPredicates--, tvp.getProcedures(), acc, tvp.getVars(),
				tvp.getClosedFormula());
	}
}
