package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Independence relation that considers semantic independence of abstractions of
 * the given actions. The abstraction is defined by the set of valid pre- /
 * post-condition pairs in a given set of predicates.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            This relation is non-conditional, so this parameter is not used.
 */
public class AbstractSemanticIndependenceRelation<STATE> implements IIndependenceRelation<STATE, IIcfgTransition<?>> {

	private final IHoareTripleChecker mChecker;
	private final Set<IPredicate> mPredicates;
	private final Set<IProgramVar> mAllVariables;

	private final Map<IInternalAction, HashRelation<IPredicate, IPredicate>> mAbstractionCache = new HashMap<>();

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	public AbstractSemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker checker, final Set<IPredicate> predicates, final Set<IProgramVar> allVariables) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		mChecker = checker;
		mPredicates = predicates;
		mAllVariables = allVariables;
	}

	@Override
	public boolean isSymmetric() {
		return false;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public boolean contains(final STATE state, final IIcfgTransition<?> a, final IIcfgTransition<?> b) {
		assert a instanceof IInternalAction && b instanceof IInternalAction;
		final HashRelation<IPredicate, IPredicate> abstrA = computeAbstraction((IInternalAction) a);
		final HashRelation<IPredicate, IPredicate> abstrB = computeAbstraction((IInternalAction) b);

		final UnmodifiableTransFormula tfA = concretizeAbstraction(abstrA);
		final UnmodifiableTransFormula tfB = concretizeAbstraction(abstrB);

		assert TransFormulaUtils.checkImplication(a.getTransformula(), tfA,
				mManagedScript) != LBool.SAT : "Abstraction is not a superset of concrete relation";
		assert TransFormulaUtils.checkImplication(b.getTransformula(), tfB,
				mManagedScript) != LBool.SAT : "Abstraction is not a superset of concrete relation";

		final UnmodifiableTransFormula transFormula1 = compose(tfA, tfB);
		final UnmodifiableTransFormula transFormula2 = compose(tfB, tfA);
		final LBool result = TransFormulaUtils.checkImplication(transFormula2, transFormula1, mManagedScript);

		return result == LBool.UNSAT;
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;

		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		final boolean tryAuxVarElimination = true;

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify,
				tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique,
				Arrays.asList(first, second));
	}

	private HashRelation<IPredicate, IPredicate> computeAbstraction(final IInternalAction action) {
		if (mAbstractionCache.containsKey(action)) {
			return mAbstractionCache.get(action);
		}

		HashRelation<IPredicate, IPredicate> abstraction = new HashRelation<>();
		for (final IPredicate pre : mPredicates) {
			for (final IPredicate post : mPredicates) {
				final IHoareTripleChecker.Validity result = mChecker.checkInternal(pre, action, post);
				assert result == Validity.VALID || result == Validity.INVALID : "Could not determine abstraction";
				abstraction.addPair(pre, post);

			}
		}
		mAbstractionCache.put(action, abstraction);

		return abstraction;
	}

	private UnmodifiableTransFormula concretizeAbstraction(HashRelation<IPredicate, IPredicate> abstraction) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		// Construct a substitution to apply to postconditions.
		final Map<TermVariable, Term> substitutionMap = new HashMap<>();
		for (IProgramVar variable : mAllVariables) {
			TermVariable original = variable.getTermVariable();
			TermVariable replacement = mManagedScript.constructFreshCopy(original);
			substitutionMap.put(original, replacement);

			// All variables are output variables (may change arbitrarily, unless
			// constrained below).
			tfb.addOutVar(variable, replacement);
		}
		final Substitution postSubstitution = new Substitution(mManagedScript.getScript(), substitutionMap);

		final List<Term> conjuncts = new ArrayList<>(abstraction.size());

		for (Map.Entry<IPredicate, IPredicate> pair : abstraction) {
			final IPredicate pre = pair.getKey();
			final IPredicate post = pair.getValue();

			// Add program constants.
			for (IProgramConst constant : pre.getConstants()) {
				tfb.addProgramConst(constant);
			}
			for (IProgramConst constant : post.getConstants()) {
				tfb.addProgramConst(constant);
			}

			// Free variables of the precondition are input variables.
			for (IProgramVar variable : pre.getVars()) {
				tfb.addInVar(variable, variable.getTermVariable());
			}

			final Term postFormula = postSubstitution.transform(post.getFormula());
			final Term conjunct = SmtUtils.implies(mManagedScript.getScript(), pre.getFormula(), postFormula);
			conjuncts.add(conjunct);
		}

		tfb.setFormula(SmtUtils.and(mManagedScript.getScript(), conjuncts));

		return tfb.finishConstruction(mManagedScript);
	}

}
