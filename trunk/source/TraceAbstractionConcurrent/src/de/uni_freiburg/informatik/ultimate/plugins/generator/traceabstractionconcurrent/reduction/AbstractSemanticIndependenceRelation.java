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
 * It is recommended to wrap this relation in a
 * {@link CachedIndependenceRelation} for better performance.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class AbstractSemanticIndependenceRelation implements IIndependenceRelation<IPredicate, IIcfgTransition<?>> {

	private final IHoareTripleChecker mChecker;
	private final Set<IPredicate> mPredicates;
	private final Set<IProgramVar> mAllVariables;

	private final boolean mConditional;
	private final boolean mSymmetric;

	private final Map<IInternalAction, HashRelation<IPredicate, IPredicate>> mAbstractionCache = new HashMap<>();

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final static SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final static XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	/**
	 * Create a new variant of the abstract semantic independence relation.
	 *
	 * @param conditional
	 *            If set to true, the relation will be conditional: It will use the
	 *            given {@link IPredicate} as context to enable additional
	 *            commutativity. This subsumes the non-conditional variant.
	 * @param symmetric
	 *            If set to true, the relation will check for full commutativity. If
	 *            false, only semicommutativity is checked, which subsumes full
	 *            commutativity.
	 */
	public AbstractSemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker checker, final Set<IPredicate> predicates, final Set<IProgramVar> allVariables,
			final boolean conditional, final boolean symmetric) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		mChecker = checker;
		mPredicates = predicates;
		mAllVariables = allVariables;

		mConditional = conditional;
		mSymmetric = symmetric;
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(final IPredicate state, final IIcfgTransition<?> a, final IIcfgTransition<?> b) {
		assert a instanceof IInternalAction && b instanceof IInternalAction;
		final HashRelation<IPredicate, IPredicate> abstrA = computeAbstraction((IInternalAction) a);
		final HashRelation<IPredicate, IPredicate> abstrB = computeAbstraction((IInternalAction) b);

		final UnmodifiableTransFormula tfA = concretizeAbstraction(abstrA);
		final UnmodifiableTransFormula tfB = concretizeAbstraction(abstrB);

		assert TransFormulaUtils.checkImplication(a.getTransformula(), tfA,
				mManagedScript) != LBool.SAT : "Abstraction is not a superset of concrete relation";
		assert TransFormulaUtils.checkImplication(b.getTransformula(), tfB,
				mManagedScript) != LBool.SAT : "Abstraction is not a superset of concrete relation";

		final IPredicate context = mConditional ? state : null;
		final boolean subset = performInclusionCheck(context, tfA, tfB);
		if (mSymmetric) {
			final boolean superset = performInclusionCheck(context, tfB, tfA);
			return subset && superset;
		} else {
			return subset;
		}
	}

	private final HashRelation<IPredicate, IPredicate> computeAbstraction(final IInternalAction action) {
		if (mAbstractionCache.containsKey(action)) {
			return mAbstractionCache.get(action);
		}

		final HashRelation<IPredicate, IPredicate> abstraction = new HashRelation<>();
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

	private final UnmodifiableTransFormula concretizeAbstraction(HashRelation<IPredicate, IPredicate> abstraction) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		// Construct a substitution to apply to postconditions.
		final Map<TermVariable, Term> substitutionMap = new HashMap<>(mAllVariables.size());
		for (final IProgramVar variable : mAllVariables) {
			final TermVariable original = variable.getTermVariable();
			final TermVariable replacement = mManagedScript.constructFreshCopy(original);
			substitutionMap.put(original, replacement);

			// All variables are output variables (may change arbitrarily, unless
			// constrained below).
			tfb.addOutVar(variable, replacement);
		}
		final Substitution postSubstitution = new Substitution(mManagedScript.getScript(), substitutionMap);

		final List<Term> conjuncts = new ArrayList<>(abstraction.size());

		for (final Map.Entry<IPredicate, IPredicate> pair : abstraction) {
			final IPredicate pre = pair.getKey();
			final IPredicate post = pair.getValue();

			// Add program constants.
			for (final IProgramConst constant : pre.getConstants()) {
				tfb.addProgramConst(constant);
			}
			for (final IProgramConst constant : post.getConstants()) {
				tfb.addProgramConst(constant);
			}

			// Free variables of the precondition are input variables.
			for (final IProgramVar variable : pre.getVars()) {
				tfb.addInVar(variable, variable.getTermVariable());
			}

			final Term postFormula = postSubstitution.transform(post.getFormula());
			final Term conjunct = SmtUtils.implies(mManagedScript.getScript(), pre.getFormula(), postFormula);
			conjuncts.add(conjunct);
		}

		tfb.setFormula(SmtUtils.and(mManagedScript.getScript(), conjuncts));

		return tfb.finishConstruction(mManagedScript);
	}

	// TODO: this method and the next are duplicated in SemanticIndependenceChecker.
	// Avoid that.
	private final boolean performInclusionCheck(final IPredicate context, final UnmodifiableTransFormula a,
			final UnmodifiableTransFormula b) {
		final UnmodifiableTransFormula transFormula1 = compose(a, b);
		UnmodifiableTransFormula transFormula2 = compose(b, a);

		if (context != null) {
			// TODO: This represents conjunction with guard (precondition) as composition
			// with assume. Is this a good way?
			final UnmodifiableTransFormula guard = TransFormulaBuilder.constructTransFormulaFromPredicate(context,
					mManagedScript);
			transFormula2 = compose(guard, transFormula2);
		}

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
}
