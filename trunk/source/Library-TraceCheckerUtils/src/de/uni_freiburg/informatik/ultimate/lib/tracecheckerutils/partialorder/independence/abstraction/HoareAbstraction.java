/*
 * Copyright (C) 2019-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An abstraction that abstracts a statement by the set of all valid pre-/postcondition pairs in a given set of
 * predicates.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of statements that are abstracted
 */
public class HoareAbstraction<L extends IAction, X> implements IRefinableAbstraction<X, Set<IPredicate>, L> {

	private final IHoareTripleChecker mChecker;
	private final Set<IProgramVar> mAllVariables;

	private final ManagedScript mManagedScript;
	private final ICopyActionFactory<L> mCopyFactory;

	public HoareAbstraction(final ManagedScript mgdScript, final IHoareTripleChecker checker,
			final Set<IProgramVar> allVariables, final ICopyActionFactory<L> copyFactory) {
		mManagedScript = mgdScript;
		mChecker = checker;
		mAllVariables = allVariables;
		mCopyFactory = copyFactory;
	}

	@Override
	public L abstractLetter(final L input, final Set<IPredicate> level) {
		assert input instanceof IInternalAction : "Cannot abstract transitions of type " + input.getClass();
		final var abstractTf = concretizeAbstraction(computePrePostPairs((IInternalAction) input, level));
		return mCopyFactory.copy(input, abstractTf, null);
	}

	private HashRelation<IPredicate, IPredicate> computePrePostPairs(final IInternalAction action,
			final Set<IPredicate> predicates) {
		final HashRelation<IPredicate, IPredicate> abstraction = new HashRelation<>();
		for (final IPredicate pre : predicates) {
			for (final IPredicate post : predicates) {
				final Validity result = mChecker.checkInternal(pre, action, post);
				assert result == Validity.VALID || result == Validity.INVALID : "Could not determine abstraction";
				if (result == Validity.VALID) {
					abstraction.addPair(pre, post);
				}
			}
		}

		return abstraction;
	}

	private UnmodifiableTransFormula concretizeAbstraction(final HashRelation<IPredicate, IPredicate> prePostPairs) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		// Construct a substitution to apply to postconditions.
		final Map<TermVariable, Term> substitutionMap = new HashMap<>(mAllVariables.size());
		for (final IProgramVar variable : mAllVariables) {
			final TermVariable original = variable.getTermVariable();
			final TermVariable replacement = mManagedScript.constructFreshCopy(original);
			substitutionMap.put(original, replacement);

			// All variables are output variables (may change arbitrarily, unless constrained below).
			tfb.addOutVar(variable, replacement);
		}

		final List<Term> conjuncts = new ArrayList<>(prePostPairs.size());
		for (final Map.Entry<IPredicate, IPredicate> pair : prePostPairs) {
			final IPredicate pre = pair.getKey();
			final IPredicate post = pair.getValue();

			// Free variables of the precondition are input variables.
			for (final IProgramVar variable : pre.getVars()) {
				tfb.addInVar(variable, variable.getTermVariable());
			}

			final Term postFormula = Substitution.apply(mManagedScript, substitutionMap, post.getFormula());
			final Term conjunct = SmtUtils.implies(mManagedScript.getScript(), pre.getFormula(), postFormula);
			conjuncts.add(conjunct);
		}

		tfb.setFormula(SmtUtils.and(mManagedScript.getScript(), conjuncts));
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mManagedScript);
	}

	@Override
	public ILattice<Set<IPredicate>> getHierarchy() {
		return new UpsideDownLattice<>(new PowersetLattice<>());
	}

	@Override
	public Set<IPredicate> refine(final Set<IPredicate> current, final IRefinementEngineResult<L, X> refinement) {
		final var newPredicates = refinement.getUsedTracePredicates().stream().flatMap(q -> q.getPredicates().stream())
				.collect(Collectors.toSet());
		return DataStructureUtils.union(current, newPredicates);
	}
}
