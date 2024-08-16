/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs;

import java.util.Collection;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * A specification stating that any execution starting in an initial location and with a variable assignment satisfying
 * a given precondition must, when (and if) it reaches a final location, have a current variable assignment satisfying a
 * given postcondition.
 *
 * There may be multiple initial locations, and the precondition that holds initially may differ depending on the
 * initial condition. This is for example needed in interprocedural programs, where (in "library mode") each procedure's
 * entry node is an initial location, and the corresponding precondition states that g = old(g) for all modifiable
 * global variables of the procedure.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            the type of states (or "locations")
 */
public class PrePostConditionSpecification<S> implements ISpecification {
	private final Map<S, IPredicate> mInitialStates;
	private final Predicate<S> mIsFinalState;
	private final IPredicate mPostcondition;

	/**
	 * Creates a new specification.
	 *
	 * @param initialStates
	 *            a map from initial states to the preconditions which may be assumed at each state
	 * @param isFinalState
	 *            a predicate identifying final states
	 * @param postcondition
	 *            a postcondition that must hold at every final state
	 */
	public PrePostConditionSpecification(final Map<S, IPredicate> initialStates, final Predicate<S> isFinalState,
			final IPredicate postcondition) {
		mInitialStates = initialStates;
		mIsFinalState = isFinalState;
		mPostcondition = Objects.requireNonNull(postcondition);
	}

	public static <LOC extends IcfgLocation> PrePostConditionSpecification<LOC> forIcfg(final IIcfg<LOC> icfg,
			final IPredicateUnifier unifier) {
		final var modGlobTable = icfg.getCfgSmtToolkit().getModifiableGlobalsTable();
		final var script = icfg.getCfgSmtToolkit().getManagedScript().getScript();
		final var initials = icfg.getInitialNodes().stream()
				.collect(Collectors.toMap(Function.identity(),
						l -> PredicateUtils.computeInitialPredicateForProcedure(modGlobTable, script, l.getProcedure(),
								unifier.getPredicateFactory())));
		return forIcfg(icfg, initials, unifier.getFalsePredicate());
	}

	public static <LOC extends IcfgLocation> PrePostConditionSpecification<LOC> forIcfg(final IIcfg<LOC> icfg,
			final Map<LOC, IPredicate> initialStates, final IPredicate postcondition) {
		return new PrePostConditionSpecification<>(initialStates, l -> IcfgUtils.isErrorLocation(icfg, l),
				postcondition);
	}

	public Collection<S> getInitialStates() {
		return mInitialStates.keySet();
	}

	public boolean isFinalState(final S state) {
		return mIsFinalState.test(state);
	}

	public IPredicate getPrecondition(final S initialState) {
		return mInitialStates.get(initialState);
	}

	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	public boolean isUnreachabilitySpecification() {
		return SmtUtils.isFalseLiteral(mPostcondition.getFormula());
	}
}
