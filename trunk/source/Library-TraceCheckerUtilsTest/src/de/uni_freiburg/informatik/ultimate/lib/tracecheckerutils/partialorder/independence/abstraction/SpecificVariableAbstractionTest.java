/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitSubSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class SpecificVariableAbstractionTest
		extends AbstractAbstractionTestSuite<VarAbsConstraints<BasicInternalAction>> {

	private BitSubSet.Factory<IProgramVar> mFactory;

	@Override
	protected IAbstraction<VarAbsConstraints<BasicInternalAction>, BasicInternalAction> createAbstraction() {
		final Set<IProgramVar> allVariables = new HashSet<>(mSymbolTable.getGlobals());
		mFactory = new BitSubSet.Factory<>(allVariables);
		return new SpecificVariableAbstraction<>(this::copyAction, mMgdScript, null, null, Collections.emptySet(),
				mFactory);
	}

	@Test
	public void rightSideAbstracted() {
		// abstract variable on right side, but not left side
		testAbstraction(yIsXTimesTwo(), Set.of(y), Collections.emptySet());
	}

	@Test
	public void leftSideAbstraction() {
		testAbstraction(yIsXTimesTwo(), Set.of(x), Set.of(x));
	}

	@Test
	public void bothSidesDifferentVariablesEmptyConstrVars() {
		testAbstraction(yIsXTimesTwo(), Collections.emptySet(), Collections.emptySet());
	}

	@Test
	public void withAuxVar() {
		testAbstraction(jointHavocXandY(), Set.of(x), Set.of(x));
	}

	@Test
	public void doNothingFullConstrVars() {
		testAbstractionDoesNothing(yIsXTimesTwo(), Set.of(x, y), Set.of(x, y));
		testAbstractionDoesNothing(xIsXPlusOne(), Set.of(x, y), Set.of(x, y));
	}

	@Test
	public void bothSidesSameVariable() {
		testAbstraction(xIsXPlusOne(), Collections.emptySet(), Collections.emptySet());
	}

	private void testAbstraction(final UnmodifiableTransFormula utf, final Set<IProgramVar> inConstr,
			final Set<IProgramVar> outConstr) {
		final BasicInternalAction action = createAction(utf);
		testAbstraction(action, makeSimpleVarAbsConstraint(action, inConstr, outConstr));
	}

	private void testAbstractionDoesNothing(final UnmodifiableTransFormula utf, final Set<IProgramVar> inConstr,
			final Set<IProgramVar> outConstr) {
		final BasicInternalAction action = createAction(utf);
		testAbstractionDoesNothing(action, makeSimpleVarAbsConstraint(action, inConstr, outConstr));
	}

	private VarAbsConstraints<BasicInternalAction> makeSimpleVarAbsConstraint(final BasicInternalAction letter,
			final Set<IProgramVar> in, final Set<IProgramVar> out) {
		final Map<BasicInternalAction, BitSubSet<IProgramVar>> inConstr = new HashMap<>();
		final Map<BasicInternalAction, BitSubSet<IProgramVar>> outConstr = new HashMap<>();
		if (!in.isEmpty()) {
			inConstr.put(letter, mFactory.valueOf(in));
		}
		if (!out.isEmpty()) {
			outConstr.put(letter, mFactory.valueOf(out));
		}
		return new VarAbsConstraints<>(inConstr, outConstr, mFactory.empty());
	}

	@Override
	protected VarAbsConstraints<BasicInternalAction>
			computeLevel(final Triple<IPredicate, BasicInternalAction, IPredicate>... triples) {
		// We need to override this method because the lattice of mAbstraction does not know all letters, and thus
		// throws exceptions.
		// TODO This needs to be fixed, so we can test #refine, #restrict etc.
		// Then this implementation will also be obsolete.

		final Map<BasicInternalAction, BitSubSet<IProgramVar>> inConstr = new HashMap<>();
		final Map<BasicInternalAction, BitSubSet<IProgramVar>> outConstr = new HashMap<>();

		for (final var triple : triples) {
			final var oldInValue = inConstr.get(triple.getSecond());
			final var newInVariables = mFactory.valueOf(triple.getFirst().getVars());
			inConstr.put(triple.getSecond(),
					oldInValue == null ? newInVariables : mFactory.union(oldInValue, newInVariables));

			final var oldOutValue = outConstr.get(triple.getSecond());
			final var newOutVariables = mFactory.valueOf(triple.getThird().getVars());
			outConstr.put(triple.getSecond(),
					oldOutValue == null ? newOutVariables : mFactory.union(oldOutValue, newOutVariables));
		}
		return new VarAbsConstraints<>(inConstr, outConstr, mFactory.empty());
	}
}
