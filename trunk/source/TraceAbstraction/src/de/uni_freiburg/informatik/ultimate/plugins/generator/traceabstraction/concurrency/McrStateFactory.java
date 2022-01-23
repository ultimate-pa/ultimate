/*
 * Copyright (C) 2021-2022 Dennis Wölfing
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A factory for MCR automaton states.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters in the automaton.
 */
public class McrStateFactory<L extends IIcfgTransition<?>> implements IEmptyStackStateFactory<IPredicate> {
	private final IPredicate mEmptyStack;

	/**
	 * Creates the factory.
	 *
	 * @param factory
	 *            A PredicateFactory.
	 */
	public McrStateFactory(final PredicateFactory factory) {
		mEmptyStack = factory.newEmptyStackPredicate();
	}

	/**
	 * Creates a predicate for the automaton from an McrState.
	 *
	 * @param original
	 *            The original state from the input automaton.
	 * @param state
	 *            The McrState.
	 * @return A new predicate.
	 */
	public IPredicate createState(final IPredicate original, final McrState<L, IPredicate> state) {
		if (!(original instanceof IMLPredicate)) {
			throw new IllegalArgumentException("Unexpected type of predicate: " + original.getClass());
		}
		return new McrPredicate((IMLPredicate) original, state);
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmptyStack;
	}

	/**
	 * A predicate for MCR.
	 *
	 * @author Dennis Wölfing
	 *
	 */
	public final class McrPredicate implements IMLPredicate {
		private final IMLPredicate mUnderlying;
		private final McrState<L, IPredicate> mState;

		/**
		 * Creates the predicate.
		 *
		 * @param underlying
		 *            The underlying state from the input automaton.
		 * @param state
		 *            The McrState to encode.
		 */
		public McrPredicate(final IMLPredicate underlying, final McrState<L, IPredicate> state) {
			mUnderlying = underlying;
			mState = state;
		}

		@Override
		public Term getFormula() {
			return mUnderlying.getFormula();
		}

		@Override
		public Term getClosedFormula() {
			return mUnderlying.getClosedFormula();
		}

		@Override
		public String[] getProcedures() {
			return mUnderlying.getProcedures();
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mUnderlying.getVars();
		}

		@Override
		public IcfgLocation[] getProgramPoints() {
			return mUnderlying.getProgramPoints();
		}

		@Override
		public Set<IProgramConst> getConstants() {
			return mUnderlying.getConstants();
		}

		@Override
		public Set<IProgramFunction> getFunctions() {
			return mUnderlying.getFunctions();
		}

		@Override
		public int hashCode() {
			return Objects.hash(mUnderlying, mState);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final McrPredicate other = (McrPredicate) obj;
			return Objects.equals(mState, other.mState) && Objects.equals(mUnderlying, other.mUnderlying);
		}

		public IPredicate getUnderlying() {
			return mUnderlying;
		}

		@Override
		public String toString() {
			return "McrPredicate [" + mState + "]";
		}
	}
}
