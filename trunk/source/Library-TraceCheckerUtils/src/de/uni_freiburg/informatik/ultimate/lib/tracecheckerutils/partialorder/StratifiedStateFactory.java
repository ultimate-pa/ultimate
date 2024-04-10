/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction.AbstractionLevel;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction.IStratifiedStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class StratifiedStateFactory<L, H> implements IStratifiedStateFactory<L, IPredicate, IPredicate, H> {
	@Override
	public IPredicate createEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicate createStratifiedState(final IPredicate state, final AbstractionLevel<H> level,
			final AbstractionLevel<H> limit) {
		return new StratifiedMLPredicate<>((IMLPredicate) state, level, limit);
	}

	@Override
	public IPredicate getOriginalState(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).getUnderlying();
	}

	@Override
	public Map<L, H> getSleepSet(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).getSleepMap();
	}

	@Override
	public void setSleepSet(final IPredicate state, final Map<L, H> sleepset) {
		((StratifiedMLPredicate<L, H>) state).setSleepMap(sleepset);
	}

	@Override
	public AbstractionLevel<H> getAbstractionLevel(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).getLevel();
	}

	@Override
	public AbstractionLevel<H> getAbstractionLimit(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).getLimit();
	}

	private static final class StratifiedMLPredicate<L, H> extends AnnotatedMLPredicate<Annotation<L, H>> {
		protected StratifiedMLPredicate(final IMLPredicate underlying, final AbstractionLevel<H> level,
				final AbstractionLevel<H> limit) {
			super(underlying, new Annotation<>(level, limit));
		}

		public AbstractionLevel<H> getLevel() {
			return mAnnotation.getLevel();
		}

		public AbstractionLevel<H> getLimit() {
			return mAnnotation.getLimit();
		}

		public Map<L, H> getSleepMap() {
			return mAnnotation.getSleepMap();
		}

		public void setSleepMap(final Map<L, H> sleepset) {
			mAnnotation.setSleepMap(sleepset);
		}

		public H getGuess() {
			return mAnnotation.getGuess();
		}

		public boolean isLoopNode() {
			return mAnnotation.isLoopNode();
		}

		public void setLoopNode() {
			mAnnotation.setLoopNode();
		}

		public void setGuessedLevel(final H guess) {
			mAnnotation.guess(guess);
		}
	}

	private static final class Annotation<L, H> {
		private final AbstractionLevel<H> mLevel;
		private final AbstractionLevel<H> mLimit;
		private H mGuessedLevel;
		private boolean mLoopEntryNode;

		private Map<L, H> mSleepMap;

		public Annotation(final AbstractionLevel<H> level, final AbstractionLevel<H> limit) {
			mLevel = level;
			mLimit = limit;
		}

		public void guess(final H lvl) {
			mGuessedLevel = lvl;
		}

		public void setLoopNode() {
			mLoopEntryNode = true;
		}

		public void setSleepMap(final Map<L, H> sleepMap) {
			if (mSleepMap != null) {
				throw new UnsupportedOperationException("Sleep map can only be set once");
			}
			if (sleepMap == null) {
				throw new IllegalArgumentException("Sleep map must not be null");
			}
			mSleepMap = sleepMap;
		}

		public AbstractionLevel<H> getLevel() {
			return mLevel;
		}

		public AbstractionLevel<H> getLimit() {
			return mLimit;
		}

		public Map<L, H> getSleepMap() {
			if (mSleepMap == null) {
				throw new UnsupportedOperationException("Sleep map has not yet been set");
			}
			return mSleepMap;
		}

		public boolean isLoopNode() {
			return mLoopEntryNode;
		}

		public H getGuess() {
			return mGuessedLevel;
		}
	}

	// stuff for loophandling
	@Override
	public H guessedLevel(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).getGuess();
	}

	@Override
	public boolean isLoopNode(final IPredicate state) {
		return ((StratifiedMLPredicate<L, H>) state).isLoopNode();
	}

	@Override
	public void setAsLoopNode(final IPredicate state) {
		((StratifiedMLPredicate<L, H>) state).setLoopNode();
	}

	@Override
	public void setGuessedLevel(final IPredicate state, final H guess) {
		((StratifiedMLPredicate<L, H>) state).setGuessedLevel(guess);
	}
}
