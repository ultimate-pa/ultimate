/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtLibUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Abstract superclass for our partial quantifier elimination techniques that we
 * apply to a dualJunction. Objects that implement this class can be kept alive
 * throughout an elimination process.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */

public abstract class DualJunctionQuantifierElimination {
	protected final Script mScript;
	protected final ManagedScript mMgdScript;
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	public DualJunctionQuantifierElimination(final ManagedScript script, final IUltimateServiceProvider services) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(SmtLibUtils.PLUGIN_ID);
		mMgdScript = script;
		mScript = script.getScript();
	}

	public abstract String getName();

	public abstract String getAcronym();

	/**
	 * Try to remove {@link TermVariable}s specified by the input
	 * {@link EliminationTaskSimple}. If nothing can be removed, the method must return
	 * null. If some eliminatee was removed return as soon as the intermediate
	 * result becomes a correspondingJunction
	 * <p>
	 * If the quantifier is an existential (resp. universal) quantifier this method
	 * returns an array of {@link Term}s <code>result</code> such that
	 * <code>∃ eliminatees. ⋀ dualJuncts</code> is equivalent to
	 * <code>∃ eliminatees'. ⋀ result</code> (resp.
	 * <code>∀ eliminatees. ⋁ dualJuncts</code> is equivalent to
	 * <code>∀ eliminatees'. ⋁ result</code>) where eliminatees' refers to the
	 * content of the set after this method was executed.
	 * <p>
	 * Which and how many variables from the set <code>eliminatees</code> can be
	 * removed depends on the quantifier elimination algorithm that implements this
	 * method.
	 * <p>
	 * Every variable that was successfully eliminated is removed from the set.
	 * However, due to formula simplifications some variables might get removed
	 * accidentally. Hence, there might be variables that are not removed from the
	 * eliminatees set but do not occur in the resulting terms.
	 */
	public abstract EliminationResult tryToEliminate(EliminationTask et);

	public static class EliminationResult implements Comparable<EliminationResult> {
		private final EliminationTask mEliminationTask;
		private final Set<TermVariable> mNewEliminatees;
		private final int mNumberOfEliminatees;
		private final long mTreeSize;

		public EliminationResult(final EliminationTask eliminationTask, final Set<TermVariable> newEliminatees) {
			super();
			mEliminationTask = eliminationTask;
			mNewEliminatees = Arrays.stream(eliminationTask.getTerm().getFreeVars()).filter(newEliminatees::contains)
					.collect(Collectors.toSet());
			mNumberOfEliminatees = mEliminationTask.getEliminatees().size() + mNewEliminatees.size();
			mTreeSize = new DAGSize().treesize(mEliminationTask.getTerm());
		}

		public EliminationTask getEliminationTask() {
			return mEliminationTask;
		}

		public Set<TermVariable> getNewEliminatees() {
			return mNewEliminatees;
		}

		public EliminationTask integrateNewEliminatees() {
			return mEliminationTask.integrateNewEliminatees(mNewEliminatees);
		}

		/**
		 * We want to implement some metric that selects better
		 * {@link EliminationResult}s. Rather randomly we take a lexicographic order
		 * that first compares the remaining eliminatees and secondly compares the size
		 * of the formula. (Rationale: eliminations may increase the size of the formula
		 * substantially)
		 */
		@Override
		public int compareTo(final EliminationResult arg0) {
			final int eliminateeBased = Integer.compare(mNumberOfEliminatees, arg0.mNumberOfEliminatees);
			if (eliminateeBased != 0) {
				return eliminateeBased;
			}
			final int sizeBased = Double.compare(mTreeSize, arg0.mTreeSize);
			if (sizeBased != 0) {
				return sizeBased;
			}
			// Some metric, not related to difficulty, just to make sure that different
			// EliminationResult are not considered equivalent.
			return mEliminationTask.getTerm().toString().compareTo(arg0.mEliminationTask.getTerm().toString());
		}
	}

}
