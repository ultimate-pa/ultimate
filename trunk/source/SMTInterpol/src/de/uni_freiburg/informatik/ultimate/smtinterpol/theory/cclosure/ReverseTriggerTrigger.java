/*
 * Copyright (C) 2009-2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;

/**
 * Trigger that holds two lists: reverse triggers and function applications (on the argument). When merged, both lists
 * are joined and every ReverseTrigger in one list is activated on every function application in the other list (and
 * vice versa).
 *
 * @author Jochen Hoenicke
 */
public final class ReverseTriggerTrigger extends SignatureTrigger {

	private final SimpleList<ReverseTrigger> mTriggers = new SimpleList<>();
	private final SimpleList<AppTermEntry> mApplications = new SimpleList<>();


	public ReverseTriggerTrigger(MasterReverseTrigger masterTrigger, ReverseTrigger trigger) {
		super(masterTrigger, new CCTerm[] { trigger.getArgument() });
		mTriggers.append(trigger);
	}

	public ReverseTriggerTrigger(MasterReverseTrigger masterTrigger, CCAppTerm app, int argPosition) {
		super(masterTrigger, new CCTerm[] { app.getArgument(argPosition) });
		mApplications.append(new AppTermEntry(app));
	}

	public SimpleList<AppTermEntry> getApplications() {
		return mApplications;
	}

	@Override
	public void merge(final CClosure engine, final SignatureTrigger other) {
		super.merge(engine, other);
		assert other instanceof ReverseTriggerTrigger;
		final ReverseTriggerTrigger otherRev = (ReverseTriggerTrigger) other;

		// Cross-activate: every trigger in this list on every app in other's list
		for (final ReverseTrigger trigger : mTriggers) {
			for (final AppTermEntry app : otherRev.mApplications) {
				trigger.activate(app.getAppTerm(), false);
			}
		}
		// Every trigger in other's list on every app in this list
		for (final ReverseTrigger trigger : otherRev.mTriggers) {
			for (final AppTermEntry app : mApplications) {
				trigger.activate(app.getAppTerm(), false);
			}
		}

		// Join both lists
		mTriggers.joinList(otherRev.mTriggers);
		mApplications.joinList(otherRev.mApplications);
	}

	@Override
	public void undoMerge(final CClosure engine, final SignatureTrigger other) {
		super.undoMerge(engine, other);
		assert other instanceof ReverseTriggerTrigger;
		final ReverseTriggerTrigger otherRev = (ReverseTriggerTrigger) other;

		// unjoin both lists
		mTriggers.unjoinList(otherRev.mTriggers);
		mApplications.unjoinList(otherRev.mApplications);
	}


	static final class AppTermEntry extends SimpleListable<AppTermEntry> {
		private CCAppTerm mAppTerm;

		public AppTermEntry(CCAppTerm appTerm) {
			mAppTerm = appTerm;
		}

		CCAppTerm getAppTerm() {
			return mAppTerm;
		}

		@Override
		public String toString() {
			return mAppTerm.toString();
		}
	}
}
