/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;

/**
 * Exception that is thrown by automata operations if they detected that the caller requested a cancellation of the
 * operation (e.g., because a timeout was reached).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class AutomataOperationCanceledException extends AutomataLibraryException implements IRunningTaskStackProvider {

	private static final long serialVersionUID = -1713238821191695165L;

	private static final String MESSAGE_CANCELED = "Timeout or canceled by user.";

	private final List<RunningTaskInfo> mRunningTaskInfos = new ArrayList<>();

	public AutomataOperationCanceledException(final Class<?> thrower) {
		super(thrower, MESSAGE_CANCELED);
		mRunningTaskInfos.add(new RunningTaskInfo(thrower, null));
	}

	public AutomataOperationCanceledException(final RunningTaskInfo runningTaskInfo) {
		super(runningTaskInfo.getClassOfTaskExecutor(), MESSAGE_CANCELED);
		mRunningTaskInfos.add(runningTaskInfo);
	}

	public void addRunningTaskInfo(final RunningTaskInfo runningTaskInfo) {
		mRunningTaskInfos.add(runningTaskInfo);
	}

	@Override
	public List<RunningTaskInfo> getRunningTaskStack() {
		return mRunningTaskInfos;
	}
}
