/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Wrapper for {@link ILoggingService} and {@link IProgressMonitorService} that are used in the automata library.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class AutomataLibraryServices {
	private final ILoggingService mLoggingService;
	private final IProgressAwareTimer mProgressAwareTimer;

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public AutomataLibraryServices(final IUltimateServiceProvider services) {
		mLoggingService = services.getLoggingService();
		mProgressAwareTimer = services.getProgressMonitorService();
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @param timeoutInMilliseconds
	 *            timeout in milliseconds
	 */
	public AutomataLibraryServices(final IUltimateServiceProvider services, final long timeoutInMilliseconds) {
		mLoggingService = services.getLoggingService();
		mProgressAwareTimer = services.getProgressMonitorService().getChildTimer(timeoutInMilliseconds);
	}

	/**
	 * @param services
	 *            Other automata library services instance.
	 * @param timeoutInMilliseconds
	 *            timeout in milliseconds
	 */
	public AutomataLibraryServices(final AutomataLibraryServices services, final long timeoutInMilliseconds) {
		mLoggingService = services.mLoggingService;
		mProgressAwareTimer = services.mProgressAwareTimer.getChildTimer(timeoutInMilliseconds);
	}

	public ILoggingService getLoggingService() {
		return mLoggingService;
	}

	public IProgressAwareTimer getProgressAwareTimer() {
		return mProgressAwareTimer;
	}
}
