/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Abstract operation with the most common fields and default methods.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CRSF>
 *            checkResult state factory type
 */
public abstract class GeneralOperation<LETTER, STATE, CRSF extends IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, CRSF> {
	/**
	 * Ultimate services.
	 */
	protected final AutomataLibraryServices mServices;

	/**
	 * Logger.
	 */
	protected final ILogger mLogger;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public GeneralOperation(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
	}

	/**
	 * Should be called regularly by subclasses to check for timeouts. A subclass which does not do this is a bad
	 * subclass! A good practice is to call this method after each sub-call to other {@link IOperation}s and inside
	 * (expensive) loops.
	 * <p>
	 * If a timeout was requested, the subclass should immediately throw an {@link AutomataOperationCanceledException}.
	 * 
	 * @return true iff {@link AutomataLibraryServices} object requests cancellation
	 */
	protected final boolean isCancellationRequested() {
		return !mServices.getProgressAwareTimer().continueProcessing();
	}

	protected final void printStartMessage() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
	}

	protected final void printExitMessage() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	protected final void printStartCheckMessage() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}
	}

	protected final void printExitCheckMessage() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isWarnEnabled()) {
			mLogger.warn("No result check for " + getOperationName() + " available yet.");
		}
		return true;
	}

	/**
	 * @return generic running task description.
	 */
	protected String generateGenericRunningTaskDescription() {
		return "applying " + getOperationName();
	}

	/**
	 * @param aoce
	 *            {@link AutomataOperationCanceledException}.
	 */
	protected final void addGenericRunningTaskInfo(final AutomataOperationCanceledException aoce) {
		addRunningTaskInfo(aoce, generateGenericRunningTaskDescription());
	}

	/**
	 * @param aoce
	 *            {@link AutomataOperationCanceledException}.
	 * @param description
	 *            description
	 */
	protected final void addRunningTaskInfo(final AutomataOperationCanceledException aoce, final String description) {
		aoce.addRunningTaskInfo(new RunningTaskInfo(getClass(), description));
	}
}
