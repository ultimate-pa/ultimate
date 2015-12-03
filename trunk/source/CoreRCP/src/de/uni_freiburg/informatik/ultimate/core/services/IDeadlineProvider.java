package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
interface IDeadlineProvider extends IProgressAwareTimer {

	long getDeadline();
}
