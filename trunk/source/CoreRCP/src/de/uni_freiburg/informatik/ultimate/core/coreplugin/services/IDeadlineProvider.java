package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
interface IDeadlineProvider extends IProgressAwareTimer {

	long getDeadline();
}
