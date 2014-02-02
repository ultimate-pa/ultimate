package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * IResult that is reported if toolchain has thrown a Throwable (Error or 
 * Exception). The Throwable stored in the result has to be the Throwable that
 * was thrown by the toolchain.
 * @author Matthias Heizmann
 */
public class ThrowableResult extends AbstractResult {
	Throwable m_Throwable;

	public ThrowableResult(String plugin, Throwable throwable) {
		super(plugin);
		m_Throwable = throwable;
	}

	@Override
	public String getShortDescription() {
		return m_Throwable.getClass().getSimpleName();
	}

	@Override
	public String getLongDescription() {
		return m_Throwable.toString();
	}
}
