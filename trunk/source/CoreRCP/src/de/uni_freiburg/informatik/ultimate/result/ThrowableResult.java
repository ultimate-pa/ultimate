package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * IResult that is reported if toolchain has thrown a Throwable (Error or 
 * Exception). The Throwable stored in the result has to be the Throwable that
 * was thrown by the toolchain.
 * @author Matthias Heizmann
 * FIXME remove Position, solve unnecessary getLocation()-problem
 */
public class ThrowableResult<P> extends AbstractResult<P> {
	Throwable m_Throwable;

	public ThrowableResult(String plugin, Throwable throwable) {
		super(null, plugin, null);
		m_Throwable = throwable;
	}

	@Override
	public ILocation getLocation() {
		ILocation dummyLocation = new BoogieLocation("",0,0,0,0,false);
		return dummyLocation;
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
