package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public abstract class CACSLLocation implements Serializable, ILocation {

	private static final long serialVersionUID = -5505219183722347819L;

	/**
	 * The m_CheckedSpecification of check/assertion applied to this node.
	 */
	private final Check mCheckedSpecification;

	private final boolean mIgnoreDuringBacktranslation;

	protected CACSLLocation(Check checkedSpec, boolean ignoreDuringBacktranslation) {
		mCheckedSpecification = checkedSpec;
		mIgnoreDuringBacktranslation = ignoreDuringBacktranslation;
	}

	@Override
	public ILocation getOrigin() {
		return this;
	}

	@Override
	public Check getCheck() {
		return mCheckedSpecification;
	}

	public boolean ignoreDuringBacktranslation() {
		return mIgnoreDuringBacktranslation;
	}

}
