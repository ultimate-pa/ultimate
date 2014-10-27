package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class LocalLValueILocationPair {

	LocalLValue llv;
	ILocation loc;

	public LocalLValueILocationPair(LocalLValue llv, ILocation loc) {
		super();
		this.llv = llv;
		this.loc = loc;
	}
}
