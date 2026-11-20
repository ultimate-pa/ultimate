package de.uni_freiburg.informatik.ultimate.eca.parser;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieTypeConstructor;

/** Status values shared by ECA condition checking and Boogie generation. */
public enum EcaStatus {
	PENDING, ACTIVE, DONE, ACTIVE_DONE;

	/** A distinct, nonnumeric Boogie type; not an integer synonym. */
	public static final BoogieType TYPE =
			BoogieType.createConstructedType(new BoogieTypeConstructor("status", true, 0, new int[0]));

	public static boolean isLiteral(final String name) {
		for (final EcaStatus status : values()) {
			if (status.name().equals(name)) {
				return true;
			}
		}
		return false;
	}
}
