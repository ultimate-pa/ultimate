package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * Interface that describes a factory which creates locations for an {@link IIcfg} based on an old location.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 *            The type of the old locations.
 * @param <OUTLOC>
 *            The type of locations that should be produced.
 */
@FunctionalInterface
public interface ILocationFactory<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {
	/**
	 * Create a new location based on an old location, a procedure, and a debug identifier.
	 *
	 * @param oldLocation
	 *            the old location
	 * @param debugIdentifier
	 *            The debug identifier of the new location.
	 * @param procedure
	 *            A string specifiying to which procedure the new location should belong.
	 * @return The new location.
	 */
	OUTLOC createLocation(final INLOC oldLocation, final DebugIdentifier debugIdentifier, final String procedure);
}