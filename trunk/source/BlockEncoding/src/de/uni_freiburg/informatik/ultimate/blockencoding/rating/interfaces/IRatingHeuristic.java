/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;

/**
 * Basically classes which implement this interface define a certain boundary
 * for which we take another rated edge level. The main target is, that this
 * boundary is automatically defined (computed) so that no user input should be
 * given. Another way is that the use can specify a certain boundary.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IRatingHeuristic {

	/**
	 * This method determines, if the certain boundary, defined by this
	 * heuristic, is reached.
	 * 
	 * @param rating
	 *            the Rating to check
	 * @return <b>true</b>, when we are less than or equal to the boundary value <br>
	 *         <b>false</b>, if the boundary is not reached <br>
	 */
	public boolean isRatingBoundReached(IRating rating, List<IMinimizedEdge> edgeLevel);

	/**
	 * The heuristic can be initialized with a preference value which can be
	 * determined in the global preferences of the plugin.
	 * 
	 * @param givenPref
	 *            the preference value as String
	 */
	public void init(String givenPref);
	
	
	/**
	 * Determines if there is a heuristic support for the chosen rating strategy.
	 * 
	 * @param strategy the chosen strategy
	 * @return <b>true</b>, if the strategy is supported <br>
	 *         <b>false</b>, otherwise <br>
	 */
	public boolean isRatingStrategySupported(RatingStrategy strategy);

}
