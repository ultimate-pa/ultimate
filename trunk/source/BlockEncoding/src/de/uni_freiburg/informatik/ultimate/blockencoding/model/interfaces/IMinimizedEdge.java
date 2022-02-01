/*
 * Copyright (C) 2012-2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * This interface represents all kinds of minimized edges.
 * 
 * @author Stefan Wissert
 * 
 */
public interface IMinimizedEdge extends
		IModifiableMultigraphEdge<MinimizedNode, IMinimizedEdge,MinimizedNode, IMinimizedEdge,VisualizationNode> {

	/**
	 * Is this a basic edge or a composite edge?
	 * 
	 * @return <b>true</b> if it is a basic edge, <br>
	 *         <b>false</b> if it is a composite edge
	 */
	public boolean isBasicEdge();

	/**
	 * Since there is an unsolved problem to minimize Call- and Return-Edges
	 * with SequentialComposition which the "old(...)"-Expression is contained,
	 * we check edges if this expression is involved. If this is the case we do
	 * not allow the minimization of Call-Edges in this case.
	 * 
	 * @return <b>true</b> if old is used, <br>
	 *         <b>false</b> if old is not used
	 */
	public boolean isOldVarInvolved();

	/**
	 * Every edge in the minimized model is rated with some metrics
	 * (complexity). So that we are now able to control which edges we want, and
	 * which we do not want. This is maybe needed because Large Block Encoding
	 * does to much minimization.
	 * 
	 * @return the computed Rating of this edge.
	 */
	public IRating getRating();

	/**
	 * Every edge can return a set of the variables, which are used here.
	 * Basically this information is used to set up a rating and a corresponding
	 * Heuristic. We use a set here, since BoogieVars are unique and we count
	 * every variable only once.
	 * 
	 * @return the set of used boogie vars
	 */
	public Set<IProgramVar> getDifferentVariables();

	/**
	 * Returns the number of IMinimizedEdges inside, so basic edges return here
	 * 1 and composite edges the number of edges inside.
	 * 
	 * @return the number of minimized edges contained
	 */
	public int getElementCount();

}
