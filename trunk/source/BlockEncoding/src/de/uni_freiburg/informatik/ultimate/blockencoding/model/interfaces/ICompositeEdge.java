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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces;

/**
 * This interface represents an edge which is composed out of two edges of the
 * type "IMinimizedEdge".
 * 
 * @see IMinimizedEdge
 * 
 * @author Stefan Wissert
 * 
 */
public interface ICompositeEdge extends IMinimizedEdge {

	/**
	 * This method returns the two edges (of type "IMinimizedEdge") of the
	 * composition.
	 * 
	 * @return an array with two composite edges.
	 */
	public IMinimizedEdge[] getCompositeEdges();

	/**
	 * A composite edge is able to check if a other edge, contains already parts
	 * of itself. We need this method to prevent duplication.
	 * 
	 * @param edgeToCheck
	 *            other edge to check
	 * @return true: if there is duplication <br>
	 *         false: if there is no duplication
	 */
	public boolean duplicationOfFormula(IMinimizedEdge edgeToCheck);

}
