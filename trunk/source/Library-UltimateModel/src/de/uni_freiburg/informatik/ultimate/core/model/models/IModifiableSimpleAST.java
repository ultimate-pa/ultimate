/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.models;

/***
 * This interface represents a modifiable variant of {@link ISimpleAST}.
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare <tt>public final class FinalModel implements IModifiableSimpleAST&lt;FinalModel&gt;</tt> .
 * @see ISimpleAST
 * @see IModifiableOutgoing
 * 
 */
public interface IModifiableSimpleAST<T extends IModifiableSimpleAST<T, E>, E extends IVisualizable<E>>
		extends ISimpleAST<T, E>, IModifiableOutgoing<T> {

}
