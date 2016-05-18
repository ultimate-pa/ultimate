/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.results;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * {@link IResultWithInfiniteLassoTrace} describes results that contain a
 * infinite trace that consists of a finite prefix called the stem, and an
 * infinite but periodic suffix called the lasso.
 * 
 * One can imagine both, the stem and the lasso, as a finite sequence of
 * statements, where the sequence of statements of the lasso repeat themselves
 * infinitely often in the order described by said sequence.
 * 
 * Both, the stem and the lasso, are represented by a {@link IProgramExecution},
 * which consists of a sequence of trace elements of type TE, and which may
 * contain program states, which are described by expressions of type E.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */
public interface IResultWithInfiniteLassoTrace<TE, E> extends IResult {

	public IProgramExecution<TE, E> getStem();

	public IProgramExecution<TE, E> getLasso();
}
