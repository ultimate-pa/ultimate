/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.typechecker.ITypeErrorReporter;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckException;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Was created in order to be able to factor out {@link TypeCheckHelper} from {@link TypeChecker}.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class TypeErrorReporter implements ITypeErrorReporter<ILocation> {

	ILocation mLocation;

	public TypeErrorReporter(final ILocation location) {
		mLocation = location;
	}

	@Override
	public void report(final Function<ILocation, String> func) {
		throw new TypeCheckException(func.apply(mLocation));
	}
}