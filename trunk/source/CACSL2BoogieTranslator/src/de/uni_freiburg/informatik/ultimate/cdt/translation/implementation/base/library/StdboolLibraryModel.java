/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Model of stdbool.h (C11 7.18, https://en.cppreference.com/w/c/header/stdbool) that defines the type {@code bool} and
 * the constants {@code true} and {@code false}.
 */
public class StdboolLibraryModel implements ILibraryModel {
	private static final CPrimitive BOOL_TYPE = new CPrimitive(CPrimitives.BOOL);

	private final FunctionModelHelper mHelper;

	public StdboolLibraryModel(final FunctionModelHelper helper) {
		mHelper = helper;
	}

	@Override
	public Collection<TypeModel> getTypeModels() {
		return List.of(new TypeModel("bool", BOOL_TYPE));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		return List.of(
				new ConstantModel("false", loc -> mHelper.constructIntegerLiteral(loc, BigInteger.ZERO, BOOL_TYPE)),
				new ConstantModel("true", loc -> mHelper.constructIntegerLiteral(loc, BigInteger.ONE, BOOL_TYPE)));
	}
}
