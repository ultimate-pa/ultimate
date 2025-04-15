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

import java.util.Collection;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public interface ILibraryModel {
	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	interface IFunctionModelHandler {
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}

	@FunctionalInterface
	interface ITypeModelHandler {
		Result handleTypedefinition(IASTNamedTypeSpecifier node, ILocation loc);
	}

	public record FunctionModel(String functionName, IFunctionModelHandler model) {
		// empty
	}

	public record TypeModel(String typeName, ITypeModelHandler model) {
		// empty
	}

	Collection<FunctionModel> getFunctionModels();

	Collection<String> getUnsupportedFunctions();

	Collection<TypeModel> getTypeModels();
}
